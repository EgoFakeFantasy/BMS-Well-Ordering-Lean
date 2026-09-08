import Lean.Elab.Tactic.Meta
import Lean.Parser.Module
import Lean.Util.CollectAxioms
import Lean.Util.Heartbeats
import YesMetaZFC.Automation.HostAvatar.Dispatch
/-!
# `prove_auto` 批量目标扫描器

静态依赖只保留公共 tactic 入口；待扫描的完整证明库在运行时从 `.olean` 加载，
避免启动时对元数学模块的大型闭式编码定义执行原生初始化。
本工具只作为独立 `lake exe` 构建，不进入证明库的默认导入图。它从 `.olean`
读取模块 import DAG 与声明原始顺序，在严格心跳预算下重建定理的 Π-上下文并运行
`prove_auto`。成功证明必须在元状态回滚前完成依赖审计，避免目标自身、同模块后置
声明或无关模块造成虚假闭合。
-/

namespace YesMetaZFC
namespace Automation
namespace Tools
namespace ProveAutoSweep

open Lean Meta

structure Config where
  modulePrefix : String := "YesMetaZFC.SetTheory"
  namePrefix : String := ""
  limit : Nat := 100
  maxHeartbeats : Nat := 50000
  maxFacts : Nat := 12
  maxRules : Nat := 8
  output : String := "tmp/prove_auto_sweep.jsonl"
  markdown : String := "tmp/prove_auto_sweep.md"
  includeExisting : Bool := false
  strictAudit : Bool := false
  sourceValidate : Bool := true
  subgoalFallback : Bool := true
  subgoalBatchSize : Nat := 3
  subgoalTimeoutMs : Nat := 50000
  showHelp : Bool := false

structure Candidate where
  name : Name
  moduleName : Name
  moduleIndex : Nat
  declarationPosition : Position
  declarationEndPosition : Position
  position : Position
  line : Nat
  type : Expr
  deriving Inhabited

structure CandidateSet where
  values : Array Candidate := #[]
  theoremCount : Nat := 0
  skippedExisting : Nat := 0

structure ProofAudit where
  backend : String := "unknown"
  proofConstants : Nat := 0
  forbiddenDependencies : Array Name := #[]
  supportModules : Array Name := #[]
  generatedAuxiliaries : Array Name := #[]
  nativeTickets : Array Name := #[]
  newAxioms : Array Name := #[]

structure SubgoalHit where
  id : String
  startLine : Nat
  startColumn : Nat
  endLine : Nat
  endColumn : Nat
  source : String
  deriving Inhabited

structure Result where
  declaration : Name
  moduleName : Name
  line : Nat
  type : String
  status : String
  prefilterStatus : String := ""
  backend : String := "unknown"
  elapsedNs : Nat := 0
  heartbeats : Nat := 0
  sourceElapsedNs : Nat := 0
  sourceRequiresImport : Bool := false
  subgoalElapsedNs : Nat := 0
  subgoals : Array SubgoalHit := #[]
  subgoalProbeMessage : String := ""
  proofConstants : Nat := 0
  forbiddenDependencies : Array Name := #[]
  supportModules : Array Name := #[]
  generatedAuxiliaries : Array Name := #[]
  nativeTickets : Array Name := #[]
  newAxioms : Array Name := #[]
  message : String := ""
  deriving Inhabited

private def usage : String :=
  String.intercalate "\n" [
    "prove_auto_sweep options:",
    "  --module-prefix <prefix>   只扫描指定模块前缀（默认 YesMetaZFC.SetTheory）",
    "  --name-prefix <prefix>     只扫描指定声明名前缀",
    "  --limit <n>                最多扫描 n 个目标，0 表示不限制（默认 100）",
    "  --max-heartbeats <n>       每个目标的 Lean 心跳上限（默认 50000）",
    "  --max-facts <n>            prove_auto 自动事实数（默认 12）",
    "  --max-rules <n>            HR 规则上限（默认 8）",
    "  --output <path>            JSONL 输出路径",
    "  --markdown <path>          Markdown 输出路径",
    "  --include-existing         包含已经由 prove_auto 生成的定理",
    "  --audit                    使用纯 Lean replay，禁用 native ticket",
    "  --no-source-validate       仅运行整库预筛，不做声明现场源码编译复核",
    "  --no-subgoals              禁用原证明第一层子目标回退探测",
    "  --subgoal-batch-size <n>    每次临时编译最多探测的分支数（默认 3，0 表示不分批）",
    "  --subgoal-timeout-ms <n>    子目标临时编译墙钟上限（默认 50000，0 表示禁用）",
    "  --help                     显示本说明"
  ]

private def parseNat (flag value : String) : Except String Nat :=
  match value.toNat? with
  | some value => .ok value
  | none => .error s!"{flag} 需要自然数参数，得到 `{value}`"

private partial def parseArgs (args : List String)
    (config : Config := {}) : Except String Config := do
  match args with
  | [] =>
      return config
  | "--module-prefix" :: value :: rest =>
      parseArgs rest { config with modulePrefix := value }
  | "--name-prefix" :: value :: rest =>
      parseArgs rest { config with namePrefix := value }
  | "--limit" :: value :: rest =>
      parseArgs rest { config with limit := ← parseNat "--limit" value }
  | "--max-heartbeats" :: value :: rest =>
      parseArgs rest {
        config with
        maxHeartbeats := ← parseNat "--max-heartbeats" value
      }
  | "--max-facts" :: value :: rest =>
      parseArgs rest {
        config with
        maxFacts := ← parseNat "--max-facts" value
      }
  | "--max-rules" :: value :: rest =>
      parseArgs rest {
        config with
        maxRules := ← parseNat "--max-rules" value
      }
  | "--output" :: value :: rest =>
      parseArgs rest { config with output := value }
  | "--markdown" :: value :: rest =>
      parseArgs rest { config with markdown := value }
  | "--include-existing" :: rest =>
      parseArgs rest { config with includeExisting := true }
  | "--audit" :: rest =>
      parseArgs rest { config with strictAudit := true }
  | "--no-source-validate" :: rest =>
      parseArgs rest { config with sourceValidate := false }
  | "--no-subgoals" :: rest =>
      parseArgs rest { config with subgoalFallback := false }
  | "--subgoal-batch-size" :: value :: rest =>
      parseArgs rest {
        config with
        subgoalBatchSize :=
          ← parseNat "--subgoal-batch-size" value
      }
  | "--subgoal-timeout-ms" :: value :: rest =>
      parseArgs rest {
        config with
        subgoalTimeoutMs :=
          ← parseNat "--subgoal-timeout-ms" value
      }
  | "--help" :: rest =>
      parseArgs rest { config with showHelp := true }
  | flag :: _ =>
      throw s!"未知参数 `{flag}`\n\n{usage}"

private def startsWithName (name : Name) (wantedPrefix : String) : Bool :=
  wantedPrefix.isEmpty || name.toString.startsWith wantedPrefix

private def proofUsesProveAuto (proof : Expr) : Bool :=
  proof.getUsedConstants.contains
    ``ProveAutoRequest.GoalAttempt.soundOfClosed

private def isGeneratedDeclaration
    (env : Environment) (name : Name) : Bool :=
  env.isProjectionFn name ||
    isAuxRecursor env name ||
    isNoConfusion env name ||
    isMatcherCore env name

private def candidateLess (left right : Candidate) : Bool :=
  if left.moduleIndex == right.moduleIndex then
    left.position.lt right.position
  else
    left.moduleIndex < right.moduleIndex

private def collectCandidates (config : Config) : MetaM CandidateSet := do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let moduleData := env.header.moduleData
  let mut values := #[]
  let mut theoremCount := 0
  let mut skippedExisting := 0
  for moduleIndex in [0 : moduleData.size] do
    let moduleName := moduleNames[moduleIndex]!
    unless moduleName.toString.startsWith config.modulePrefix do
      continue
    let data := moduleData[moduleIndex]!
    for declarationIndex in [0 : data.constants.size] do
      let some declarationName := data.constNames[declarationIndex]?
        | continue
      let .thmInfo theoremInfo := data.constants[declarationIndex]!
        | continue
      if isPrivateName declarationName ||
          isGeneratedDeclaration env declarationName then
        continue
      let some ranges ← findDeclarationRanges? declarationName
        | continue
      theoremCount := theoremCount + 1
      if !startsWithName declarationName config.namePrefix then
        continue
      if !config.includeExisting &&
          proofUsesProveAuto theoremInfo.value then
        skippedExisting := skippedExisting + 1
        continue
      let position := ranges.selectionRange.pos
      values := values.push {
        name := declarationName
        moduleName
        moduleIndex
        declarationPosition := ranges.range.pos
        declarationEndPosition := ranges.range.endPos
        position
        line := position.line
        type := theoremInfo.type
      }
  let sortedValues := values.qsort candidateLess
  let limitedValues :=
    if config.limit == 0 then sortedValues
    else sortedValues.take config.limit
  return {
    values := limitedValues
    theoremCount
    skippedExisting
  }

private def moduleImportClosure (env : Environment)
    (moduleIndex : Nat) : NameSet := Id.run do
  let moduleData := env.header.moduleData
  let mut visited : NameSet := {}
  let mut pending :=
    moduleData[moduleIndex]!.imports.map (·.module)
  while !pending.isEmpty do
    let moduleName := pending.back!
    pending := pending.pop
    if visited.contains moduleName then
      continue
    visited := visited.insert moduleName
    if let some importedIndex := env.getModuleIdx? moduleName then
      for imported in
          moduleData[importedIndex.toNat]!.imports do
        unless visited.contains imported.module do
          pending := pending.push imported.module
  return visited

private def pushNameUnique (values : Array Name)
    (value : Name) : Array Name :=
  if values.contains value then values else values.push value

private def inferBackend (constants : Array Name) : String :=
  if constants.any fun name =>
      name.toString.startsWith
        "YesMetaZFC.Automation.HostRules" then
    "HR"
  else if constants.any fun name =>
      name.toString.startsWith
        "YesMetaZFC.Automation.HostHigherOrder" then
    "HO"
  else if constants.any fun name =>
      name.toString.startsWith
        "YesMetaZFC.Automation.HostFirstOrder" then
    "FO"
  else
    "unknown"

private def collectExpressionAxioms (expression : Expr) :
    MetaM (Array Name) := do
  let mut axioms : NameSet := {}
  for declaration in expression.getUsedConstants do
    for ax in ← collectAxioms declaration do
      axioms := axioms.insert ax
  return axioms.toArray.qsort Name.lt

private def isNativeTicket (env : Environment) (name : Name) : Bool :=
  match env.find? name with
  | some (.axiomInfo _) =>
      let text := name.toString
      text.contains "_native" || text.contains "native_decide"
  | _ =>
      false

private def auditProof (candidate : Candidate)
    (proof : Expr) : MetaM ProofAudit := do
  let env ← getEnv
  let imports := moduleImportClosure env candidate.moduleIndex
  let moduleNames := env.header.moduleNames
  let constants := proof.getUsedConstants
  let mut forbiddenDependencies := #[]
  let mut supportModules := #[]
  let mut generatedAuxiliaries := #[]
  for declaration in constants do
    if declaration == candidate.name then
      forbiddenDependencies :=
        pushNameUnique forbiddenDependencies declaration
      continue
    match env.getModuleIdxFor? declaration with
    | none =>
        if (env.find? declaration).isSome then
          generatedAuxiliaries :=
            pushNameUnique generatedAuxiliaries declaration
    | some moduleIndex =>
        let moduleName := moduleNames[moduleIndex]!
        if moduleIndex.toNat == candidate.moduleIndex then
          let earlier ←
            match ← findDeclarationRanges? declaration with
            | some ranges =>
                pure <| ranges.selectionRange.pos.lt
                  candidate.position
            | none =>
                pure false
          unless earlier do
            forbiddenDependencies :=
              pushNameUnique forbiddenDependencies declaration
        else if !imports.contains moduleName then
          if moduleName.toString.startsWith
              "YesMetaZFC.Automation" then
            supportModules :=
              pushNameUnique supportModules moduleName
          else
            forbiddenDependencies :=
              pushNameUnique forbiddenDependencies declaration
  let baselineAxioms := ← collectAxioms candidate.name
  let generatedAxioms := ← collectExpressionAxioms proof
  let mut nativeTickets := #[]
  let mut newAxioms := #[]
  for ax in generatedAxioms do
    unless baselineAxioms.contains ax do
      if isNativeTicket env ax then
        nativeTickets := nativeTickets.push ax
      else
        newAxioms := newAxioms.push ax
  return {
    backend := inferBackend constants
    proofConstants := constants.size
    forbiddenDependencies
    supportModules
    generatedAuxiliaries
    nativeTickets
    newAxioms
  }

private def truncate (value : String) (limit : Nat) : String :=
  if value.length <= limit then
    value
  else
    (value.take limit).toString ++ "..."

private def compactMessage (value : String) : String :=
  truncate (value.replace "\r" " " |>.replace "\n" " ") 800

private def classifyFailure (message : String) : String :=
  let lower := message.toLower
  if lower.contains "unsupported" ||
      lower.contains "not supported" ||
      lower.contains "could not reify" then
    "unsupported_frontend"
  else if lower.contains "routed backend failed" ||
      lower.contains "could not synthesize" ||
      lower.contains "did not close" then
    "not_closed"
  else
    "internal_error"

private def resultOfAudit (candidate : Candidate)
    (type : String) (audit : ProofAudit) : Result :=
  let status :=
    if !audit.forbiddenDependencies.isEmpty then
      "closed_forbidden_dependency"
    else if !audit.newAxioms.isEmpty then
      "closed_new_axioms"
    else if !audit.supportModules.isEmpty then
      "closed_support_import"
    else
      "closed_clean"
  {
    declaration := candidate.name
    moduleName := candidate.moduleName
    line := candidate.line
    type
    status
    backend := audit.backend
    proofConstants := audit.proofConstants
    forbiddenDependencies := audit.forbiddenDependencies
    supportModules := audit.supportModules
    generatedAuxiliaries := audit.generatedAuxiliaries
    nativeTickets := audit.nativeTickets
    newAxioms := audit.newAxioms
  }

private def optionsFor (config : Config) (options : Options) :
    Options :=
  options
    |>.set `prove_auto.context.maxFacts config.maxFacts
    |>.set `prove_auto.host.maxFacts config.maxFacts
    |>.set `prove_auto.hr.maxRules config.maxRules
    |>.setBool `prove_auto.replay.strictAudit config.strictAudit

private unsafe def runCandidateCore
    (candidate : Candidate) (type : String) :
    MetaM Result := do
  forallTelescopeReducing candidate.type fun arguments target => do
    unless ← isProp target do
      return {
        declaration := candidate.name
        moduleName := candidate.moduleName
        line := candidate.line
        type
        status := "unsupported_frontend"
        message := "Π-上下文的最终目标不是 Prop"
      }
    let goalExpression ← mkFreshExprMVar (some target)
    let goal := goalExpression.mvarId!
    let (remaining, _) ←
      Lean.Elab.runTactic goal (← `(tactic| prove_auto))
    unless remaining.isEmpty do
      return {
        declaration := candidate.name
        moduleName := candidate.moduleName
        line := candidate.line
        type
        status := "not_closed"
        message := s!"prove_auto 留下 {remaining.length} 个目标"
      }
    let proofBody ← instantiateMVars goalExpression
    if proofBody.hasMVar then
      throwError
        "prove_auto 扫描结果仍含 metavariable:{indentExpr proofBody}"
    let proof ← mkLambdaFVars arguments proofBody
    let proofType ← inferType proof
    unless ← isDefEq proofType candidate.type do
      throwError
        "prove_auto 扫描证明类型不匹配:\n得到{indentExpr proofType}\n\
        预期{indentExpr candidate.type}"
    resultOfAudit candidate type <$> auditProof candidate proof

private unsafe def runCandidate (config : Config)
    (candidate : Candidate) :
    MetaM Result := do
  let type :=
    truncate (toString (← ppExpr candidate.type)) 1600
  let savedState ← saveState
  let startedNs ← IO.monoNanosNow
  let startedHeartbeats ← IO.getNumHeartbeats
  tryCatchRuntimeEx
    (do
      let result ←
        withDeclNameForAuxNaming
          (candidate.name ++ `_proveAutoSweep) do
        withOptions (optionsFor config) do
        withTheReader Core.Context
            (fun context => {
              context with
              maxHeartbeats := config.maxHeartbeats * 1000
            }) do
          Core.withCurrHeartbeats do
            runCandidateCore candidate type
      let finishedNs ← IO.monoNanosNow
      let finishedHeartbeats ← IO.getNumHeartbeats
      savedState.restore
      return {
        result with
        elapsedNs := finishedNs - startedNs
        heartbeats :=
          (finishedHeartbeats - startedHeartbeats) / 1000
      })
    fun error => do
      let finishedNs ← IO.monoNanosNow
      let finishedHeartbeats ← IO.getNumHeartbeats
      let heartbeatExceeded := error.isMaxHeartbeat
      let message ←
        if heartbeatExceeded then
          pure "达到单目标心跳上限"
        else
          try
            withTheReader Core.Context
                (fun context => { context with maxHeartbeats := 0 }) do
              error.toMessageData.toString
          catch _ =>
            pure "无法渲染 prove_auto 异常"
      savedState.restore
      return {
        declaration := candidate.name
        moduleName := candidate.moduleName
        line := candidate.line
        type
        status :=
          if heartbeatExceeded then
            "heartbeat_exceeded"
          else
            classifyFailure message
        elapsedNs := finishedNs - startedNs
        heartbeats :=
          (finishedHeartbeats - startedHeartbeats) / 1000
        message := compactMessage message
      }

private def isSourceValidationCandidate (result : Result) : Bool :=
  result.status == "closed_clean" ||
    result.status == "closed_support_import"

private def moduleSourcePath (moduleName : Name) : System.FilePath :=
  System.FilePath.mk <|
    moduleName.toString.replace "." "/" ++ ".lean"

private def sanitizeFileName (name : Name) : String :=
  name.toString
    |>.replace "." "_"
    |>.replace "/" "_"
    |>.replace "\\" "_"
    |>.replace ":" "_"

private def sourceProbeText (config : Config)
    (type : String) : String :=
  String.intercalate "\n" [
    "",
    "/- prove_auto_sweep 声明现场整定理探针。 -/",
    s!"set_option maxHeartbeats {config.maxHeartbeats} in",
    s!"set_option prove_auto.context.maxFacts {config.maxFacts} in",
    s!"set_option prove_auto.host.maxFacts {config.maxFacts} in",
    s!"set_option prove_auto.hr.maxRules {config.maxRules} in",
    s!"set_option prove_auto.replay.strictAudit {config.strictAudit} in",
    s!"example : {type} := by",
    "  prove_auto",
    ""
  ]

private def insertAtPosition (source insertion : String)
    (position : Position) : String :=
  let source := source.crlfToLf
  let offset := (FileMap.ofString source).ofPosition position
  String.Pos.Raw.extract source 0 offset ++
    insertion ++
    String.Pos.Raw.extract source offset source.rawEndPos

private def sourceWithDispatchImport (source : String) : String :=
  "import YesMetaZFC.Automation.HostAvatar.Dispatch\n" ++ source

private def ensureParent (path : System.FilePath) : IO Unit := do
  if let some parent := path.parent then
    IO.FS.createDirAll parent

structure SourceProbe where
  closed : Bool
  requiresImport : Bool := false
  elapsedNs : Nat := 0
  message : String := ""

private def runLeanSource (cwd path : System.FilePath) :
    IO (UInt32 × String) := do
  let output ← IO.Process.output {
    cmd := "lake"
    args := #["env", "lean", path.toString]
    cwd := some cwd
  }
  return (
    output.exitCode,
    compactMessage <|
      if output.stderr.isEmpty then output.stdout
      else output.stderr ++ "\n" ++ output.stdout
  )

private def collectProcessOutput
    (stdout stderr : Task (Except IO.Error String))
    (exitCode : UInt32) : IO IO.Process.Output := do
  return {
    exitCode
    stdout := ← IO.ofExcept stdout.get
    stderr := ← IO.ofExcept stderr.get
  }

private partial def waitProcessOutput
    {cfg : IO.Process.StdioConfig}
    (child : IO.Process.Child cfg)
    (stdout stderr : Task (Except IO.Error String))
    (remainingMs timeoutMs : Nat) :
    IO IO.Process.Output := do
  if let some exitCode ← child.tryWait then
    return ← collectProcessOutput stdout stderr exitCode
  if remainingMs == 0 then
    child.kill
    discard child.wait
    let output ← collectProcessOutput stdout stderr 124
    return {
      output with
      stderr := output.stderr ++
        (if output.stderr.isEmpty then "" else "\n") ++
        s!"prove_auto_sweep 子目标临时编译超过 {timeoutMs} ms"
    }
  let sleepMs := min 50 remainingMs
  IO.sleep sleepMs.toUInt32
  waitProcessOutput child stdout stderr
    (remainingMs - sleepMs) timeoutMs

private def runLeanSourceOutput (cwd path : System.FilePath)
    (maxHeartbeats timeoutMs : Nat) :
    IO IO.Process.Output := do
  let args : IO.Process.SpawnArgs := {
    cmd := "lean"
    args := #[
      s!"-DmaxHeartbeats={maxHeartbeats}",
      path.toString
    ]
    cwd := some cwd
  }
  if timeoutMs == 0 then
    return ← IO.Process.output args
  let child ← IO.Process.spawn {
    args with
    stdout := .piped
    stderr := .piped
    stdin := .null
  }
  let stdout ←
    IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let stderr ←
    IO.asTask child.stderr.readToEnd Task.Priority.dedicated
  waitProcessOutput child stdout stderr timeoutMs timeoutMs

private def writeAndRunSourceProbe (cwd tempPath : System.FilePath)
    (source : String) : IO (UInt32 × String) := do
  ensureParent tempPath
  IO.FS.writeFile tempPath source
  runLeanSource cwd tempPath

private def sourceProbe (config : Config) (candidate : Candidate)
    (type : String) : IO SourceProbe := do
  let cwd ← IO.Process.getCurrentDir
  let sourcePath := cwd / moduleSourcePath candidate.moduleName
  unless ← sourcePath.pathExists do
    return {
      closed := false
      message := s!"找不到声明源文件 `{sourcePath}`"
    }
  let source ← IO.FS.readFile sourcePath
  let probe := sourceProbeText config type
  let inserted :=
    insertAtPosition source probe candidate.declarationPosition
  let tempPath :=
    cwd / "tmp" / "prove_auto_sweep_source" /
      s!"{sanitizeFileName candidate.name}.lean"
  let startedNs ← IO.monoNanosNow
  let (plainExit, plainMessage) ←
    writeAndRunSourceProbe cwd tempPath inserted
  if plainExit == 0 then
    return {
      closed := true
      elapsedNs := (← IO.monoNanosNow) - startedNs
    }
  let (importExit, importMessage) ←
    writeAndRunSourceProbe cwd tempPath
      (sourceWithDispatchImport inserted)
  let elapsedNs := (← IO.monoNanosNow) - startedNs
  if importExit == 0 then
    return {
      closed := true
      requiresImport := true
      elapsedNs
    }
  return {
    closed := false
    elapsedNs
    message :=
      "原导入图: " ++ plainMessage ++
      " | 补 Dispatch: " ++ importMessage
  }

private unsafe def validateAtSource (config : Config)
    (candidate : Candidate) (result : Result) : MetaM Result := do
  unless config.sourceValidate &&
      isSourceValidationCandidate result do
    return result
  let type ←
    withOptions (fun options =>
      options
        |>.setBool `pp.universes true
        |>.setBool `pp.explicit false) do
      return toString (← ppExpr candidate.type)
  let probe ← sourceProbe config candidate type
  if probe.closed then
    return {
      result with
      status := "closed_source_verified"
      prefilterStatus := result.status
      sourceElapsedNs := probe.elapsedNs
      sourceRequiresImport := probe.requiresImport
    }
  return {
    result with
    status := "closed_source_rejected"
    prefilterStatus := result.status
    sourceElapsedNs := probe.elapsedNs
    message := probe.message
  }

structure BranchTarget where
  id : String
  resultIndex : Nat
  start : String.Pos.Raw
  stop : String.Pos.Raw
  startPosition : Position
  endPosition : Position
  source : String
  deriving Inhabited

structure SourceEdit where
  start : String.Pos.Raw
  stop : String.Pos.Raw
  replacement : String

private def spaces (count : Nat) : String :=
  String.ofList (List.replicate count ' ')

private def indentBranchBody (column : Nat)
    (source : String) : String :=
  match source.splitOn "\n" with
  | [] =>
      ""
  | first :: rest =>
      rest.foldl
        (fun value line => value ++ "\n  " ++ line)
        (spaces (column + 2) ++ first)

private def branchReplacement (config : Config)
    (target : BranchTarget) : String :=
  s!"prove_auto_sweep_branch \"{target.id}\" \
    {config.maxHeartbeats} {config.maxFacts} {config.maxRules} \
    {config.strictAudit} =>\n" ++
    indentBranchBody target.startPosition.column target.source

private def applySourceEdits (source : String)
    (edits : Array SourceEdit) : String :=
  let ordered :=
    edits.qsort fun left right =>
      left.start.byteIdx > right.start.byteIdx
  ordered.foldl (init := source) fun current edit =>
    String.Pos.Raw.extract current 0 edit.start ++
      edit.replacement ++
      String.Pos.Raw.extract current edit.stop current.rawEndPos

private partial def collectImmediateTacticSequences
    (fileMap : FileMap)
    (declarationStart declarationStop : String.Pos.Raw)
    (stx : Syntax) (tacticDepth : Nat := 0) :
    Array (String.Pos.Raw × String.Pos.Raw × Position × Position) := Id.run do
  let isTacticSequence :=
    stx.isOfKind ``Lean.Parser.Tactic.tacticSeq
  let nextDepth :=
    if isTacticSequence then tacticDepth + 1 else tacticDepth
  if isTacticSequence && tacticDepth == 1 then
    if let some range := stx.getRange? then
      if declarationStart <= range.start &&
          range.stop <= declarationStop then
        return #[(
          range.start,
          range.stop,
          fileMap.toPosition range.start,
          fileMap.toPosition range.stop
        )]
  let mut ranges := #[]
  for child in stx.getArgs do
    ranges := ranges ++
      collectImmediateTacticSequences fileMap
        declarationStart declarationStop child nextDepth
  return ranges

private def branchTargetsForCandidate (source : String)
    (fileMap : FileMap) (moduleSyntax : Syntax)
    (candidate : Candidate) (resultIndex : Nat) :
    Array BranchTarget := Id.run do
  let declarationStart :=
    fileMap.ofPosition candidate.declarationPosition
  let declarationStop :=
    fileMap.ofPosition candidate.declarationEndPosition
  let ranges :=
    collectImmediateTacticSequences fileMap
      declarationStart declarationStop moduleSyntax
  let mut targets := Array.mkEmpty ranges.size
  for branchIndex in [0 : ranges.size] do
    let (start, stop, startPosition, endPosition) :=
      ranges[branchIndex]!
    targets := targets.push {
      id := s!"r{resultIndex}_b{branchIndex}"
      resultIndex
      start
      stop
      startPosition
      endPosition
      source := String.Pos.Raw.extract source start stop
    }
  return targets

private def markerIds (output : IO.Process.Output) : Array String := Id.run do
  let marker := "PROVE_AUTO_SWEEP_BRANCH "
  let text := output.stdout ++ "\n" ++ output.stderr
  let mut ids := #[]
  for line in text.splitOn "\n" do
    let line := line.trimAscii.toString
    if line.startsWith marker then
      ids := ids.push <|
        (line.drop marker.length).toString.trimAscii.toString
  return ids

private def sourceEditOfBranch (config : Config)
    (target : BranchTarget) : SourceEdit := {
  start := target.start
  stop := target.stop
  replacement := branchReplacement config target
}

private def resultWithSubgoal (result : Result)
    (target : BranchTarget) (elapsedNs : Nat) : Result :=
  let hit : SubgoalHit := {
    id := target.id
    startLine := target.startPosition.line
    startColumn := target.startPosition.column
    endLine := target.endPosition.line
    endColumn := target.endPosition.column
    source := truncate target.source 500
  }
  {
    result with
    status :=
      if result.status == "closed_source_verified" then
        result.status
      else
        "closed_subgoals_verified"
    prefilterStatus :=
      if result.prefilterStatus.isEmpty then
        result.status
      else
        result.prefilterStatus
    subgoalElapsedNs := elapsedNs
    subgoals := result.subgoals.push hit
  }

private def batchContainsResultIndex
    (batch : Array BranchTarget) (index : Nat) : Bool :=
  batch.any fun target => target.resultIndex == index

private def addBatchElapsed (results : Array Result)
    (batch : Array BranchTarget) (elapsedNs : Nat) :
    Array Result :=
  results.mapIdx fun index result =>
    if batchContainsResultIndex batch index then
      {
        result with
        subgoalElapsedNs := result.subgoalElapsedNs + elapsedNs
      }
    else
      result

private partial def runBranchBatch (config : Config)
    (cwd : System.FilePath) (source : String)
    (moduleName : Name) (batch : Array BranchTarget)
    (label : String) (results : Array Result) :
    IO (Array Result) := do
  let edits := batch.map (sourceEditOfBranch config)
  let instrumented :=
    "import YesMetaZFC.Automation.Tools.ProveAutoBranchProbe\n" ++
      applySourceEdits source edits
  let tempPath :=
    cwd / "tmp" / "prove_auto_sweep_branches" /
      s!"{sanitizeFileName moduleName}_batch{label}.lean"
  ensureParent tempPath
  IO.FS.writeFile tempPath instrumented
  IO.println
    s!"[subgoals] {moduleName}; batch={label}; \
      branches={batch.size}"
  let startedNs ← IO.monoNanosNow
  /-
  分支各自有独立预算；文件级预算还需容纳原模块证明，否则多个探针会
  共同耗尽 Lean 默认的 200000 心跳并制造批次假失败。
  -/
  let moduleHeartbeats :=
    if config.maxHeartbeats == 0 then
      0
    else
      200000 + config.maxHeartbeats * batch.size
  let output ←
    runLeanSourceOutput cwd tempPath moduleHeartbeats
      config.subgoalTimeoutMs
  let elapsedNs := (← IO.monoNanosNow) - startedNs
  let updated := addBatchElapsed results batch elapsedNs
  if output.exitCode == 0 then
    let ids := markerIds output
    let mut accepted := updated
    for target in batch do
      if ids.contains target.id then
        accepted := accepted.set! target.resultIndex <|
          resultWithSubgoal accepted[target.resultIndex]!
            target accepted[target.resultIndex]!.subgoalElapsedNs
    return accepted
  if batch.size > 1 then
    let middle := batch.size / 2
    let left := batch.extract 0 middle
    let right := batch.extract middle batch.size
    IO.println
      s!"[subgoals-retry] {moduleName}; batch={label}; \
        split={left.size}+{right.size}"
    let updated ←
      runBranchBatch config cwd source moduleName left
        (label ++ "L") updated
    return ←
      runBranchBatch config cwd source moduleName right
        (label ++ "R") updated
  let message :=
    compactMessage <|
      if output.stderr.isEmpty then output.stdout
      else output.stderr ++ "\n" ++ output.stdout
  let target := batch[0]!
  return updated.set! target.resultIndex {
    updated[target.resultIndex]! with
    subgoalProbeMessage :=
      updated[target.resultIndex]!.subgoalProbeMessage ++
        s!"[branch {target.startPosition.line}:\
          {target.startPosition.column}] " ++ message
  }

private unsafe def probeModuleSubgoals (config : Config)
    (candidates : CandidateSet) (results : Array Result)
    (moduleName : Name) : MetaM (Array Result) := do
  let cwd ← IO.Process.getCurrentDir
  let sourcePath := cwd / moduleSourcePath moduleName
  unless ← sourcePath.pathExists do
    return results
  let source ← IO.FS.readFile sourcePath
  let source := source.crlfToLf
  let fileMap := FileMap.ofString source
  let moduleSyntax ←
    Parser.testParseModule (← getEnv) sourcePath.toString source
  let mut targets := #[]
  for resultIndex in [0 : candidates.values.size] do
    let candidate := candidates.values[resultIndex]!
    let result := results[resultIndex]!
    if candidate.moduleName == moduleName &&
        result.status != "closed_source_verified" then
      targets := targets ++
        branchTargetsForCandidate source fileMap moduleSyntax
          candidate resultIndex
  if targets.isEmpty then
    return results
  let batchSize :=
    if config.subgoalBatchSize == 0 then
      targets.size
    else
      config.subgoalBatchSize
  let batchCount :=
    (targets.size + batchSize - 1) / batchSize
  let mut updated := results
  for batchIndex in [0 : batchCount] do
    let start := batchIndex * batchSize
    let stop := min targets.size (start + batchSize)
    let batch := targets.extract start stop
    updated ←
      runBranchBatch config cwd source moduleName batch
        s!"{batchIndex + 1}of{batchCount}" updated
  return updated

private unsafe def validateSubgoals (config : Config)
    (candidates : CandidateSet) (results : Array Result) :
    MetaM (Array Result) := do
  unless config.subgoalFallback do
    return results
  let mut processed : NameSet := {}
  let mut updated := results
  for candidate in candidates.values do
    unless processed.contains candidate.moduleName do
      processed := processed.insert candidate.moduleName
      updated ←
        probeModuleSubgoals config candidates updated
          candidate.moduleName
  return updated

private unsafe def scan (config : Config) :
    MetaM (CandidateSet × Array Result) := do
  let candidates ← collectCandidates config
  let mut results := Array.mkEmpty candidates.values.size
  let mut position := 0
  for candidate in candidates.values do
    IO.println
      s!"[{position + 1}/{candidates.values.size}] {candidate.name}"
    let prefilter ← runCandidate config candidate
    let result ← validateAtSource config candidate prefilter
    IO.println
      s!"  {result.status}; backend={result.backend}; \
      hb={result.heartbeats}; elapsedNs={result.elapsedNs}; \
      sourceElapsedNs={result.sourceElapsedNs}"
    results := results.push result
    position := position + 1
  results ← validateSubgoals config candidates results
  return (candidates, results)

private def namesJson (names : Array Name) : Json :=
  Json.arr <| names.map fun name => Json.str name.toString

private def subgoalJson (hit : SubgoalHit) : Json :=
  Json.mkObj [
    ("id", Json.str hit.id),
    ("start_line", toJson hit.startLine),
    ("start_column", toJson hit.startColumn),
    ("end_line", toJson hit.endLine),
    ("end_column", toJson hit.endColumn),
    ("source", Json.str hit.source)
  ]

private def resultJson (result : Result) : Json :=
  Json.mkObj [
    ("declaration", Json.str result.declaration.toString),
    ("module", Json.str result.moduleName.toString),
    ("line", toJson result.line),
    ("type", Json.str result.type),
    ("status", Json.str result.status),
    ("prefilter_status", Json.str result.prefilterStatus),
    ("backend", Json.str result.backend),
    ("elapsed_ns", toJson result.elapsedNs),
    ("heartbeats", toJson result.heartbeats),
    ("source_elapsed_ns", toJson result.sourceElapsedNs),
    ("source_requires_import", toJson result.sourceRequiresImport),
    ("subgoal_elapsed_ns", toJson result.subgoalElapsedNs),
    ("subgoals", Json.arr <| result.subgoals.map subgoalJson),
    ("subgoal_probe_message",
      Json.str result.subgoalProbeMessage),
    ("proof_constants", toJson result.proofConstants),
    ("forbidden_dependencies",
      namesJson result.forbiddenDependencies),
    ("support_modules", namesJson result.supportModules),
    ("generated_auxiliaries",
      namesJson result.generatedAuxiliaries),
    ("native_tickets", namesJson result.nativeTickets),
    ("new_axioms", namesJson result.newAxioms),
    ("message", Json.str result.message)
  ]

private def statusCount (results : Array Result)
    (status : String) : Nat :=
  results.foldl
    (fun count result =>
      if result.status == status then count + 1 else count)
    0

private def markdownEscape (value : String) : String :=
  value.replace "|" "\\|" |>.replace "\r" " " |>.replace "\n" " "

private def renderMarkdown (config : Config)
    (candidates : CandidateSet) (results : Array Result) : String :=
  let ordered :=
    results.qsort fun left right =>
      if left.status == right.status then
        left.heartbeats < right.heartbeats
      else
        left.status < right.status
  let header := String.intercalate "\n" [
    "# prove_auto 批量扫描报告",
    "",
    s!"- 模块前缀：`{config.modulePrefix}`",
    s!"- 声明名前缀：`{config.namePrefix}`",
    s!"- 扫描目标：{results.size}",
    s!"- 模块内 theorem 数：{candidates.theoremCount}",
    s!"- 跳过既有 prove_auto：{candidates.skippedExisting}",
    s!"- 每目标心跳上限：{config.maxHeartbeats}",
    s!"- 自动事实：{config.maxFacts}",
    s!"- HR 规则上限：{config.maxRules}",
    s!"- 纯 Lean replay：{config.strictAudit}",
    s!"- 声明现场源码复核：{config.sourceValidate}",
    s!"- 已拆分子目标回退：{config.subgoalFallback}",
    s!"- 子目标单批上限：{config.subgoalBatchSize}",
    s!"- 子目标临时编译墙钟上限：{config.subgoalTimeoutMs} ms",
    s!"- closed_source_verified：{statusCount results "closed_source_verified"}",
    s!"- closed_source_rejected：{statusCount results "closed_source_rejected"}",
    s!"- closed_subgoals_verified：{statusCount results "closed_subgoals_verified"}",
    s!"- closed_clean：{statusCount results "closed_clean"}",
    s!"- closed_support_import：{statusCount results "closed_support_import"}",
    s!"- closed_forbidden_dependency：{statusCount results "closed_forbidden_dependency"}",
    s!"- closed_new_axioms：{statusCount results "closed_new_axioms"}",
    s!"- heartbeat_exceeded：{statusCount results "heartbeat_exceeded"}",
    s!"- not_closed：{statusCount results "not_closed"}",
    s!"- unsupported_frontend：{statusCount results "unsupported_frontend"}",
    s!"- internal_error：{statusCount results "internal_error"}",
    "",
    "| declaration | source | status | backend | heartbeats | elapsed ms | subgoals | native tickets | note |",
    "|---|---|---:|---:|---:|---:|---:|---:|---|"
  ]
  ordered.foldl (init := header) fun report result =>
    let note :=
      if !result.subgoals.isEmpty then
        "verified ranges: " ++
          String.intercalate ", "
            (result.subgoals.map fun hit =>
              s!"{hit.startLine}:{hit.startColumn}-\
                {hit.endLine}:{hit.endColumn}").toList
      else if !result.forbiddenDependencies.isEmpty then
        "forbidden: " ++
          String.intercalate ", "
            (result.forbiddenDependencies.map (·.toString)).toList
      else if !result.newAxioms.isEmpty then
        "new axioms: " ++
          String.intercalate ", "
            (result.newAxioms.map (·.toString)).toList
      else if !result.supportModules.isEmpty then
        "support imports: " ++
          String.intercalate ", "
            (result.supportModules.map (·.toString)).toList
      else if result.sourceRequiresImport then
        "source verified; requires Dispatch import"
      else if !result.subgoalProbeMessage.isEmpty then
        result.subgoalProbeMessage
      else
        result.message
    report ++ "\n| " ++ markdownEscape result.declaration.toString ++
      " | " ++ markdownEscape
        s!"{result.moduleName}:{result.line}" ++
      " | " ++ result.status ++
      " | " ++ result.backend ++
      " | " ++ toString result.heartbeats ++
      " | " ++ toString (result.elapsedNs / 1000000) ++
      " | " ++ toString result.subgoals.size ++
      " | " ++ toString result.nativeTickets.size ++
      " | " ++ markdownEscape note ++ " |"

private def writeReports (config : Config)
    (candidates : CandidateSet) (results : Array Result) : IO Unit := do
  let jsonPath : System.FilePath := config.output
  let markdownPath : System.FilePath := config.markdown
  ensureParent jsonPath
  ensureParent markdownPath
  let jsonl :=
    String.intercalate "\n"
      (results.map fun result =>
        (resultJson result).compress).toList
  IO.FS.writeFile jsonPath
    (if jsonl.isEmpty then "" else jsonl ++ "\n")
  IO.FS.writeFile markdownPath
    (renderMarkdown config candidates results ++ "\n")

private unsafe def runIO (config : Config) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let options :=
    Options.empty
      |>.set `maxHeartbeats 0
      |>.set `maxRecDepth 100000
  let env ←
    importModules #[{ module := `YesMetaZFC }]
      options
      (leakEnv := true)
      (loadExts := true)
  let env :=
    env.setMainModule
      `YesMetaZFC.Automation.Tools.ProveAutoSweep.Runtime
  let coreContext : Core.Context := {
    fileName := "<prove_auto_sweep>"
    fileMap := FileMap.ofString ""
    options
    maxRecDepth := 100000
    maxHeartbeats := 0
  }
  let coreState : Core.State := { env }
  let ((candidates, results), _, _) ←
    MetaM.toIO (scan config) coreContext coreState
  writeReports config candidates results
  IO.println
    s!"wrote {results.size} results to {config.output} and {config.markdown}"
  return (0 : UInt32)

unsafe def cli (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error message =>
      IO.eprintln message
      return (2 : UInt32)
  | .ok config =>
      if config.showHelp then
        IO.println usage
        return (0 : UInt32)
      try
        runIO config
      catch error =>
        IO.eprintln s!"prove_auto_sweep failed: {error}"
        return (1 : UInt32)

end ProveAutoSweep
end Tools
end Automation
end YesMetaZFC

unsafe def main (args : List String) : IO UInt32 :=
  YesMetaZFC.Automation.Tools.ProveAutoSweep.cli args
