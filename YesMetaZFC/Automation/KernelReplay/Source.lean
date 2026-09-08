import YesMetaZFC.Automation.KernelReplay
import YesMetaZFC.Automation.SourcePreprocessing

/-!
# Source preprocessing 的内核重放

本模块独占预处理证书与一阶 source replay 的元层证明项生成。通用 `KernelReplay`
不再反向依赖 source provider、投影语义或完备性实现。
-/

namespace YesMetaZFC
namespace Automation
namespace KernelReplay

open Lean Meta

private def traceRemainingHeartbeats (label : String) : MetaM Unit := do
  let remaining ← getRemainingHeartbeats
  trace[YesMetaZFC.proveAuto.kernelReplay]
    "{label}; remainingHb={remaining / 1000}"

private inductive SourceReplayKind where
  | firstOrder
  | fool
private inductive SourceReplayTickets where
  | avatar (arena registry registryCheck : Expr)
  | guarded (arena guardedCheck : Expr)
private def definitionalCnfCheckProof (definitionalCnfExpr : Expr) : MetaM Expr := do
  let config ←
    mkAppM ``CoreSyntax.NormalForm.DefinitionalCnfPayload.config
      #[definitionalCnfExpr]
  let contextSorts ←
    mkAppM ``CoreSyntax.NormalForm.DefinitionalCnfPayload.contextSorts
      #[definitionalCnfExpr]
  let source ←
    mkAppM ``CoreSyntax.NormalForm.DefinitionalCnfPayload.source
      #[definitionalCnfExpr]
  let quantifierFree ←
    mkAppM ``CoreSyntax.NormalForm.Nnf.quantifierFree #[source]
  let hQuantifierFree ←
    boolTrueProof "preprocessing definitional CNF quantifier free" quantifierFree
  let sourceFormula ←
    mkAppM ``CoreSyntax.NormalForm.Nnf.toFormula #[source]
  let sourceCheck ←
    mkAppM ``CoreSyntax.Formula.checkWith #[contextSorts, sourceFormula]
  let hSourceCheck ←
    boolTrueProof "preprocessing definitional CNF source syntax" sourceCheck
  let built ←
    mkAppM ``CoreSyntax.NormalForm.DefinitionalCnfPayload.build
      #[config, contextSorts, source]
  let definitions ←
    mkAppM ``CoreSyntax.NormalForm.DefinitionalCnfPayload.definitions #[built]
  let definitionsList ← mkAppM ``Array.toList #[definitions]
  let definitionsCheck ←
    mkAppM ``List.all
      #[definitionsList,
        mkConst ``CoreSyntax.NormalForm.DefinitionalCnf.Definition.check]
  let hDefinitionsCheck ←
    boolTrueProof "preprocessing definitional CNF definitions" definitionsCheck
  let hBuilt ←
    mkAppM
      ``CoreSyntax.NormalForm.Semantics.DefinitionalCnfPayload.check_build_eq_true_of_components
      #[config, contextSorts, source, hQuantifierFree, hSourceCheck,
        hDefinitionsCheck]
  let actualCheck ←
    mkAppM ``CoreSyntax.NormalForm.DefinitionalCnfPayload.check
      #[definitionalCnfExpr]
  let expectedType ← mkEq actualCheck (mkConst ``Bool.true)
  return mkExpectedPropHint hBuilt expectedType
private def preprocessingLinkCheckProof (payloadExpr : Expr) : MetaM Expr := do
  let source ←
    mkAppM ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.source #[payloadExpr]
  let normalized ←
    mkAppM ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.normalized #[payloadExpr]
  let normalizationTrace ←
    mkAppM
      ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.normalizationTrace
      #[payloadExpr]
  let traceSource ←
    mkAppM ``CoreSyntax.NormalForm.Trace.source #[normalizationTrace]
  let traceTarget ←
    mkAppM ``CoreSyntax.NormalForm.Trace.target #[normalizationTrace]
  let sourceTraceExpr ←
    mkAppM ``CoreSyntax.NormalForm.TraceExpr.formula #[source]
  let normalizedTraceExpr ←
    mkAppM ``CoreSyntax.NormalForm.TraceExpr.formula #[normalized]
  let hTraceSource ←
    reflectedEqualityBoolProof "preprocessing trace source link"
      ``CoreSyntax.NormalForm.Semantics.TraceExpr.eq_eq_true
      traceSource sourceTraceExpr
  let hTraceTarget ←
    reflectedEqualityBoolProof "preprocessing trace target link"
      ``CoreSyntax.NormalForm.Semantics.TraceExpr.eq_eq_true
      traceTarget normalizedTraceExpr
  let initialNnf ←
    mkAppM ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.initialNnf
      #[payloadExpr]
  let positiveNnf ←
    mkAppM ``CoreSyntax.NormalForm.toNnfWith
      #[mkConst ``CoreSyntax.NormalForm.Polarity.positive, normalized]
  let hInitialNnf ←
    reflectedEqualityBoolProof "preprocessing initial NNF link"
      ``CoreSyntax.NormalForm.SyntaxEq.nnfEq_eq_true
      initialNnf positiveNnf
  let antiPrenex ←
    mkAppM ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.antiPrenex
      #[payloadExpr]
  let antiPrenexSource ←
    mkAppM ``CoreSyntax.NormalForm.AntiPrenexPayload.source #[antiPrenex]
  let antiPrenexResult ←
    mkAppM ``CoreSyntax.NormalForm.AntiPrenexPayload.result #[antiPrenex]
  let hAntiPrenex ←
    reflectedEqualityBoolProof "preprocessing anti-prenex source link"
      ``CoreSyntax.NormalForm.SyntaxEq.nnfEq_eq_true
      antiPrenexSource initialNnf
  let localSkolem ←
    mkAppM ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.localSkolem
      #[payloadExpr]
  let localSkolemSource ←
    mkAppM ``CoreSyntax.NormalForm.LocalSkolemPayload.source #[localSkolem]
  let localSkolemResult ←
    mkAppM ``CoreSyntax.NormalForm.LocalSkolemPayload.result #[localSkolem]
  let hLocalSkolem ←
    reflectedEqualityBoolProof "preprocessing local Skolem source link"
      ``CoreSyntax.NormalForm.SyntaxEq.nnfEq_eq_true
      localSkolemSource antiPrenexResult
  let definitionalCnf ←
    mkAppM ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.definitionalCnf
      #[payloadExpr]
  let definitionalCnfSource ←
    mkAppM ``CoreSyntax.NormalForm.DefinitionalCnfPayload.source #[definitionalCnf]
  let hDefinitionalCnf ←
    reflectedEqualityBoolProof "preprocessing definitional CNF source link"
      ``CoreSyntax.NormalForm.SyntaxEq.nnfEq_eq_true
      definitionalCnfSource localSkolemResult
  let clauses ←
    mkAppM ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.clauses #[payloadExpr]
  let definitionalCnfClauses ←
    mkAppM ``CoreSyntax.NormalForm.DefinitionalCnfPayload.clauses #[definitionalCnf]
  let hClauses ←
    reflectedEqualityBoolProof "preprocessing clause output link"
      ``CoreSyntax.NormalForm.Semantics.ClauseSet.eq_eq_true
      clauses definitionalCnfClauses
  mkAppM
    ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.linkCheck_eq_true_of_components
    #[payloadExpr, hTraceSource, hTraceTarget, hInitialNnf, hAntiPrenex,
      hLocalSkolem, hDefinitionalCnf, hClauses]

/-- 预处理证书的纯 Lean 分解证明，仅供严格审计路径使用。 -/
private def strictSourceReplayProof
    (kind : SourceReplayKind) (sourceProblem refutationSource payloadExpr : Expr)
    (rawPayloadExprs : PreprocessingPayloadExprs) : MetaM Expr := do
  let payloadSource ←
    mkAppM ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.source
      #[payloadExpr]
  let normalized ←
    mkAppM ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.normalized
      #[payloadExpr]
  let sourceSyntaxCheck ←
    mkAppM ``CoreSyntax.Formula.check? #[payloadSource]
  let hSourceSyntax ←
    boolTrueProof "preprocessing source syntax" sourceSyntaxCheck
  let normalizedSyntaxCheck ←
    mkAppM ``CoreSyntax.Formula.check? #[normalized]
  let hNormalizedSyntax ←
    boolTrueProof "preprocessing normalized syntax" normalizedSyntaxCheck
  traceRemainingHeartbeats "checked source syntax"
  let settings ←
    mkAppM ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.settings
      #[payloadExpr]
  let normalFormConfig ←
    mkAppM ``CoreSyntax.NormalForm.CheckedPreprocessing.Settings.normalForm
      #[settings]
  let normalizationTrace ←
    mkAppM
      ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.normalizationTrace
      #[payloadExpr]
  let traceCheck ←
    mkAppM ``CoreSyntax.NormalForm.Trace.check
      #[normalFormConfig, normalizationTrace]
  let hTrace ←
    boolTrueProof "preprocessing normalization trace" traceCheck
  traceRemainingHeartbeats "checked normalization trace"
  let antiPrenex ←
    mkAppM ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.antiPrenex
      #[payloadExpr]
  let antiPrenexResult ←
    mkAppM ``CoreSyntax.NormalForm.AntiPrenexPayload.result #[antiPrenex]
  let antiPrenexCheck ←
    mkAppM ``CoreSyntax.NormalForm.AntiPrenexPayload.check #[antiPrenex]
  let hAntiPrenex ←
    boolTrueProof "preprocessing anti-prenex payload" antiPrenexCheck
  traceRemainingHeartbeats "checked anti-prenex payload"
  let localSkolem ←
    mkAppM ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.localSkolem
      #[payloadExpr]
  let localSkolemCheck ←
    mkAppM ``CoreSyntax.NormalForm.LocalSkolemPayload.check #[localSkolem]
  let hLocalSkolem ←
    boolTrueProof "preprocessing local Skolem payload" localSkolemCheck
  traceRemainingHeartbeats "checked local Skolem payload"
  let hDefinitionalCnf ←
    definitionalCnfCheckProof rawPayloadExprs.definitionalCnf
  traceRemainingHeartbeats "checked definitional CNF payload"
  let hPhase ←
    mkAppM
      ``SourcePreprocessing.FirstOrderReplay.phaseCheck_eq_true_of_components
      #[payloadExpr, hSourceSyntax, hNormalizedSyntax, hTrace,
        hAntiPrenex, hLocalSkolem, hDefinitionalCnf]
  let hLink ←
    preprocessingLinkCheckProof payloadExpr
  traceRemainingHeartbeats "checked preprocessing links"
  let hSourceCheck ←
    reflectedEqualityBoolProof "preprocessing source equality"
      ``CoreSyntax.NormalForm.SyntaxEq.formulaEq_eq_true
      payloadSource refutationSource
  traceRemainingHeartbeats "checked source alignment"
  let freeCheck ←
    mkAppM
      ``CoreSyntax.NormalForm.Semantics.FreeSupport.nnfFreeClosed
      #[antiPrenexResult]
  let hFree ←
    boolTrueProof "preprocessing free closure" freeCheck
  let clauses ←
    mkAppM ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.clauses
      #[payloadExpr]
  let projectableCheck ←
    mkAppM
      ``CoreSyntax.NormalForm.FirstOrderProjection.Projectable.clauseSet
      #[clauses]
  let hProjectable ←
    boolTrueProof "first-order clause projection" projectableCheck
  traceRemainingHeartbeats "checked projection boundary"
  let hReplay ←
    match kind with
    | .firstOrder =>
        let hNormalization ←
          reflectedEqualityBoolProof "first-order normalization identity"
            ``CoreSyntax.NormalForm.SyntaxEq.formulaEq_eq_true
            normalized payloadSource
        mkAppM
          ``SourcePreprocessing.FirstOrderReplay.check_eq_true_of_components
          #[sourceProblem, payloadExpr, hPhase, hLink,
            hSourceCheck, hFree, hProjectable, hNormalization]
    | .fool =>
        let foolCheck ←
          mkAppM ``CoreSyntax.NormalForm.Trace.foolCheck
            #[normalizationTrace]
        let hFool ←
          boolTrueProof "FOOL normalization trace boundary" foolCheck
        mkAppM ``SourcePreprocessing.FoolReplay.check_eq_true_of_components
          #[sourceProblem, payloadExpr, hPhase, hLink,
            hSourceCheck, hFree, hProjectable, hFool]
  traceRemainingHeartbeats "composed strict preprocessing replay"
  pure hReplay

/--
把元层的一阶搜索产物拆成 preprocessing 与 DAG 的小型 checked 证明项。
返回值只含纯数据引用及其 checker 证明；具体宿主语义仍由各 provider 自己的
universe-polymorphic bridge 消费。
-/
private def sourceReplayExprs (kind : SourceReplayKind)
    (sourceProblemValue : SourcePreprocessing.Problem)
    (sourceProblem problem compiled settingsExpr : Expr)
    (payload : SourcePreprocessing.Payload)
    (artifact : SourcePreprocessing.Result.AvatarRunArtifact) (label : String) : MetaM ReplayExprs := do
  traceRemainingHeartbeats "start source replay"
  let refutationSource ←
    mkAppM ``SourcePreprocessing.Problem.refutationSource #[sourceProblem]
  let normalizedExpr :=
    if CoreSyntax.NormalForm.SyntaxEq.formulaEq payload.normalized payload.source then
      refutationSource
    else
      toExpr payload.normalized
  let rawPayloadExprs ←
    preprocessingPayloadExprs refutationSource normalizedExpr
      settingsExpr
      payload.normalizationTrace payload.initialNnf
  let strictAudit :=
    (← getOptions).getBool `prove_auto.replay.strictAudit false
  let payloadExpr ← cacheReplayData `_replayPayload <|
    if strictAudit then rawPayloadExprs.payload else toExpr payload
  let search := artifact.toSearchInput label
  let searchExpr ← cacheReplayData `_replaySearch (toExpr search)
  traceRemainingHeartbeats "cached payload and search data"
  let hReplay ←
    if strictAudit then
      strictSourceReplayProof kind sourceProblem refutationSource
        payloadExpr rawPayloadExprs
    else
      let nativePayload := toExpr payload
      let nativeCheck ←
        match kind with
        | .firstOrder =>
            mkAppM ``SourcePreprocessing.FirstOrderReplay.check
              #[toExpr sourceProblemValue, nativePayload]
        | .fool =>
            mkAppM ``SourcePreprocessing.FoolReplay.check
              #[toExpr sourceProblemValue, nativePayload]
      let targetCheck ←
        match kind with
        | .firstOrder =>
            mkAppM ``SourcePreprocessing.FirstOrderReplay.check
              #[sourceProblem, payloadExpr]
        | .fool =>
            mkAppM ``SourcePreprocessing.FoolReplay.check
              #[sourceProblem, payloadExpr]
      nativeBoolTrueProofFor `prove_auto_native_preprocessing
        "preprocessing proof-only quotation" nativeCheck targetCheck
  traceRemainingHeartbeats
    s!"composed preprocessing replay; strictAudit={strictAudit}"
  let replaySearchInput ←
    match kind with
    | .firstOrder =>
        mkAppM ``SourcePreprocessing.FirstOrderReplay.searchInput
          #[payloadExpr, problem, searchExpr, toExpr label]
    | .fool =>
        mkAppM ``SourcePreprocessing.FoolReplay.searchInput
          #[payloadExpr, problem, searchExpr, toExpr label]
  let clauseProblem :=
    match kind with
    | .firstOrder =>
        SourcePreprocessing.FirstOrderReplay.clauseProblemOf payload
    | .fool =>
        SourcePreprocessing.FoolReplay.clauseProblemOf payload
  let materialized ←
    match
      SearchReplayMaterial.materializeRoot?
        clauseProblem search.dag artifact.root.id with
    | Except.ok result =>
        pure result
    | Except.error error =>
        throwError "search DAG materialization failed: {error.label}"
  let afterMaterialization ← getRemainingHeartbeats
  trace[YesMetaZFC.proveAuto.kernelReplay]
    "materialized tightly coupled replay data: \
      nodes={materialized.data.dag.nodes.size}; \
      bytes={materialized.data.arena.size}; \
      remainingHb={afterMaterialization / 1000}"
  let clauseProblemExpr ←
    match kind with
    | .firstOrder =>
        mkAppM ``SourcePreprocessing.FirstOrderReplay.clauseProblemOf
          #[payloadExpr]
    | .fool =>
        mkAppM ``SourcePreprocessing.FoolReplay.clauseProblemOf
          #[payloadExpr]
  let nativeDagValueExpr := toExpr materialized.data.dag
  let nativeArenaValueExpr := toExpr materialized.data.arena
  let (dagExpr, arenaExpr) ←
    if strictAudit then
      let replayProblemExpr ←
        cacheReplayData `_replayProblem (toExpr clauseProblem)
      let nodesExpr ←
        cacheReplayData `_replayNodes (toExpr materialized.data.dag.nodes)
      let rawDagExpr ←
        mkAppM ``DAGCertificate.DAG.mk
          #[replayProblemExpr, toExpr materialized.data.dag.root, nodesExpr]
      let dagExpr ← cacheReplayData `_replayDag rawDagExpr
      let arenaExpr ←
        cacheReplayData `_replayArena (toExpr materialized.data.arena)
      pure (dagExpr, arenaExpr)
    else
      let dagExpr ←
        cacheReplayData `_replayDag nativeDagValueExpr
      let arenaExpr ←
        cacheReplayData `_replayArena nativeArenaValueExpr
      pure (dagExpr, arenaExpr)
  traceRemainingHeartbeats "cached tightly materialized DAG/Arena projections"
  let includeAvatarExpr :=
    toExpr materialized.data.dag.avatarSoundnessSupported
  let arenaCheck ←
    mkAppM ``DAGCertificate.DAG.ReplayArena.checkFor
      #[includeAvatarExpr, dagExpr, arenaExpr]
  let tickets : SourceReplayTickets ←
    if strictAudit then
      let dagProofs ←
        dagContractProof dagExpr materialized.data.dag
          materialized.data.dag.avatarSoundnessSupported
      let layoutCheck ←
        mkAppM ``DAGCertificate.DAG.ReplayArena.layoutCheck
          #[dagExpr, arenaExpr]
      let hLayout ←
        sealedBoolTrueProof layoutCheck
          (← mkEqRefl (mkConst ``Bool.true))
      let checked ←
        mkAppM
          ``DAGCertificate.DAG.ReplayArena.checkFor_eq_true_of_components
          #[includeAvatarExpr, dagExpr, arenaExpr, hLayout,
            dagProofs.rootExists, dagProofs.rootClosed, dagProofs.denseIds,
            dagProofs.parentsBefore, dagProofs.arenaNodes]
      trace[YesMetaZFC.proveAuto.kernelReplay]
        "strict Arena completeness ticket established"
      if materialized.data.dag.avatarSoundnessSupported then
        let registry :=
          DAGCertificate.AvatarSelectorComponent.Registry.build
            materialized.data.dag.avatarSelectorRegistry
        let registryExpr ←
          cacheReplayData `_replayAvatarRegistry (toExpr registry)
        let registryCheck ←
          mkAppM ``DAGCertificate.AvatarSelectorComponent.Registry.check
            #[registryExpr, ← mkAppM
              ``DAGCertificate.DAG.avatarSelectorRegistry #[dagExpr]]
        let hRegistryCheck ←
          boolTrueProof "DAG AVATAR selector registry" registryCheck
        pure (SourceReplayTickets.avatar checked registryExpr hRegistryCheck)
      else if materialized.data.dag.guardedSoundnessSupported then
        let guardedCheck ←
          mkAppM ``DAGCertificate.DAG.guardedSoundnessSupported #[dagExpr]
        let hGuarded ←
          boolTrueProof "search DAG guarded capability" guardedCheck
        pure (SourceReplayTickets.guarded checked hGuarded)
      else
        throwError
          "materialized search DAG is outside all proved soundness fragments"
    else
      let nativeMaterialExpr ←
        mkAppM ``SearchReplayMaterial.Data.mk
          #[nativeDagValueExpr, nativeArenaValueExpr]
      if materialized.data.dag.avatarSoundnessSupported then
        let registry :=
          DAGCertificate.AvatarSelectorComponent.Registry.build
            materialized.data.dag.avatarSelectorRegistry
        let nativeRegistryExpr := toExpr registry
        let registryExpr ←
          cacheReplayData `_replayAvatarRegistry nativeRegistryExpr
        let registryCheck ←
          mkAppM ``DAGCertificate.AvatarSelectorComponent.Registry.check
            #[registryExpr, ← mkAppM
              ``DAGCertificate.DAG.avatarSelectorRegistry #[dagExpr]]
        let nativeCheck ←
          mkAppM ``SearchReplayMaterial.Data.avatarCheck
            #[nativeMaterialExpr, nativeRegistryExpr]
        let targetCheck ← boolAndChain #[arenaCheck, registryCheck]
        let proof ←
          nativeBoolTrueProofFor `prove_auto_native_replay_material
            "tightly coupled AVATAR replay material"
            nativeCheck targetCheck
        let proofs ←
          splitBoolAndTrueProofs #[arenaCheck, registryCheck] proof
        pure
          (SourceReplayTickets.avatar
            proofs[0]! registryExpr proofs[1]!)
      else if materialized.data.dag.guardedSoundnessSupported then
        let guardedCheck ←
          mkAppM ``DAGCertificate.DAG.guardedSoundnessSupported #[dagExpr]
        let nativeCheck ←
          mkAppM ``SearchReplayMaterial.Data.guardedCheck
            #[nativeMaterialExpr]
        let targetCheck ← boolAndChain #[arenaCheck, guardedCheck]
        let proof ←
          nativeBoolTrueProofFor `prove_auto_native_replay_material
            "tightly coupled guarded replay material"
            nativeCheck targetCheck
        let proofs ←
          splitBoolAndTrueProofs #[arenaCheck, guardedCheck] proof
        pure (SourceReplayTickets.guarded proofs[0]! proofs[1]!)
      else
        throwError
          "materialized search DAG is outside all proved soundness fragments"
  let hArenaCheck :=
    match tickets with
    | SourceReplayTickets.avatar arena .. => arena
    | SourceReplayTickets.guarded arena .. => arena
  let arenaContract ←
    mkAppM ``DAGCertificate.DAG.ReplayArena.contract_of_checkFor
      #[hArenaCheck]
  trace[YesMetaZFC.proveAuto.kernelReplay]
    "constructed checked DAG contract from contiguous replay arena; \
      strictAudit={strictAudit}"
  let checkedDag ←
    mkAppM ``DAGCertificate.CheckedDAG.ofContract #[dagExpr, arenaContract]
  let dagProblem ←
    mkAppM ``DAGCertificate.CheckedDAG.problem #[checkedDag]
  let hDagProblem ←
    equalityProof "search DAG problem alignment" dagProblem clauseProblemExpr
  trace[YesMetaZFC.proveAuto.kernelReplay] "checked DAG problem alignment"
  let checkedArtifact ←
    mkAppM ``SearchMaterialization.CheckedArtifact.mk
      #[checkedDag, hDagProblem]
  let nativeCompileCheck :=
    DAGCertificate.Compile.CheckedDAGClauses.compileCheck
      materialized.data.dag
  unless nativeCompileCheck do
    throwError
      "materialized DAG failed intrinsic clause compilation"
  let compileCheck ←
    mkAppM ``DAGCertificate.Compile.CheckedDAGClauses.compileCheck
      #[dagExpr]
  let hCompileCheck ←
    erasableBoolTrueProof `prove_auto_native_dag_clause_compile
      "intrinsic DAG clause compilation"
      (toExpr nativeCompileCheck) compileCheck
  let compiledDAG ←
    mkAppM ``DAGCertificate.Compile.CheckedDAGClauses.ofCompileCheck
      #[hCompileCheck]
  let rawPreparedData ←
    match tickets with
    | SourceReplayTickets.avatar _ registryExpr hRegistryCheck =>
      let hAvatarNodes ←
        mkAppM
          ``DAGCertificate.DAG.ReplayArena.avatarNodesChecked_of_checkFor
          #[hArenaCheck]
      let avatarFields ←
        mkAppM ``DAGCertificate.DAG.LinearReplay.avatar_fields_of_components
          #[hAvatarNodes, hRegistryCheck]
      let hAvatar ← mkAppM ``And.left #[avatarFields]
      let hRegistry ← mkAppM ``And.right #[avatarFields]
      trace[YesMetaZFC.proveAuto.kernelReplay]
        "sealed DAG AVATAR node and registry checks"
        mkAppOptM
        ``SearchReplayMaterial.SearchCertificateProvider.PreparedReplaySearchData.avatar
        #[some replaySearchInput, some checkedArtifact,
          some hAvatar, some registryExpr, some hRegistry, some compiledDAG,
          some compiled]
    | SourceReplayTickets.guarded _ hGuarded =>
      mkAppOptM
        ``SearchReplayMaterial.SearchCertificateProvider.PreparedReplaySearchData.guarded
        #[some replaySearchInput, some checkedArtifact, some hGuarded,
          some compiledDAG, some compiled]
  let preparedData ←
    cacheReplayData `_replayPreparedSearchData rawPreparedData
  trace[YesMetaZFC.proveAuto.kernelReplay]
    "cached prepared replay search data"
  trace[YesMetaZFC.proveAuto.kernelReplay] "finished source replay"
  return {
    payload := payloadExpr
    search := searchExpr
    checked := hReplay
    data := preparedData
  }
def firstOrderReplayExprs
    (sourceProblemValue : SourcePreprocessing.Problem)
    (sourceProblem problem compiled settingsExpr : Expr)
    (payload : SourcePreprocessing.Payload)
    (artifact : SourcePreprocessing.Result.AvatarRunArtifact) (label : String) : MetaM ReplayExprs :=
  sourceReplayExprs .firstOrder
    sourceProblemValue sourceProblem problem compiled settingsExpr
    payload artifact label
def foolReplayExprs
    (sourceProblemValue : SourcePreprocessing.Problem)
    (sourceProblem problem compiled settingsExpr : Expr)
    (payload : SourcePreprocessing.Payload)
    (artifact : SourcePreprocessing.Result.AvatarRunArtifact) (label : String) : MetaM ReplayExprs :=
  sourceReplayExprs .fool
    sourceProblemValue sourceProblem problem compiled settingsExpr
    payload artifact label

end KernelReplay
end Automation
end YesMetaZFC
