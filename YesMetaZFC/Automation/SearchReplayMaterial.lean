import YesMetaZFC.Automation.SearchMaterialization
import YesMetaZFC.Automation.DAGCertificate.ReplayArena
import YesMetaZFC.Automation.DAGCertificate.CompileDAG

/-!
# 搜索证书的紧耦合回放材料

本层把依赖切片到富 DAG 的翻译与连续 Arena 编码放在同一个拓扑循环中。旧路径需要先
构造完整 DAG，再为格式边界扫描一次节点，最后再扫描一次写 Arena；这里仅预扫轻量
`ClauseInfo` 计算精确容量，富节点一经构造就立刻顺序写入唯一字节块。
-/

namespace YesMetaZFC
namespace Automation
namespace SearchReplayMaterial

open Data.CertificateBlob
open SearchMaterialization
universe x

/-- 可被元层一次 quotation 并由回放端分别投影的唯一数据所有者。 -/
structure Data where
  dag : DAG
  arena : Blob

namespace Data

/-- AVATAR 默认线只报价一次 DAG/Arena，两个 checker 借用同一材料。 -/
@[noinline]
def avatarCheck (data : @& Data)
    (registry :
      @& DAGCertificate.AvatarSelectorComponent.Registry SearchSignature) :
    Bool :=
  DAGCertificate.DAG.ReplayArena.checkFor true data.dag data.arena &&
    DAGCertificate.AvatarSelectorComponent.Registry.check
      registry data.dag.avatarSelectorRegistry

/-- 非 AVATAR guarded 默认线共享同一份 DAG/Arena quotation。 -/
@[noinline]
def guardedCheck (data : @& Data) : Bool :=
  DAGCertificate.DAG.ReplayArena.checkFor false data.dag data.arena &&
    data.dag.guardedSoundnessSupported

end Data

/-- 与 canonical clause problem 对齐的紧耦合材料。 -/
structure Material (problem : ClauseProblem) where
  data : Data
  problem_eq : data.dag.problem = problem

private def encodedBytes (infos : Array ClauseInfo) : Nat :=
  infos.foldl (fun total info =>
    total + DAGCertificate.DAG.ReplayArena.ra_nodeFixedBytes +
      4 * info.parents.size)
    DAGCertificate.DAG.ReplayArena.ra_headerBytes

def materializeRoot? (problem : ClauseProblem) (search : SearchDAG)
    (root : NodeId) : Result (Material problem) := do
  let infos ← checkedDependencySlice? problem search root
  let rootId ← requireSome .dagCheck
    s!"root id {root} is not present in the checked dependency slice" <|
      infos.findIdx? fun info => info.id == root
  let totalBytes := encodedBytes infos
  let mut encoder ← requireSome .dagCheck
    "checked dependency slice exceeds the contiguous Arena format" <|
      DAGCertificate.DAG.ReplayArena.Encoder.start?
        totalBytes infos.size rootId
  let mut state := MaterializationState.emptyWithCapacity infos.size
  for info in infos do
    let materialized ← node problem state info
    encoder := encoder.push materialized
    state := state.push info.id materialized
  let mappedRoot ← requireSome .dagCheck
    s!"root id {root} is not present in tightly coupled material" <|
      state.newId? root
  unless mappedRoot == rootId do
    throw (diagnostic .dagCheck
      s!"tight material root mismatch: expected={rootId}, actual={mappedRoot}")
  let arena ← requireSome .dagCheck
    "contiguous Arena did not consume its exact node/byte budget" <|
      encoder.finish?
  let dag : DAG := {
    problem := problem
    root := rootId
    nodes := state.nodes
  }
  unless DAGCertificate.DAG.ReplayArena.audit dag arena do
    throw (diagnostic .dagCheck
      "tightly coupled DAG/Arena material failed structural/source audit")
  pure {
    data := {
      dag := dag
      arena := arena
    }
    problem_eq := rfl
  }

/-! ## 紧耦合搜索 provider -/

namespace SearchCertificateProvider

structure Input where
  dag : SearchDAG
  root? : Option NodeId := none
  label : String := "search-DAG"
  deriving Repr, Lean.ToExpr

private def formulaListEq : List Formula → List Formula → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      DAGCertificate.StructuralEq.formula left right &&
        formulaListEq leftRest rightRest
  | _, _ => false

private theorem formulaListEq_sound :
    ∀ {left right : List Formula}, formulaListEq left right = true →
      left = right
  | [], [], _ => rfl
  | left :: leftRest, right :: rightRest, h => by
      simp only [formulaListEq, Bool.and_eq_true_iff] at h
      have hHead :=
        DAGCertificate.StructuralEq.formula_sound left right h.1
      have hRest := formulaListEq_sound h.2
      cases hHead
      cases hRest
      rfl
  | [], _ :: _, h => by
      simp [formulaListEq] at h
  | _ :: _, [], h => by
      simp [formulaListEq] at h

def deepProblemEq (left right : DeepProblem) : Bool :=
  formulaListEq left.premises right.premises &&
    DAGCertificate.StructuralEq.formula left.target right.target

theorem deepProblemEq_sound
    {left right : DeepProblem} (h : deepProblemEq left right = true) :
    left = right := by
  rcases Bool.and_eq_true_iff.mp h with ⟨hPremises, hTarget⟩
  have hPremisesEq := formulaListEq_sound hPremises
  have hTargetEq :=
    DAGCertificate.StructuralEq.formula_sound left.target right.target hTarget
  cases left
  cases right
  simp only at hPremisesEq hTargetEq
  cases hPremisesEq
  cases hTargetEq
  rfl

/--
checked replay 使用的纯搜索输入。
它只携带 deep problem、canonical clause problem 与搜索 DAG，不包含 preprocessing
证明或语义 bridge。
-/
structure ReplaySearchInput where
  problem : DeepProblem
  clauseProblem : ClauseProblem
  search? : Option Input := none
  label : String := "replayed search-DAG"

namespace ReplaySearchInput

def unsupportedDiagnostic
    (input : ReplaySearchInput) : Certificate.Diagnostic :=
  diagnostic .clausification
    s!"checked replay for {input.label} did not supply a search DAG/refutation root"

def materializeSearch?
    (input : ReplaySearchInput)
    (unsupported : Certificate.Diagnostic := input.unsupportedDiagnostic) :
    Result (Material input.clauseProblem) :=
  match input.search? with
  | some search => do
      let root ←
        match search.root? with
        | some root => pure root
        | none =>
            requireSome .dagCheck
              "search DAG does not contain an empty-clause root"
              search.dag.emptyClause?
      materializeRoot? input.clauseProblem search.dag root
  | none =>
      throw unsupported

end ReplaySearchInput

/--
预处理后的纯计算输入。
这里故意不携带反模型 bridge，使搜索、材料化和 checker 的成功状态可以独立执行。
-/
structure PreprocessedSearchInput where
  problem : DeepProblem
  clauseProblem : ClauseProblem
  preprocessing : CoreSyntax.NormalForm.CheckedPreprocessing.Checked
  search? : Option Input := none
  label : String := "preprocessed search-DAG"

namespace PreprocessedSearchInput

theorem structuralSound (input : PreprocessedSearchInput) :
    CoreSyntax.NormalForm.CheckedPreprocessing.Sound
      input.preprocessing.payload :=
  CoreSyntax.NormalForm.CheckedPreprocessing.sound input.preprocessing

def toReplaySearchInput
    (input : PreprocessedSearchInput) : ReplaySearchInput := {
  problem := input.problem
  clauseProblem := input.clauseProblem
  search? := input.search?
  label := input.label
}

def unsupportedDiagnostic
    (input : PreprocessedSearchInput) : Certificate.Diagnostic :=
  let stats := input.preprocessing.payload.stats
  diagnostic .clausification
    (s!"checked preprocessing accepted for {input.label} " ++
      s!"(clauses={stats.clauses}, literals={stats.literals}, " ++
      s!"steps={stats.steps}), but no search DAG/refutation root was supplied; " ++
      "structural preprocessing soundness alone is not a semantic backend success")

end PreprocessedSearchInput

inductive PreparedReplaySearchData (input : ReplaySearchInput) where
  | avatar
      (artifact : CheckedArtifact input.clauseProblem)
      (avatarSupported :
        artifact.checked.dag.avatarSoundnessSupported = true)
      (registry :
        DAGCertificate.AvatarSelectorComponent.Registry SearchSignature)
      (registryChecked :
        DAGCertificate.DAG.avatarRegistryCheckWith
          artifact.checked.dag registry = true)
      (compiledDAG :
        DAGCertificate.Compile.CheckedDAGClauses artifact.checked.dag)
      (compiled :
        DAGCertificate.Compile.CheckedProblem input.problem)
  | guarded
      (artifact : CheckedArtifact input.clauseProblem)
      (guardedSupported :
        artifact.checked.dag.guardedSoundnessSupported = true)
      (compiledDAG :
        DAGCertificate.Compile.CheckedDAGClauses artifact.checked.dag)
      (compiled :
        DAGCertificate.Compile.CheckedProblem input.problem)

def prepareReplaySearchData
    (input : ReplaySearchInput)
    (unsupported : Certificate.Diagnostic := input.unsupportedDiagnostic) :
    Result (PreparedReplaySearchData input) := do
  let compiled ← requireSome .dagCheck
    "formula problem cannot be compiled to intrinsic closed syntax"
    (DAGCertificate.Compile.CheckedProblem.compile? input.problem)
  let materialized ← input.materializeSearch? unsupported
  let dag := materialized.data.dag
  let arena := materialized.data.arena
  if hCheck :
      DAGCertificate.DAG.ReplayArena.checkFor
        dag.avatarSoundnessSupported dag arena = true then
    let artifact : CheckedArtifact input.clauseProblem := {
      checked := DAGCertificate.CheckedDAG.ofContract dag <|
        DAGCertificate.DAG.ReplayArena.contract_of_checkFor hCheck
      problem_eq := materialized.problem_eq
    }
    if hAvatarSupported :
        artifact.checked.dag.avatarSoundnessSupported = true then
      let registry :=
        DAGCertificate.AvatarSelectorComponent.Registry.build
          artifact.checked.dag.avatarSelectorRegistry
      if hRegistry :
          DAGCertificate.DAG.avatarRegistryCheckWith
            artifact.checked.dag registry = true then
      match DAGCertificate.Compile.CheckedDAGClauses.compile?
          artifact.checked.dag with
      | none =>
          throw <| diagnostic .dagCheck
            "materialized DAG passed structural checks but failed intrinsic clause compilation"
      | some compiledDAG =>
          pure <|
            .avatar artifact hAvatarSupported registry hRegistry compiledDAG
              compiled
      else
        throw <| diagnostic .dagCheck
          ("materialized AVATAR DAG passed the contiguous Arena checker " ++
            "but failed the global selector registry checker")
    else if hGuardedSupported :
        artifact.checked.dag.guardedSoundnessSupported = true then
      match DAGCertificate.Compile.CheckedDAGClauses.compile?
          artifact.checked.dag with
      | none =>
          throw <| diagnostic .dagCheck
            "materialized DAG passed guarded checks but failed intrinsic clause compilation"
      | some compiledDAG =>
          pure <| .guarded artifact hGuardedSupported compiledDAG compiled
    else
      throw <| diagnostic .dagCheck
        ("materialized preprocessed DAG passed the contiguous Arena checker " ++
          "but contains payloads outside both replay fragments")
  else
    throw <| diagnostic .dagCheck
      s!"materialized DAG/Arena failed checker: {dag.summary}"

abbrev PreparedPreprocessedData (input : PreprocessedSearchInput) :=
  PreparedReplaySearchData input.toReplaySearchInput

def preparePreprocessedData
    (input : PreprocessedSearchInput) :
    Result (PreparedPreprocessedData input) :=
  prepareReplaySearchData
    input.toReplaySearchInput input.unsupportedDiagnostic

def runReplayClosed (input : ReplaySearchInput) : Bool :=
  Scheduler.closed (prepareReplaySearchData input)

def runReplaySummary (input : ReplaySearchInput) : String :=
  Scheduler.summary
    (prepareReplaySearchData input) "DAG Arena reflection: closed"

def runPreprocessedClosedAt
    (input : PreprocessedSearchInput) : Bool :=
  Scheduler.closed (preparePreprocessedData input)

def runPreprocessedSummary
    (input : PreprocessedSearchInput) : String :=
  Scheduler.summary
    (preparePreprocessedData input) "DAG Arena reflection: closed"

end SearchCertificateProvider

end SearchReplayMaterial
end Automation
end YesMetaZFC
