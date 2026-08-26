import YesMetaZFC.Automation.HODAGCertificate
/-!
# 高阶外延见证全局注册表
注册表只从已经存在的 HO-DAG `functionExtensionality` 节点抽取，不接受搜索器额外
声明见证。全局 checker 复核见证符号类型、相对初始问题与先前节点的新鲜性，以及
不同外延步骤之间的符号唯一性。
-/
namespace YesMetaZFC
namespace Automation
namespace HOExtensionalWitnessRegistry
open HODAGCertificate
open Logic.HigherOrder
universe u v w
abbrev Signature := HODAGCertificate.Signature
abbrev SimpleType (σ : Signature) := HODAGCertificate.SimpleType σ
abbrev Term (σ : Signature) := HODAGCertificate.Term σ
abbrev Clause (σ : Signature) := HODAGCertificate.Clause σ
abbrev Node (σ : Signature) := HODAGCertificate.Node σ
abbrev DAG (σ : Signature) := HODAGCertificate.DAG σ
abbrev CheckedDAG (σ : Signature) [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] :=
  HODAGCertificate.CheckedDAG (σ := σ)
abbrev WitnessEvidence (σ : Signature) :=
  HODAGCertificate.FunctionExtensionality.Evidence σ
namespace Syntax
mutual
  def termContainsFunction {σ : Signature.{u, v, w}} [DecidableEq σ.FuncSymbol] (target : σ.FuncSymbol) : Term σ → Bool
    | .var _ => false
    | .app symbol arguments =>
        decide (symbol = target) || termListContainsFunction target arguments
    | .apply function argument =>
        termContainsFunction target function || termContainsFunction target argument
    | .lam _ _ body => termContainsFunction target body
  def termListContainsFunction {σ : Signature.{u, v, w}} [DecidableEq σ.FuncSymbol] (target : σ.FuncSymbol) : List (Term σ) → Bool
    | [] => false
    | term :: rest =>
        termContainsFunction target term || termListContainsFunction target rest
end
def atomContainsFunction {σ : Signature.{u, v, w}} [DecidableEq σ.FuncSymbol] (target : σ.FuncSymbol) : HODAGCertificate.Atom σ → Bool
  | .rel _ arguments => termListContainsFunction target arguments
  | .equal _ left right =>
      termContainsFunction target left || termContainsFunction target right
def literalContainsFunction {σ : Signature.{u, v, w}} [DecidableEq σ.FuncSymbol] (target : σ.FuncSymbol) (literal : HODAGCertificate.Literal σ) : Bool :=
  atomContainsFunction target literal.atom
def clauseContainsFunction {σ : Signature.{u, v, w}} [DecidableEq σ.FuncSymbol] (target : σ.FuncSymbol) (clause : Clause σ) : Bool :=
  clause.literals.any (literalContainsFunction target)
mutual
  def termWitnessFree {σ : Signature.{u, v, w}} : Term σ → Bool
    | .var _ => true
    | .app symbol arguments =>
        !σ.isFunctionExtensionalityWitness symbol &&
          termListWitnessFree arguments
    | .apply function argument =>
        termWitnessFree function && termWitnessFree argument
    | .lam _ _ body =>
        termWitnessFree body
  def termListWitnessFree {σ : Signature.{u, v, w}} : List (Term σ) → Bool
    | [] => true
    | term :: rest =>
        termWitnessFree term && termListWitnessFree rest
end
def atomWitnessFree {σ : Signature.{u, v, w}} : HODAGCertificate.Atom σ → Bool
  | .rel _ arguments =>
      termListWitnessFree arguments
  | .equal _ left right =>
      termWitnessFree left && termWitnessFree right
def literalWitnessFree {σ : Signature.{u, v, w}} (literal : HODAGCertificate.Literal σ) : Bool :=
  atomWitnessFree literal.atom
def clauseWitnessFree {σ : Signature.{u, v, w}} (clause : Clause σ) : Bool :=
  clause.literals.all literalWitnessFree
end Syntax
structure Entry (σ : Signature.{u, v, w}) where
  nodeId : Nat
  evidence : WitnessEvidence σ
namespace Entry
def ofEvidence {σ : Signature.{u, v, w}} (nodeId : Nat) (evidence : WitnessEvidence σ) : Entry σ := {
  nodeId := nodeId
  evidence := evidence
}
def ofNode? {σ : Signature.{u, v, w}} (node : Node σ) : Option (Entry σ) :=
  match node.payload with
  | .functionExtensionality evidence => some (ofEvidence node.id evidence)
  | _ => none
def witnessSymbol {σ : Signature.{u, v, w}} (entry : Entry σ) : σ.FuncSymbol :=
  entry.evidence.witnessSymbol
def domain {σ : Signature.{u, v, w}} (entry : Entry σ) : SimpleType σ :=
  entry.evidence.domain
def codomain {σ : Signature.{u, v, w}} (entry : Entry σ) : SimpleType σ :=
  entry.evidence.codomain
def left {σ : Signature.{u, v, w}} (entry : Entry σ) : Term σ :=
  entry.evidence.left
def right {σ : Signature.{u, v, w}} (entry : Entry σ) : Term σ :=
  entry.evidence.right
def signatureCheck {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort] (entry : Entry σ) : Bool :=
  σ.isFunctionExtensionalityWitness entry.witnessSymbol &&
    decide (σ.funcDomain entry.witnessSymbol =
        [.arrow entry.domain entry.codomain, .arrow entry.domain entry.codomain]) &&
    decide (σ.funcCodomain entry.witnessSymbol = entry.domain)
theorem signatureCheck_sound {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    {entry : Entry σ} (hCheck : entry.signatureCheck = true) :
    σ.isFunctionExtensionalityWitness entry.witnessSymbol = true ∧
      σ.funcDomain entry.witnessSymbol =
        [.arrow entry.domain entry.codomain, .arrow entry.domain entry.codomain] ∧
      σ.funcCodomain entry.witnessSymbol = entry.domain := by
  have hFields : (σ.isFunctionExtensionalityWitness entry.witnessSymbol = true ∧
        σ.funcDomain entry.witnessSymbol =
          [.arrow entry.domain entry.codomain, .arrow entry.domain entry.codomain]) ∧
        σ.funcCodomain entry.witnessSymbol = entry.domain := by
    simpa [signatureCheck] using hCheck
  exact ⟨hFields.1.1, hFields.1.2, hFields.2⟩
def SourceFresh {σ : Signature.{u, v, w}} [DecidableEq σ.FuncSymbol] (problem : HODAGCertificate.Problem σ) (entry : Entry σ) : Prop :=
  ∀ clause, clause ∈ problem.initialClauses.toList →
    Syntax.clauseContainsFunction entry.witnessSymbol clause = false
def sourceFreshCheck {σ : Signature.{u, v, w}} [DecidableEq σ.FuncSymbol] (problem : HODAGCertificate.Problem σ) (entry : Entry σ) : Bool :=
  problem.initialClauses.toList.all fun clause =>
    !Syntax.clauseContainsFunction entry.witnessSymbol clause
theorem sourceFreshCheck_sound {σ : Signature.{u, v, w}}
    [DecidableEq σ.FuncSymbol] {problem : HODAGCertificate.Problem σ}
    {entry : Entry σ} (hCheck : entry.sourceFreshCheck problem = true) :
    entry.SourceFresh problem := by
  intro clause hClause
  have hFresh :=
    List.all_eq_true.mp hCheck clause hClause
  simpa using hFresh
def PriorFresh {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (dag : DAG σ) (entry : Entry σ) : Prop :=
  ∀ node, node ∈ dag.nodes.toList → node.id < entry.nodeId →
    ∃ clause, node.conclusion? dag.problem = some clause ∧
      Syntax.clauseContainsFunction entry.witnessSymbol clause = false
def priorFreshCheck {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (dag : DAG σ) (entry : Entry σ) : Bool :=
  dag.nodes.toList.all fun node =>
    if node.id < entry.nodeId then
      match node.conclusion? dag.problem with
      | some clause => !Syntax.clauseContainsFunction entry.witnessSymbol clause
      | none => false
    else
      true
theorem priorFreshCheck_sound {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {dag : DAG σ} {entry : Entry σ} (hCheck : entry.priorFreshCheck dag = true) :
    entry.PriorFresh dag := by
  intro node hNode hBefore
  have hNodeCheck :=
    List.all_eq_true.mp hCheck node hNode
  rw [if_pos hBefore] at hNodeCheck
  cases hConclusion : node.conclusion? dag.problem with
  | none =>
      simp [hConclusion] at hNodeCheck
  | some clause =>
      refine ⟨clause, rfl, ?_⟩
      simpa [hConclusion] using hNodeCheck
def Fresh {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (dag : DAG σ) (entry : Entry σ) : Prop :=
  entry.SourceFresh dag.problem ∧ entry.PriorFresh dag
def freshCheck {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (dag : DAG σ) (entry : Entry σ) : Bool :=
  entry.sourceFreshCheck dag.problem && entry.priorFreshCheck dag
theorem freshCheck_sound {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {dag : DAG σ} {entry : Entry σ} (hCheck : entry.freshCheck dag = true) :
    entry.Fresh dag := by
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hSource, hPrior⟩
  exact ⟨sourceFreshCheck_sound hSource, priorFreshCheck_sound hPrior⟩
end Entry
structure Registry (σ : Signature.{u, v, w}) where
  entries : List (Entry σ)
namespace Registry
def ofDAG {σ : Signature.{u, v, w}} (dag : DAG σ) : Registry σ := {
  entries := dag.nodes.toList.filterMap Entry.ofNode?
}
end Registry
namespace SourceProblem
def WitnessFree {σ : Signature.{u, v, w}} (problem : HODAGCertificate.Problem σ) : Prop :=
  ∀ (index : Nat) (clause : Clause σ), problem.initialClauses[index]? = some clause →
    Syntax.clauseWitnessFree clause
def witnessFreeCheck {σ : Signature.{u, v, w}} (problem : HODAGCertificate.Problem σ) : Bool :=
  problem.initialClauses.toList.all Syntax.clauseWitnessFree
theorem witnessFreeCheck_sound {σ : Signature.{u, v, w}}
    {problem : HODAGCertificate.Problem σ} (hCheck : SourceProblem.witnessFreeCheck problem = true) :
    SourceProblem.WitnessFree problem := by
  intro index clause hClause
  have hIndex := Array.getElem?_eq_some_iff.mp hClause |>.1
  have hGet := Array.getElem?_eq_some_iff.mp hClause |>.2
  have hMember : clause ∈ problem.initialClauses.toList := by
    simpa [hGet] using Array.getElem_mem hIndex
  exact List.all_eq_true.mp hCheck clause hMember
end SourceProblem
namespace Registry
def PairwiseSymbolUnique {σ : Signature.{u, v, w}} :
    List (Entry σ) → Prop
  | [] => True
  | head :: rest =>
      (∀ other, other ∈ rest → head.witnessSymbol ≠ other.witnessSymbol) ∧
        PairwiseSymbolUnique rest
def pairwiseSymbolUniqueCheck {σ : Signature.{u, v, w}}
    [DecidableEq σ.FuncSymbol] : List (Entry σ) → Bool
  | [] => true
  | head :: rest =>
      (rest.all fun other => decide (head.witnessSymbol ≠ other.witnessSymbol)) &&
        pairwiseSymbolUniqueCheck rest
theorem pairwiseSymbolUniqueCheck_sound {σ : Signature.{u, v, w}}
    [DecidableEq σ.FuncSymbol] {entries : List (Entry σ)} (hCheck : pairwiseSymbolUniqueCheck entries = true) :
    PairwiseSymbolUnique entries := by
  induction entries with
  | nil =>
      trivial
  | cons head rest ih =>
      rcases Bool.and_eq_true_iff.mp hCheck with ⟨hHead, hRest⟩
      constructor
      · intro other hOther
        simpa using List.all_eq_true.mp hHead other hOther
      · exact ih hRest
structure Contract {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (dag : DAG σ) (registry : Registry σ) : Prop where
  sourceWitnessFree : SourceProblem.WitnessFree dag.problem
  signature :
    ∀ entry, entry ∈ registry.entries →
      σ.isFunctionExtensionalityWitness entry.witnessSymbol = true ∧
        σ.funcDomain entry.witnessSymbol =
          [.arrow entry.domain entry.codomain, .arrow entry.domain entry.codomain] ∧
        σ.funcCodomain entry.witnessSymbol = entry.domain
  fresh :
    ∀ entry, entry ∈ registry.entries → entry.Fresh dag
  pairwiseUnique : PairwiseSymbolUnique registry.entries
def check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (dag : DAG σ) (registry : Registry σ) : Bool := (SourceProblem.witnessFreeCheck dag.problem &&
      registry.entries.all fun entry =>
        entry.signatureCheck && entry.freshCheck dag) &&
      pairwiseSymbolUniqueCheck registry.entries
theorem check_sound {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {dag : DAG σ} {registry : Registry σ} (hCheck : registry.check dag = true) :
    Contract dag registry := by
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hEntries, hUnique⟩
  rcases Bool.and_eq_true_iff.mp hEntries with ⟨hSource, hEntries⟩
  refine {
    sourceWitnessFree :=
      SourceProblem.witnessFreeCheck_sound (σ := σ) hSource
    signature := ?_
    fresh := ?_
    pairwiseUnique := pairwiseSymbolUniqueCheck_sound hUnique
  }
  · intro entry hEntry
    have hEntryCheck := List.all_eq_true.mp hEntries entry hEntry
    exact Entry.signatureCheck_sound (Bool.and_eq_true_iff.mp hEntryCheck).1
  · intro entry hEntry
    have hEntryCheck := List.all_eq_true.mp hEntries entry hEntry
    exact Entry.freshCheck_sound (Bool.and_eq_true_iff.mp hEntryCheck).2
end Registry
structure CheckedRegistry {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedDAG σ) where
  registry : Registry σ
  extracted : registry = Registry.ofDAG cert.dag
  checked : registry.check cert.dag = true
namespace CheckedRegistry
def mk? {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG σ) : Option (CheckedRegistry cert) :=
  let registry := Registry.ofDAG cert.dag
  if hCheck : registry.check cert.dag = true then
    some {
      registry := registry
      extracted := rfl
      checked := hCheck
    }
  else
    none
theorem contract {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {cert : CheckedDAG σ} (registry : CheckedRegistry cert) :
    Registry.Contract cert.dag registry.registry :=
  Registry.check_sound registry.checked
end CheckedRegistry
end HOExtensionalWitnessRegistry
end Automation
end YesMetaZFC
