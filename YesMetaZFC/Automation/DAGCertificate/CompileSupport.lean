import YesMetaZFC.Automation.DAGCertificate.Payload

/-!
# DAG replay 的全局自由变量支持集

registry 必须覆盖节点结论之外的替换项、pivot、标准化副本与命题链接。这里集中定义
一次支持集扫描，后续所有 typed 编译阶段共享同一结果。
-/

namespace YesMetaZFC
namespace Automation
namespace DAGCertificate

variable {σ : Signature}

namespace TermSubstitution

def freeSupport (substitution : TermSubstitution σ) :
    List (σ.SortSymbol × Nat) :=
  substitution.flatMap fun entry => entry.2.2.freeSupport

end TermSubstitution

namespace StandardizeApartSideEvidence

def freeSupport (evidence : StandardizeApartSideEvidence σ) :
    List (σ.SortSymbol × Nat) :=
  evidence.original.freeSupport ++ evidence.renamed.freeSupport

end StandardizeApartSideEvidence

namespace StandardizeApartEvidence

def freeSupport (evidence : StandardizeApartEvidence σ) :
    List (σ.SortSymbol × Nat) :=
  evidence.left.freeSupport ++ evidence.right.freeSupport

end StandardizeApartEvidence

namespace TermContext

def freeSupport : TermContext σ → List (σ.SortSymbol × Nat)
  | .hole => []
  | .app _ before context suffix =>
      before.flatMap Term.freeSupport ++ context.freeSupport ++
        suffix.flatMap Term.freeSupport

end TermContext

namespace AtomContext

def freeSupport : AtomContext σ → List (σ.SortSymbol × Nat)
  | .rel _ before context suffix =>
      before.flatMap Term.freeSupport ++ context.freeSupport ++
        suffix.flatMap Term.freeSupport
  | .equalLeft context right =>
      context.freeSupport ++ right.freeSupport
  | .equalRight left context =>
      left.freeSupport ++ context.freeSupport

end AtomContext

namespace ResolutionEvidence

def freeSupport (evidence : ResolutionEvidence σ) :
    List (σ.SortSymbol × Nat) :=
  evidence.left.clause.freeSupport ++ evidence.right.clause.freeSupport ++
    evidence.pivot.freeSupport ++ evidence.substitution.freeSupport ++
      evidence.standardizeApart?.toList.flatMap
        StandardizeApartEvidence.freeSupport

end ResolutionEvidence

namespace FactoringEvidence

def freeSupport (evidence : FactoringEvidence σ) :
    List (σ.SortSymbol × Nat) :=
  evidence.parent.clause.freeSupport ++ evidence.substitution.freeSupport

end FactoringEvidence

namespace EqualityResolutionEvidence

def freeSupport (evidence : EqualityResolutionEvidence σ) :
    List (σ.SortSymbol × Nat) :=
  evidence.parent.clause.freeSupport ++ evidence.left.freeSupport ++
    evidence.right.freeSupport ++ evidence.substitution.freeSupport

end EqualityResolutionEvidence

namespace RewriteEvidence

def freeSupport (evidence : RewriteEvidence σ) :
    List (σ.SortSymbol × Nat) :=
  evidence.equality.clause.freeSupport ++ evidence.target.clause.freeSupport ++
    evidence.substitution.freeSupport ++
      evidence.standardizeApart?.toList.flatMap
        StandardizeApartEvidence.freeSupport ++
        evidence.context.freeSupport ++ evidence.lhs.freeSupport ++
          evidence.rhs.freeSupport

end RewriteEvidence

namespace LocalRuleEvidence

def freeSupport : LocalRuleEvidence σ → List (σ.SortSymbol × Nat)
  | .parentCopy parent => parent.clause.freeSupport
  | .resolution evidence => evidence.freeSupport
  | .factoring evidence => evidence.freeSupport
  | .equalityResolution evidence => evidence.freeSupport
  | .rewrite _ evidence => evidence.freeSupport

end LocalRuleEvidence

namespace PropLiteralLink

def freeSupport (link : PropLiteralLink σ) :
    List (σ.SortSymbol × Nat) :=
  link.object.freeSupport

end PropLiteralLink

namespace PropInitialJustification

def freeSupport : PropInitialJustification σ → List (σ.SortSymbol × Nat)
  | .parentClause link =>
      link.parent.clause.freeSupport ++
        link.literalLinks.toList.flatMap PropLiteralLink.freeSupport
  | .guardActivationClause link =>
      link.parent.clause.freeSupport ++
        link.literalLinks.toList.flatMap PropLiteralLink.freeSupport
  | .propLearnedClause _ => []
  | .avatarSkeleton _ => []

end PropInitialJustification

namespace PropositionalClosurePayload

def freeSupport (payload : PropositionalClosurePayload σ) :
    List (σ.SortSymbol × Nat) :=
  payload.atomMap.toList.flatMap Formula.freeSupport ++
    payload.initialJustifications.toList.flatMap
      PropInitialJustification.freeSupport

end PropositionalClosurePayload

namespace Payload

def freeSupport : Payload σ → List (σ.SortSymbol × Nat)
  | .source _ => []
  | .avatarSplit payload => payload.source.clause.freeSupport
  | .avatarComponent _ => []
  | .localRule payload => payload.evidence.freeSupport
  | .theoryConflict payload => payload.conflict.clause.freeSupport
  | .propositionalLearnedClause _ => []
  | .residualCdcl payload => payload.freeSupport

end Payload

namespace Node

def freeSupport (node : Node σ) : List (σ.SortSymbol × Nat) :=
  node.conclusion.freeSupport ++ node.payload.freeSupport

end Node

namespace DAG

/-- 整张证书唯一的 replay 支持集。 -/
def replaySupport (dag : DAG σ) : List (σ.SortSymbol × Nat) :=
  dag.problem.initialClauses.toList.flatMap Clause.freeSupport ++
    dag.nodes.toList.flatMap Node.freeSupport

/-- 任一实际节点 payload 的自由支持都进入整图 replay 支持集。 -/
theorem mem_replaySupport_of_node_payload
    (dag : DAG σ) (index : Nat) (hIndex : index < dag.nodes.size)
    {entry : σ.SortSymbol × Nat}
    (hEntry : entry ∈ (dag.nodeAt index hIndex).payload.freeSupport) :
    entry ∈ dag.replaySupport := by
  apply List.mem_append_right
  exact List.mem_flatMap.mpr
    ⟨dag.nodeAt index hIndex, Array.getElem_mem_toList hIndex,
      List.mem_append_right _ hEntry⟩

end DAG

end DAGCertificate
end Automation
end YesMetaZFC
