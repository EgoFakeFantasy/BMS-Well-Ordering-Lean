import YesMetaZFC.Automation.DAGCertificate.AvatarRegistry
import YesMetaZFC.Automation.DAGCertificate.Compile
import YesMetaZFC.Automation.DAGCertificate.CompileDAG
import YesMetaZFC.Automation.DAGCertificate.CompileSubstitution

/-!
# 已检查 DAG 结构

本模块只封装整图结构契约和拓扑归纳。对象逻辑可靠性不再与 DAG 数据结构混写；
后续内在语法编译器与回放器将消费这里的 CheckedDAG。
-/

namespace YesMetaZFC
namespace Automation
namespace DAGCertificate

section DAGCertificateSignature

variable {σ : Signature}
variable [DecidableEq σ.SortSymbol]
variable [DecidableEq σ.FuncSymbol]
variable [DecidableEq σ.RelSymbol]

/-- 已通过整图结构 checker 的 DAG。 -/
structure CheckedDAG where
  private mkInternal ::
  dag : DAG σ
  contract : DAG.Contract dag

namespace CheckedDAG

/-- 已有完整结构契约时直接封装，不重复执行总 checker。 -/
def ofContract (dag : DAG σ) (contract : DAG.Contract dag) :
    CheckedDAG (σ := σ) :=
  ⟨dag, contract⟩

def problem (cert : CheckedDAG (σ := σ)) : ClauseProblem σ :=
  cert.dag.problem

def toComposite (cert : CheckedDAG (σ := σ)) :
    Certificate.Composite :=
  cert.dag.toComposite

theorem topologicalInduction
    (cert : CheckedDAG (σ := σ))
    {P : ∀ index, index < cert.dag.nodes.size → Node σ → Prop}
    (hStep :
      ∀ index (hIndex : index < cert.dag.nodes.size),
        (∀ parent
          (hParent :
            parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
          P parent
            (Nat.lt_trans
              (cert.contract.parents_before index hIndex parent hParent)
              hIndex)
            (cert.dag.nodeAt parent
              (Nat.lt_trans
                (cert.contract.parents_before index hIndex parent hParent)
                hIndex))) →
        P index hIndex (cert.dag.nodeAt index hIndex)) :
    ∀ index (hIndex : index < cert.dag.nodes.size),
      P index hIndex (cert.dag.nodeAt index hIndex) :=
  cert.dag.topologicalInduction cert.contract.parents_before hStep

theorem rootByTopologicalInduction
    (cert : CheckedDAG (σ := σ))
    {P : ∀ index, index < cert.dag.nodes.size → Node σ → Prop}
    (hStep :
      ∀ index (hIndex : index < cert.dag.nodes.size),
        (∀ parent
          (hParent :
            parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
          P parent
            (Nat.lt_trans
              (cert.contract.parents_before index hIndex parent hParent)
              hIndex)
            (cert.dag.nodeAt parent
              (Nat.lt_trans
                (cert.contract.parents_before index hIndex parent hParent)
                hIndex))) →
        P index hIndex (cert.dag.nodeAt index hIndex)) :
    P cert.dag.root cert.contract.root_exists
      (cert.dag.nodeAt cert.dag.root cert.contract.root_exists) :=
  cert.dag.rootByTopologicalInduction cert.contract.root_exists
    cert.contract.parents_before hStep

end CheckedDAG

end DAGCertificateSignature

end DAGCertificate
end Automation
end YesMetaZFC
