import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ProjectRelationElimination.Transport

/-!
# Project 关系消去的 Hilbert 搬运

本模块把关系展开合同提升到十二类 Hilbert 逻辑公理及整棵证明树。结果理论仍是
源理论的公式像；后续定义插件只需证明这些像公理可由裸理论推出。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProjectRelationElimination

open Nonlogical.BasicSetTheory

set_option autoImplicit false

private abbrev targetSort :=
  YesMetaZFC.SetTheory.SetSort.set

/-- 关系消去逐项保持十二类基础 Hilbert 公理。 -/
theorem base_axiom
    {source : SourceFormula}
    (hSource : HilbertBaseAxiom source) :
    HilbertBaseAxiom (formula source) := by
  cases hSource with
  | implication_distribution antecedent middle consequent =>
      exact .implication_distribution
        (formula antecedent) (formula middle)
        (formula consequent)
  | self_implication source =>
      exact .self_implication (formula source)
  | weakening source extra =>
      exact .weakening (formula source) (formula extra)
  | contradiction source conclusion =>
      exact .contradiction
        (formula source) (formula conclusion)
  | classical source =>
      exact .classical (formula source)
  | explosion source conclusion =>
      exact .explosion
        (formula source) (formula conclusion)
  | case_analysis source conclusion =>
      exact .case_analysis
        (formula source) (formula conclusion)
  | forall_specialization sort body source
      hSorted hClosed =>
      cases sort
      simpa [formula,
        formula_openAt 0 source body hClosed] using
        (HilbertBaseAxiom.forall_specialization
          targetSort (formula body) (term source)
          (term_well_sorted hSorted)
          (term_bound_closed hClosed))
  | forall_distribution sort antecedent consequent =>
      cases sort
      exact .forall_distribution targetSort
        (formula antecedent) (formula consequent)
  | vacuous_forall sort eigen source hFresh =>
      cases sort
      simpa [formula, formula_closeFreeAt] using
        (HilbertBaseAxiom.vacuous_forall
          targetSort (eigen + 1) (formula source)
          (formula_fresh eigen source hFresh))
  | equality_substitution sort leftId rightId body =>
      cases sort
      have hRightClosed :
          Term.BoundClosed
            (Term.var (.fvar SetSort.set rightId) :
              SourceTerm) :=
        TermScoped.fvar
          (σ := SourceSignature)
          SetSort.set rightId
      simpa [formula,
        formula_substituteFree leftId
          (.var (.fvar SetSort.set rightId))
          body hRightClosed] using
        (HilbertBaseAxiom.equality_substitution
          targetSort (leftId + 1) (rightId + 1)
          (formula body))
  | equality_reflexivity sort id =>
      cases sort
      exact HilbertBaseAxiom.equality_reflexivity
        (σ := PureSignature) targetSort (id + 1)

/-- 关系消去保持有限全称闭包后的逻辑公理。 -/
theorem logical_axiom
    {source : SourceFormula}
    (hSource : HilbertLogicalAxiom source) :
    HilbertLogicalAxiom (formula source) := by
  induction hSource with
  | base hBase =>
      exact .base (base_axiom hBase)
  | forall_closure sort eigen hAxiom ih =>
      cases sort
      simpa [formula, formula_closeFreeAt] using
        (HilbertLogicalAxiom.forall_closure
          targetSort (eigen + 1) ih)

/-- 一个中间理论在纯集合论签名中的公式像。 -/
def theory (source : SourceTheory) : PureTheory :=
  fun target =>
    ∃ sourceFormula,
      source sourceFormula ∧
        target = formula sourceFormula

/-- Hilbert 推导可逐树消去当前关系层。 -/
theorem hilbert
    {sourceTheory : SourceTheory}
    {source : SourceFormula}
    (hSource :
      HilbertDerives sourceTheory source) :
    HilbertDerives (theory sourceTheory)
      (formula source) := by
  induction hSource with
  | logical_axiom hAxiom hAdmissible =>
      exact .logical_axiom
        (logical_axiom hAxiom)
        (formula_admissible hAdmissible)
  | theory_axiom hTheory hAdmissible =>
      exact .theory_axiom
        ⟨_, hTheory, rfl⟩
        (formula_admissible hAdmissible)
  | modus_ponens hAntecedent hImplication
      ihAntecedent ihImplication =>
      exact .modus_ponens ihAntecedent <| by
        simpa [formula] using ihImplication

end ProjectRelationElimination
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
