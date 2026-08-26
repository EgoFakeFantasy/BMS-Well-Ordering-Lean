import YesMetaZFC.Logic.FirstOrder.Hilbert
/-!
# Hilbert 演绎的结构与派生规则
本模块从十二类基础模式机械导出后续编译自然演绎所需的公共规则：理论弱化、
蕴含自反与复合、演绎定理，以及满足新鲜条件的全称化。所有规则最终仍只生成
`HilbertProof` 可线性化的逻辑公理、理论行和 modus ponens。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
universe u v w
namespace Theory
/--
Hilbert 意义下的理论扩张。
`strong` 不必逐字包含 `weak`；只要求 `strong` 能证明 `weak` 的每一条公理。
这是理论替换、定义扩张消去以及后续不完备性定理在不同公理化之间搬运证明的公共边界。
-/
def hilbert_extends {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (strong weak : Theory σ) : Prop :=
  ∀ ⦃formula : Formula σ⦄,
    weak formula → Formula.Admissible formula →
      HilbertDerives strong formula
/-- 每个 Hilbert 理论扩张自身。 -/
theorem hilbert_extends_refl {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (theory : Theory σ) :
    Theory.hilbert_extends theory theory := by
  intro formula hTheory
  intro hAdmissible
  exact .theory_axiom hTheory hAdmissible
/-- 理论逐字包含蕴含 Hilbert 意义下的理论扩张。 -/
theorem hilbert_extends_of_subset {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {strong weak : Theory σ} (hSubset : ∀ formula, weak formula → strong formula) :
    Theory.hilbert_extends strong weak := by
  intro formula hTheory
  intro hAdmissible
  exact .theory_axiom (hSubset formula hTheory) hAdmissible
end Theory
namespace HilbertDerives
/-- 基础模式可以直接作为 Hilbert 逻辑公理使用。 -/
theorem base_axiom {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {theory : Theory σ}
    {formula : Formula σ} (hAxiom : HilbertBaseAxiom formula) (hAdmissible : Formula.Admissible formula) :
    HilbertDerives theory formula :=
  .logical_axiom (.base hAxiom) hAdmissible
/--
Hilbert 理论 cut。
若目标理论能证明源理论的每一条公理，则源理论中的整棵推导可以在目标理论中重放。
逻辑公理保持不变，理论公理由 `hExtends` 替换，modus ponens 递归搬运。
-/
theorem theory_cut {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {source target : Theory σ} (hExtends : Theory.hilbert_extends target source)
    {formula : Formula σ} (hDerives : HilbertDerives source formula) :
    HilbertDerives target formula := by
  induction hDerives with
  | logical_axiom hAxiom hAdmissible =>
      exact .logical_axiom hAxiom hAdmissible
  | theory_axiom hTheory hAdmissible =>
      exact hExtends hTheory hAdmissible
  | modus_ponens hAntecedent hImplication ihAntecedent ihImplication =>
      exact .modus_ponens ihAntecedent ihImplication
/-- Hilbert 推导对理论包含关系单调。 -/
theorem theory_weakening {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {theory stronger : Theory σ} (hSubset : ∀ formula, theory formula → stronger formula)
    {formula : Formula σ} (hDerives : HilbertDerives theory formula) :
    HilbertDerives stronger formula :=
  hDerives.theory_cut (Theory.hilbert_extends_of_subset hSubset)
/-- Hilbert 系统中的蕴含自反律。 -/
theorem imp_refl {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {theory : Theory σ} (formula : Formula σ) (hFormula : Formula.Admissible formula) :
    HilbertDerives theory (Formula.imp formula formula) := by
  have hFirst :
      HilbertDerives theory (Formula.imp formula (Formula.imp (Formula.imp formula formula) formula)) :=
    base_axiom (.weakening formula (Formula.imp formula formula)) (Formula.Admissible.imp hFormula (Formula.Admissible.imp
          (Formula.Admissible.imp hFormula hFormula) hFormula))
  have hDistribution :
      HilbertDerives theory (Formula.imp (Formula.imp formula (Formula.imp (Formula.imp formula formula) formula)) (Formula.imp
            (Formula.imp formula (Formula.imp formula formula)) (Formula.imp formula formula))) :=
    base_axiom (.implication_distribution formula (Formula.imp formula formula) formula) (Formula.Admissible.imp (Formula.Admissible.imp hFormula
          (Formula.Admissible.imp (Formula.Admissible.imp hFormula hFormula) hFormula)) (Formula.Admissible.imp (Formula.Admissible.imp hFormula
            (Formula.Admissible.imp hFormula hFormula)) (Formula.Admissible.imp hFormula hFormula)))
  have hStep :
      HilbertDerives theory (Formula.imp (Formula.imp formula (Formula.imp formula formula)) (Formula.imp formula formula)) :=
    .modus_ponens hFirst hDistribution
  have hSecond :
      HilbertDerives theory (Formula.imp formula (Formula.imp formula formula)) :=
    base_axiom (.self_implication formula) (Formula.Admissible.imp hFormula (Formula.Admissible.imp hFormula hFormula))
  exact .modus_ponens hSecond hStep
/-- 已有结论可以忽略一个新的蕴含前件。 -/
theorem imp_weaken {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {theory : Theory σ}
    {formula : Formula σ} (antecedent : Formula σ) (hAntecedent : Formula.Admissible antecedent) (hFormula : HilbertDerives theory formula) :
    HilbertDerives theory (Formula.imp antecedent formula) := by
  have hWeakening :
      HilbertDerives theory (Formula.imp formula (Formula.imp antecedent formula)) :=
    base_axiom (.weakening formula antecedent) (Formula.Admissible.imp hFormula.admissible (Formula.Admissible.imp hAntecedent hFormula.admissible))
  exact .modus_ponens hFormula hWeakening
/-- 两条蕴含可以在 Hilbert 系统中复合。 -/
theorem imp_trans {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {theory : Theory σ}
    {left middle right : Formula σ} (hLeft : HilbertDerives theory (Formula.imp left middle)) (hRight : HilbertDerives theory (Formula.imp middle right)) :
    HilbertDerives theory (Formula.imp left right) := by
  have hLeftAdmissible :=
    Formula.Admissible.imp_left hLeft.admissible
  have hMiddleAdmissible :=
    Formula.Admissible.imp_right hLeft.admissible
  have hRightAdmissible :=
    Formula.Admissible.imp_right hRight.admissible
  have hLifted :
      HilbertDerives theory (Formula.imp left (Formula.imp middle right)) :=
    imp_weaken left hLeftAdmissible hRight
  have hDistribution :
      HilbertDerives theory (Formula.imp (Formula.imp left (Formula.imp middle right)) (Formula.imp (Formula.imp left middle) (Formula.imp left right))) :=
    base_axiom (.implication_distribution left middle right) (Formula.Admissible.imp (Formula.Admissible.imp hLeftAdmissible
          (Formula.Admissible.imp hMiddleAdmissible hRightAdmissible)) (Formula.Admissible.imp (Formula.Admissible.imp hLeftAdmissible hMiddleAdmissible)
          (Formula.Admissible.imp hLeftAdmissible hRightAdmissible)))
  have hStep :
      HilbertDerives theory (Formula.imp (Formula.imp left middle) (Formula.imp left right)) :=
    .modus_ponens hLifted hDistribution
  exact .modus_ponens hLeft hStep
/--
Hilbert 演绎定理。把临时加入理论的一条公式移到结论的蕴含前件；证明只使用
`K`、`S` 两类基础模式，因此可直接线性化为内部证明序列。
-/
theorem deduction {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {theory : Theory σ}
    {antecedent consequent : Formula σ} (hAntecedent : Formula.Admissible antecedent) (hDerives :
      HilbertDerives (Theory.insert antecedent theory) consequent) :
    HilbertDerives theory (Formula.imp antecedent consequent) := by
  induction hDerives with
  | logical_axiom hAxiom hAdmissible =>
      exact imp_weaken antecedent hAntecedent (.logical_axiom hAxiom hAdmissible)
  | @theory_axiom formula hTheory hAdmissible =>
      rcases hTheory with rfl | hTheory
      · exact imp_refl formula hAdmissible
      · exact imp_weaken antecedent hAntecedent (.theory_axiom hTheory hAdmissible)
  | @modus_ponens left right hLeft hImplication ihLeft ihImplication =>
      have hDistribution :
          HilbertDerives theory (Formula.imp (Formula.imp antecedent (Formula.imp left right)) (Formula.imp (Formula.imp antecedent left)
                (Formula.imp antecedent right))) :=
        base_axiom (.implication_distribution antecedent left right) (Formula.Admissible.imp (Formula.Admissible.imp hAntecedent (Formula.Admissible.imp
                hLeft.admissible (Formula.Admissible.imp_right hImplication.admissible))) (Formula.Admissible.imp (Formula.Admissible.imp hAntecedent
                hLeft.admissible) (Formula.Admissible.imp hAntecedent (Formula.Admissible.imp_right
                  hImplication.admissible))))
      exact .modus_ponens ihLeft (.modus_ponens ihImplication hDistribution)
/--
在理论对 `eigen` 新鲜时，Hilbert 推导可以全称化。逻辑公理走全称闭包，理论行走
无关量词引入，MP 分支走全称量词分配。
-/
theorem forall_closure {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {theory : Theory σ} (sort : σ.SortSymbol) (eigen : FreeVarId) (hFresh :
      ∀ formula, theory formula → (sort, eigen) ∉ Formula.freeSupport formula)
    {formula : Formula σ} (hDerives : HilbertDerives theory formula) :
    HilbertDerives theory (Formula.forallE sort (Formula.closeFreeAt sort eigen 0 formula)) := by
  induction hDerives with
  | logical_axiom hAxiom hAdmissible =>
      exact .logical_axiom (.forall_closure sort eigen hAxiom) (Formula.Admissible.forall_closeFreeAt sort eigen hAdmissible)
  | @theory_axiom formula hTheory hAdmissible =>
      have hVacuous :
          HilbertDerives theory (Formula.imp formula (Formula.forallE sort (Formula.closeFreeAt sort eigen 0 formula))) :=
        base_axiom (.vacuous_forall sort eigen formula (hFresh _ hTheory)) (Formula.Admissible.imp hAdmissible (Formula.Admissible.forall_closeFreeAt
              sort eigen hAdmissible))
      exact .modus_ponens (.theory_axiom hTheory hAdmissible) hVacuous
  | @modus_ponens antecedent consequent hAntecedent hImplication
      ihAntecedent ihImplication =>
      let closedAntecedent :=
        Formula.closeFreeAt sort eigen 0 antecedent
      let closedConsequent :=
        Formula.closeFreeAt sort eigen 0 consequent
      have hImplication' :
          HilbertDerives theory (Formula.forallE sort (Formula.imp closedAntecedent closedConsequent)) := by
        simpa [closedAntecedent, closedConsequent,
          Formula.closeFreeAt] using ihImplication
      have hDistribution :
          HilbertDerives theory (Formula.imp (Formula.forallE sort (Formula.imp closedAntecedent closedConsequent)) (Formula.imp
                (Formula.forallE sort closedAntecedent) (Formula.forallE sort closedConsequent))) :=
        base_axiom (.forall_distribution sort
            closedAntecedent closedConsequent) (Formula.Admissible.imp
            ihImplication.admissible (Formula.Admissible.imp
              ihAntecedent.admissible (Formula.Admissible.forall_closeFreeAt
                sort eigen (Formula.Admissible.imp_right
                  hImplication.admissible))))
      have hStep :
          HilbertDerives theory (Formula.imp (Formula.forallE sort closedAntecedent) (Formula.forallE sort closedConsequent)) :=
        .modus_ponens hImplication' hDistribution
      exact .modus_ponens ihAntecedent hStep
/-- 任意 sort 正确且 bound-closed 的项满足 Hilbert 等式自反律。 -/
theorem equality_refl {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {theory : Theory σ}
    {sort : σ.SortSymbol} (term : Term σ) (hTerm : TermWellSorted term sort) (hClosed : Term.BoundClosed term) :
    HilbertDerives theory (Formula.equal term term) := by
  let eigen : FreeVarId := 0
  have hVariable :
      HilbertLogicalAxiom (Formula.equal (Term.var (.fvar sort eigen)) (Term.var (.fvar sort eigen))) :=
    .base (.equality_reflexivity sort eigen)
  have hUniversal :
      HilbertDerives theory (Formula.forallE sort (Formula.closeFreeAt sort eigen 0 (Formula.equal (Term.var (.fvar sort eigen))
              (Term.var (.fvar sort eigen))))) :=
    .logical_axiom (.forall_closure sort eigen hVariable) (Formula.Admissible.forall_closeFreeAt sort eigen
        ⟨.equal (TermWellSorted.fvar sort eigen) (TermWellSorted.fvar sort eigen),
          .equal (TermScoped.fvar sort eigen) (TermScoped.fvar sort eigen)⟩)
  have hSpecialization :
      HilbertDerives theory (Formula.imp (Formula.forallE sort (Formula.closeFreeAt sort eigen 0 (Formula.equal (Term.var (.fvar sort eigen))
                (Term.var (.fvar sort eigen))))) (Formula.openAt sort 0 term (Formula.closeFreeAt sort eigen 0 (Formula.equal (Term.var (.fvar sort eigen))
                (Term.var (.fvar sort eigen)))))) :=
    base_axiom (.forall_specialization sort (Formula.closeFreeAt sort eigen 0 (Formula.equal (Term.var (.fvar sort eigen)) (Term.var (.fvar sort eigen))))
        term hTerm hClosed) (Formula.Admissible.imp hUniversal.admissible (Formula.Admissible.forall_openAt sort
          hUniversal.admissible ⟨hTerm, hClosed⟩))
  simpa [Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.substituteFree, Term.substituteFree] using (HilbertDerives.modus_ponens hUniversal hSpecialization)
end HilbertDerives
namespace Theory
/-- Hilbert 意义下的理论扩张具有传递性。 -/
theorem hilbert_extends_trans {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {strong middle weak : Theory σ} (hStrong : Theory.hilbert_extends strong middle) (hMiddle : Theory.hilbert_extends middle weak) :
    Theory.hilbert_extends strong weak := by
  intro formula hFormula
  intro hAdmissible
  exact (hMiddle hFormula hAdmissible).theory_cut hStrong
/-- 若目标理论分别证明两个理论的公理，则它证明二者联合理论的全部公理。 -/
theorem hilbert_extends_union {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {target left right : Theory σ} (hLeft : Theory.hilbert_extends target left) (hRight : Theory.hilbert_extends target right) :
    Theory.hilbert_extends target (Theory.union left right) := by
  intro formula hFormula
  intro hAdmissible
  rcases hFormula with hFormula | hFormula
  · exact hLeft hFormula hAdmissible
  · exact hRight hFormula hAdmissible
end Theory
end FirstOrder
end Logic
end YesMetaZFC
