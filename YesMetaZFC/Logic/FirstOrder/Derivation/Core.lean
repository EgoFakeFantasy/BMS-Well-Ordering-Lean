import YesMetaZFC.Logic.FirstOrder.Derivation.Substitution.Basic

/-!
# 类型正确的 Hilbert 演绎核

可信推导只有标准逻辑公理、闭理论公理、modus ponens、全称一般化和统一 free 替换。
本层没有 raw 证明树、Bool 检查器、checked 包装、良构参数或 freshness 参数。

局部自然演绎上下文不进入本核；未来证明前端应编译为这里的 Hilbert 推导。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder

universe u v w

/-- 与对象内证明编码保持同形的十二类基础 Hilbert 模式。 -/
inductive HilbertBaseAxiom (σ : Signature.{u, v, w}) :
    {free : SortContext σ} → OpenFormula σ free → Type (max u v w) where
  | implication_distribution {free : SortContext σ}
      (antecedent middle consequent : OpenFormula σ free) :
      HilbertBaseAxiom σ
        (.imp (.imp antecedent (.imp middle consequent))
          (.imp (.imp antecedent middle) (.imp antecedent consequent)))
  | self_implication {free : SortContext σ}
      (formula : OpenFormula σ free) :
      HilbertBaseAxiom σ (.imp formula (.imp formula formula))
  | weakening {free : SortContext σ}
      (formula extra : OpenFormula σ free) :
      HilbertBaseAxiom σ (.imp formula (.imp extra formula))
  | contradiction {free : SortContext σ}
      (formula conclusion : OpenFormula σ free) :
      HilbertBaseAxiom σ
        (.imp formula (.imp (.neg formula) conclusion))
  | classical {free : SortContext σ}
      (formula : OpenFormula σ free) :
      HilbertBaseAxiom σ (.imp (.imp (.neg formula) formula) formula)
  | explosion {free : SortContext σ}
      (formula conclusion : OpenFormula σ free) :
      HilbertBaseAxiom σ
        (.imp (.neg formula) (.imp formula conclusion))
  | case_analysis {free : SortContext σ}
      (formula conclusion : OpenFormula σ free) :
      HilbertBaseAxiom σ
        (.imp (.imp formula conclusion)
          (.imp (.imp (.neg formula) conclusion) conclusion))
  | truth_intro {free : SortContext σ} :
      HilbertBaseAxiom σ (.truth : OpenFormula σ free)
  | falsum_elimination {free : SortContext σ}
      (conclusion : OpenFormula σ free) :
      HilbertBaseAxiom σ (.imp .falsum conclusion)
  | negation_intro {free : SortContext σ}
      (formula : OpenFormula σ free) :
      HilbertBaseAxiom σ (.imp (.imp formula .falsum) (.neg formula))
  | negation_elimination {free : SortContext σ}
      (formula : OpenFormula σ free) :
      HilbertBaseAxiom σ (.imp formula (.imp (.neg formula) .falsum))
  | conjunction_intro {free : SortContext σ}
      (left right : OpenFormula σ free) :
      HilbertBaseAxiom σ
        (.imp left (.imp right (.conj left right)))
  | conjunction_elim_left {free : SortContext σ}
      (left right : OpenFormula σ free) :
      HilbertBaseAxiom σ (.imp (.conj left right) left)
  | conjunction_elim_right {free : SortContext σ}
      (left right : OpenFormula σ free) :
      HilbertBaseAxiom σ (.imp (.conj left right) right)
  | disjunction_intro_left {free : SortContext σ}
      (left right : OpenFormula σ free) :
      HilbertBaseAxiom σ (.imp left (.disj left right))
  | disjunction_intro_right {free : SortContext σ}
      (left right : OpenFormula σ free) :
      HilbertBaseAxiom σ (.imp right (.disj left right))
  | disjunction_elimination {free : SortContext σ}
      (left right conclusion : OpenFormula σ free) :
      HilbertBaseAxiom σ
        (.imp (.imp left conclusion)
          (.imp (.imp right conclusion)
            (.imp (.disj left right) conclusion)))
  | biconditional_intro {free : SortContext σ}
      (left right : OpenFormula σ free) :
      HilbertBaseAxiom σ
        (.imp (.imp left right)
          (.imp (.imp right left) (.iff left right)))
  | biconditional_elim_left {free : SortContext σ}
      (left right : OpenFormula σ free) :
      HilbertBaseAxiom σ (.imp (.iff left right) (.imp left right))
  | biconditional_elim_right {free : SortContext σ}
      (left right : OpenFormula σ free) :
      HilbertBaseAxiom σ (.imp (.iff left right) (.imp right left))
  | forall_specialization {free : SortContext σ}
      (sort : σ.SortSymbol)
      (body : Formula σ [sort] free)
      (term : OpenTerm σ free sort) :
      HilbertBaseAxiom σ
        (.imp (.forallE sort body) (body.instantiateTop term))
  | forall_distribution {free : SortContext σ}
      (sort : σ.SortSymbol)
      (antecedent consequent : OpenFormula σ (sort :: free)) :
      HilbertBaseAxiom σ
        (.imp ((Formula.imp antecedent consequent).forallFreeTop sort)
          (.imp (antecedent.forallFreeTop sort)
            (consequent.forallFreeTop sort)))
  | vacuous_forall {free : SortContext σ}
      (sort : σ.SortSymbol) (formula : OpenFormula σ free) :
      HilbertBaseAxiom σ
        (.imp formula ((formula.weakenFree sort).forallFreeTop sort))
  | exists_introduction {free : SortContext σ}
      (sort : σ.SortSymbol)
      (body : Formula σ [sort] free)
      (term : OpenTerm σ free sort) :
      HilbertBaseAxiom σ
        (.imp (body.instantiateTop term) (.existsE sort body))
  | exists_elimination {free : SortContext σ}
      (sort : σ.SortSymbol)
      (body : OpenFormula σ (sort :: free))
      (conclusion : OpenFormula σ free) :
      HilbertBaseAxiom σ
        (.imp
          ((Formula.imp body (conclusion.weakenFree sort)).forallFreeTop sort)
          (.imp (body.existsFreeTop sort) conclusion))
  | equality_substitution {free : SortContext σ}
      (sort : σ.SortSymbol)
      (left right : OpenTerm σ free sort)
      (body : Formula σ [sort] free) :
      HilbertBaseAxiom σ
        (.imp (.equal left right)
          (.imp (body.instantiateTop left)
            (body.instantiateTop right)))
  | equality_reflexivity {free : SortContext σ}
      {sort : σ.SortSymbol} (term : OpenTerm σ free sort) :
      HilbertBaseAxiom σ (.equal term term)

namespace HilbertBaseAxiom

/-- 沿同一 free 上下文中的公式等式运输基础公理结论。 -/
def castFormula {σ : Signature.{u, v, w}}
    {free : SortContext σ} {left right : OpenFormula σ free}
    (hFormula : left = right)
    (hAxiom : HilbertBaseAxiom σ left) :
    HilbertBaseAxiom σ right := by
  cases hFormula
  exact hAxiom

@[simp] theorem castFormula_rfl {σ : Signature.{u, v, w}}
    {free : SortContext σ} {formula : OpenFormula σ free}
    (hAxiom : HilbertBaseAxiom σ formula) :
    castFormula rfl hAxiom = hAxiom := rfl

end HilbertBaseAxiom

/--
标准有限 Hilbert 推导树。索引保证每个构造子的结论精确匹配规则，不再需要外部
检查器恢复合法性。
-/
inductive HilbertDerivation {σ : Signature.{u, v, w}}
    (T : Theory σ) :
    (free : SortContext σ) → OpenFormula σ free → Type (max u v w) where
  | logical_axiom {free : SortContext σ}
      {formula : OpenFormula σ free} :
      HilbertBaseAxiom σ formula → HilbertDerivation T free formula
  | theory_axiom {free : SortContext σ} {sentence : Sentence σ} :
      T sentence →
        HilbertDerivation T free (Formula.fromSentence sentence)
  | modus_ponens {free : SortContext σ}
      {antecedent consequent : OpenFormula σ free} :
      HilbertDerivation T free antecedent →
      HilbertDerivation T free (.imp antecedent consequent) →
        HilbertDerivation T free consequent
  | forall_generalization {free : SortContext σ} {sort : σ.SortSymbol}
      {formula : OpenFormula σ (sort :: free)} :
      HilbertDerivation T (sort :: free) formula →
        HilbertDerivation T free (formula.forallFreeTop sort)
  | free_strengthening {free : SortContext σ} {sort : σ.SortSymbol}
      {formula : OpenFormula σ free} :
      HilbertDerivation T (sort :: free) (formula.weakenFree sort) →
        HilbertDerivation T free formula
  | free_substitution {sourceFree targetFree : SortContext σ}
      (substitution :
        VariableSubstitution σ sourceFree [] targetFree)
      {formula : OpenFormula σ sourceFree} :
      HilbertDerivation T sourceFree formula →
        HilbertDerivation T targetFree
          (formula.substituteFree substitution)

/-- 核心可证性：存在一棵标准有限、类型正确的 Hilbert 推导树。 -/
def Provable {σ : Signature.{u, v, w}}
    (T : Theory σ) {free : SortContext σ}
    (formula : OpenFormula σ free) : Prop :=
  Nonempty (HilbertDerivation T free formula)

namespace HilbertDerivation

/-- 沿同一 free 上下文中的公式等式运输推导结论。 -/
def castFormula {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {left right : OpenFormula σ free}
    (hFormula : left = right)
    (proof : HilbertDerivation T free left) :
    HilbertDerivation T free right := by
  cases hFormula
  exact proof

@[simp] theorem castFormula_rfl {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {formula : OpenFormula σ free}
    (proof : HilbertDerivation T free formula) :
    castFormula rfl proof = proof := rfl

/-- 沿理论包含关系搬运推导。 -/
def theoryWeakening {σ : Signature.{u, v, w}}
    {T U : Theory σ} {free : SortContext σ}
    {formula : OpenFormula σ free}
    (hTU : Theory.Extends U T) :
    HilbertDerivation T free formula → HilbertDerivation U free formula
  | .logical_axiom hAxiom => .logical_axiom hAxiom
  | .theory_axiom hTheory => .theory_axiom (hTU hTheory)
  | .modus_ponens hAntecedent hImplication =>
      .modus_ponens (hAntecedent.theoryWeakening hTU)
        (hImplication.theoryWeakening hTU)
  | .forall_generalization hFormula =>
      .forall_generalization (hFormula.theoryWeakening hTU)
  | .free_strengthening hFormula =>
      .free_strengthening (hFormula.theoryWeakening hTU)
  | .free_substitution substitution hFormula =>
      .free_substitution substitution (hFormula.theoryWeakening hTU)

/-- 推导树的节点数。 -/
def size {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {formula : OpenFormula σ free} :
    HilbertDerivation T free formula → Nat
  | .logical_axiom _ => 1
  | .theory_axiom _ => 1
  | .modus_ponens hAntecedent hImplication =>
      hAntecedent.size + hImplication.size + 1
  | .forall_generalization hFormula => hFormula.size + 1
  | .free_strengthening hFormula => hFormula.size + 1
  | .free_substitution _ hFormula => hFormula.size + 1

end HilbertDerivation

namespace Provable

/-- 逻辑公理进入公共可推导性。 -/
theorem logical_axiom {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {formula : OpenFormula σ free}
    (hAxiom : HilbertBaseAxiom σ formula) :
    Provable T formula :=
  ⟨.logical_axiom hAxiom⟩

/-- 闭理论公理进入任意 free 上下文。 -/
theorem theory_axiom {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {sentence : Sentence σ} (hTheory : T sentence) :
    Provable T (Formula.fromSentence (free := free) sentence) :=
  ⟨.theory_axiom hTheory⟩

/-- modus ponens。 -/
theorem modus_ponens {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {antecedent consequent : OpenFormula σ free}
    (hAntecedent : Provable T antecedent)
    (hImplication : Provable T (.imp antecedent consequent)) :
    Provable T consequent := by
  rcases hAntecedent with ⟨antecedentProof⟩
  rcases hImplication with ⟨implicationProof⟩
  exact ⟨.modus_ponens antecedentProof implicationProof⟩

/-- 对 free 上下文顶部变量作全称一般化。 -/
theorem forall_generalization {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {formula : OpenFormula σ (sort :: free)}
    (hFormula : Provable T formula) :
    Provable T (formula.forallFreeTop sort) := by
  rcases hFormula with ⟨proof⟩
  exact ⟨.forall_generalization proof⟩

/-- 删除结论中未使用的 free 上下文顶部变量。 -/
theorem free_strengthening {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {formula : OpenFormula σ free}
    (hFormula : Provable T (formula.weakenFree sort)) :
    Provable T formula := by
  rcases hFormula with ⟨proof⟩
  exact ⟨.free_strengthening proof⟩

/-- 对证明结论执行一次类型化的统一 free 替换。 -/
theorem free_substitution {σ : Signature.{u, v, w}}
    {T : Theory σ} {sourceFree targetFree : SortContext σ}
    (substitution :
      VariableSubstitution σ sourceFree [] targetFree)
    {formula : OpenFormula σ sourceFree}
    (hFormula : Provable T formula) :
    Provable T (formula.substituteFree substitution) := by
  rcases hFormula with ⟨proof⟩
  exact ⟨.free_substitution substitution proof⟩

/-- 沿理论包含关系搬运公共可推导性。 -/
theorem theory_weakening {σ : Signature.{u, v, w}}
    {T U : Theory σ} {free : SortContext σ}
    {formula : OpenFormula σ free}
    (hTU : Theory.Extends U T) (hDerives : Provable T formula) :
    Provable U formula := by
  rcases hDerives with ⟨proof⟩
  exact ⟨proof.theoryWeakening hTU⟩

end Provable
end FirstOrder
end Logic
end YesMetaZFC
