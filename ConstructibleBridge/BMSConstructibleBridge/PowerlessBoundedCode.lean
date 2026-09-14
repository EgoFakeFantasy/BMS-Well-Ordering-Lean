import BMSConstructibleBridge.PowerlessBoundedQuantifier
import BMSConstructibleBridge.PowerlessEvaluationEquations

/-!
# 有界存在量词的同一内部数码

由隶属、两次与非及存在构造子组成 ∃ xᵢ∈xⱼ, body。
界槽与更新槽不同；编码只依赖内部自然数与现有配数，不依赖求值域。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundedCode

open Logic FirstOrder ThirdOrderSemantics PowerlessFormulaConstructor

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def code_l (ω e T t₂ t₃ i j b c : carrier_l ℳ) : Prop :=
  i ≠ j ∧ ∃ d p q, constructor_l ω e T e i j d ∧ constructor_l ω e T t₂ d b p ∧
    constructor_l ω e T t₂ p p q ∧ constructor_l ω e T t₃ i q c

def code_m {Γ Δ : SortContext ℒ} (ω e T t₂ t₃ i j b c : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := ((t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .conj (.neg (.equal i j)) (.existsE .set (.existsE .set (.existsE .set
    (.conj (constructor_m (w ω) (w e) (w T) (w e) (w i) (w j) (.bvar (.there (.there .here))))
      (.conj (constructor_m (w ω) (w e) (w T) (w t₂) (.bvar (.there (.there .here))) (w b) (.bvar (.there .here)))
        (.conj (constructor_m (w ω) (w e) (w T) (w t₂) (.bvar (.there .here)) (.bvar (.there .here)) (.bvar .here))
          (constructor_m (w ω) (w e) (w T) (w t₃) (w i) (.bvar .here) (w c))))))))

theorem code_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₂ t₃ i j b c : Term ℒ Γ Δ .set) :
    (code_m ω e T t₂ t₃ i j b c).satisfies η ↔
      code_l (ω.eval η) (e.eval η) (T.eval η) (t₂.eval η) (t₃.eval η) (i.eval η) (j.eval η) (b.eval η) (c.eval η) := by
  simp only [code_m, code_l, Formula.satisfies, constructor_formula_l, Term.eval_weakenBound]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ i j b : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hi : member_l ℳ i ω) (hj : member_l ℳ j ω) (hb : member_l ℳ b ω) (hij : i ≠ j) :
    ∃ c, member_l ℳ c ω ∧ code_l ω e T t₂ t₃ i j b c := by
  obtain ⟨he, _, h₂, h₃⟩ := PowerlessEvaluationTags.natural_l hℳ hω ht
  obtain ⟨d, hd, hD⟩ := PowerlessFormulaConstructor.exists_l hℳ hω ht.1 hT he hi hj
  obtain ⟨p, hp, hP⟩ := PowerlessFormulaConstructor.exists_l hℳ hω ht.1 hT h₂ hd hb
  obtain ⟨q, hq, hQ⟩ := PowerlessFormulaConstructor.exists_l hℳ hω ht.1 hT h₂ hp hp
  obtain ⟨c, hc, hC⟩ := PowerlessFormulaConstructor.exists_l hℳ hω ht.1 hT h₃ hi hq
  exact ⟨c, hc, hij, d, p, q, hD, hP, hQ, hC⟩

theorem unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₂ t₃ i j b c k : carrier_l ℳ} (hω : omega_l ω)
    (he : PowerlessNatural.zero_l e) (hT : PowerlessTriangular.triangular_l ω e T)
    (hc : code_l ω e T t₂ t₃ i j b c) (hk : code_l ω e T t₂ t₃ i j b k) : c = k := by
  obtain ⟨_, d, p, q, hD, hP, hQ, hC⟩ := hc
  obtain ⟨_, a, r, s, hA, hR, hS, hK⟩ := hk
  have h := PowerlessFormulaConstructor.unique_l hℳ hω he hT hD hA
  subst a
  have h := PowerlessFormulaConstructor.unique_l hℳ hω he hT hP hR
  subst r
  have h := PowerlessFormulaConstructor.unique_l hℳ hω he hT hQ hS
  subst s
  exact PowerlessFormulaConstructor.unique_l hℳ hω he hT hC hK

theorem bounds_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₂ t₃ i j b c : carrier_l ℳ} (hω : omega_l ω)
    (he : PowerlessNatural.zero_l e) (hT : PowerlessTriangular.triangular_l ω e T)
    (hc : code_l ω e T t₂ t₃ i j b c) : member_l ℳ i c ∧ member_l ℳ j c ∧ member_l ℳ b c := by
  obtain ⟨_, d, p, q, hD, hP, hQ, hC⟩ := hc
  have h := PowerlessNaturalOrder.member_transitive_l hℳ hω c (PowerlessFormulaConstructor.natural_l hℳ hω he hT hC)
  have h₀ := PowerlessFormulaConstructor.bounds_l hℳ hω he hT hC
  have hp := h q p h₀.2 (PowerlessFormulaConstructor.bounds_l hℳ hω he hT hQ).1
  have h₁ := PowerlessFormulaConstructor.bounds_l hℳ hω he hT hP
  exact ⟨h₀.1, h d j (h p d hp h₁.1) (PowerlessFormulaConstructor.bounds_l hℳ hω he hT hD).2, h p b hp h₁.2⟩

theorem equation_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A t₁ t₂ t₃ S F i j b c : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F)
    (hS : ∀ f, member_l ℳ f S ↔ ∃ n, member_l ℳ n ω ∧ map_l f n A)
    (hc : code_l ω e T t₂ t₃ i j b c) (f : carrier_l ℳ) (hf : member_l ℳ f S) :
    PowerlessEvaluationClause.query_l F c f ↔ PowerlessBoundedQuantifier.exists_l ω A F f i j b := by
  classical
  obtain ⟨hij, d, p, q, hD, hP, hQ, hC⟩ := hc
  have h : ∀ g, member_l ℳ g S → (PowerlessEvaluationClause.query_l F q g ↔
      PowerlessEvaluationClause.member_l g i j ∧ PowerlessEvaluationClause.query_l F b g) := by
    intro g hg
    have h₀ := (PowerlessEvaluationEquations.nand_l hℳ hω ht hT hF hQ g).trans (and_iff_right hg)
    have h₁ := (PowerlessEvaluationEquations.nand_l hℳ hω ht hT hF hP g).trans (and_iff_right hg)
    have h₂ := (PowerlessEvaluationEquations.member_l hℳ hω ht hT hF hD g).trans (and_iff_right hg)
    simpa only [h₁, h₂, and_self, not_not] using h₀
  refine ((PowerlessEvaluationEquations.exists_l hℳ hω ht hT hF hC f).trans (and_iff_right hf)).trans ?_
  constructor
  · rintro ⟨n, hn, hf₀, hi, a, _, g, hg, h₀, h₁⟩
    obtain ⟨h₂, h₃⟩ := (h g ((hS g).mpr ⟨n, hn, hg⟩)).mp h₁
    obtain ⟨z, hz, ha⟩ := (PowerlessBoundedQuantifier.guard_l hℳ hg h₀ hij).mp h₂
    exact ⟨n, hn, hf₀, hi, z, hz, a, ha, g, hg, h₀, h₃⟩
  · rintro ⟨n, hn, hf₀, hi, z, hz, a, ha, g, hg, h₀, h₁⟩
    exact ⟨n, hn, hf₀, hi, a, (PowerlessFunction.value_mem_l hℳ hg (PowerlessAssignmentUpdate.at_l h₀)).2,
      g, hg, h₀, (h g ((hS g).mpr ⟨n, hn, hg⟩)).mpr
        ⟨(PowerlessBoundedQuantifier.guard_l hℳ hg h₀ hij).mpr ⟨z, hz, ha⟩, h₁⟩⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundedCode
