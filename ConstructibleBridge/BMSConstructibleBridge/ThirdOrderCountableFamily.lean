import BMSConstructibleBridge.ThirdOrderSelection
import BMSConstructibleBridge.ThirdOrderOmegaOne
import BMSConstructibleBridge.PowerlessProduct

/-!
# 可数集合族的统一单射见证

实际选出每个成员到 ω 的单射，并把并集单射到族与 ω 的笛卡尔积。
这里还没有证明可数乘积可数，因此不把本文件当成 ω₁ 正则性证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderCountableFamily

open Logic FirstOrder ThirdOrderSemantics ThirdOrderOmegaOne

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem exists_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    (ω H : carrier_l ℳ) (h : ∀ A, member_l ℳ A H → countable_l ω A) :
    ∃ F D, map_l F H D ∧ ∀ A f, value_l F A f → map_l f A ω ∧ injective_l f := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 1 :=
    { bound := fun _ => ω, free := fun _ => H }
  let φ : Formula ℒ [] [.set, .set, .set] :=
    .conj (SecondOrderObjectSyntax.map_m (.fvar .here) (.fvar (.there .here))
      (.fvar (.there (.there .here)))) (SecondOrderObjectSyntax.injective_m (.fvar .here))
  have h₀ : ∀ A f, φ.satisfies (((PowerlessComprehension.env_l η).pushFree A).pushFree f) ↔
      map_l f A ω ∧ injective_l f := by
    intro A f
    simp only [φ, Formula.satisfies, map_formula_l, injective_formula_l]
    rfl
  obtain ⟨F, D, hF, h₁⟩ := ThirdOrderSelection.exists_l hℳ φ η H
    (fun A hA => by
      obtain ⟨f, hf⟩ := h A hA
      exact ⟨f, (h₀ A f).mpr hf⟩)
  exact ⟨F, D, hF, fun A f hf => (h₀ A f).mp (h₁ A f hf)⟩

theorem union_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    (ω H : carrier_l ℳ) (h : ∀ A, member_l ℳ A H → countable_l ω A) :
    ∃ U P g, (∀ x, member_l ℳ x U ↔ ∃ A, member_l ℳ A H ∧ member_l ℳ x A) ∧
      PowerlessProduct.product_l H ω P ∧ map_l g U P ∧ injective_l g := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  obtain ⟨F, D, hF, h₁⟩ := exists_l hℳ ω H h
  obtain ⟨U, hU⟩ := PowerlessBasic.union_l h₀ H
  obtain ⟨P, hP⟩ := PowerlessProduct.exists_l h₀ H ω
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 1 :=
    { bound := fun _ => F, free := fun _ => H }
  let φ : Formula ℒ [] [.set, .set, .set] :=
    .existsE .set (.existsE .set (.existsE .set (.conj
      (SecondOrderObjectSyntax.value_m (.fvar (.there (.there .here)))
        (.bvar (.there (.there .here))) (.bvar (.there .here)))
      (.conj (SecondOrderObjectSyntax.value_m (.bvar (.there .here)) (.fvar (.there .here)) (.bvar .here))
        (SecondOrderObjectSyntax.ordered_m (.bvar (.there (.there .here))) (.bvar .here) (.fvar .here))))))
  have h₂ : ∀ x p, φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree p) ↔
      ∃ A f n, value_l F A f ∧ value_l f x n ∧ ordered_l A n p := by
    intro x p
    simp only [φ, Formula.satisfies, value_formula_l, ordered_formula_l]
    rfl
  obtain ⟨g, C, hg, hG⟩ := ThirdOrderSelection.exists_l hℳ φ η U
    (fun x hx => by
      obtain ⟨A, hA, hx⟩ := (hU x).mp hx
      obtain ⟨f, hf, _⟩ := hF.2 A hA
      obtain ⟨n, hn, _⟩ := (h₁ A f hf.2).1.2 x hx
      obtain ⟨p, hp⟩ := PowerlessBasic.ordered_exists_l h₀ A n
      exact ⟨p, (h₂ x p).mpr ⟨A, f, n, hf.2, hn.2, hp⟩⟩)
  have h₃ : ∀ x p, value_l g x p → ∃ A f n, value_l F A f ∧ value_l f x n ∧ ordered_l A n p :=
    fun x p hp => (h₂ x p).mp (hG x p hp)
  refine ⟨U, P, g, hU, hP, PowerlessFunction.range_l h₀ hg ?_, ?_⟩
  · intro x p hp
    obtain ⟨A, f, n, hf, hn, h₄⟩ := h₃ x p hp
    exact (hP p).mpr ⟨A, (PowerlessFunction.value_mem_l h₀ hF hf).1,
      n, (PowerlessFunction.value_mem_l h₀ (h₁ A f hf).1 hn).2, h₄⟩
  · intro x y p hx hy
    obtain ⟨A, f, n, hf, hn, h₄⟩ := h₃ x p hx
    obtain ⟨B, k, m, hk, hm, h₅⟩ := h₃ y p hy
    obtain ⟨h₆, h₇⟩ := (PowerlessBasic.ordered_eq_l h₀ h₄ h₅).mp rfl
    subst B
    subst m
    have h₈ := PowerlessFunction.value_unique_l h₀ hF hf hk
    subst k
    exact (h₁ A f hf).2 x y n hn hm

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderCountableFamily
