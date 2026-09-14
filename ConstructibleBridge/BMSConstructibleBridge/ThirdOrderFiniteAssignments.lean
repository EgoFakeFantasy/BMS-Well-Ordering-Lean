import BMSConstructibleBridge.PowerlessFiniteAssignments
import BMSConstructibleBridge.ThirdOrderCountableUnion
import BMSConstructibleBridge.ThirdOrderCountableImage

/-! # 可数结构的全部内部有限赋值仍可数 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderFiniteAssignments

open Logic FirstOrder ThirdOrderSemantics ThirdOrderOmegaOne PowerlessFiniteAssignments

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem zero_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e A P : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (hP : family_l e A P) : countable_l ω P := by
  obtain ⟨i, hi, hI, _⟩ := PowerlessIdentity.exists_l hℳ ω
  apply ThirdOrderCountableImage.subset_l hℳ ⟨i, hi, hI⟩
  intro f hf
  exact (empty_unique_l hℳ he ((hP f).mp hf)).symm ▸ PowerlessNatural.zero_mem_l hℳ hω he

theorem successor_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω n m A P Q : carrier_l ℳ} (hω : omega_l ω) (hA : countable_l ω A) (hP : family_l n A P)
    (hQ : family_l m A Q) (h : countable_l ω P) (hm : PowerlessNatural.successor_l n m) : countable_l ω Q := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  obtain ⟨D, F, B, hD, hF, h₁, hB⟩ := PowerlessAppendFamily.exists_l h₀ n P A
  have h₂ := ThirdOrderCountableUnion.product_l h₀ hω h hA hD
  have h₃ := ThirdOrderCountableImage.surjective_l hℳ hF h₂ h₁
  apply ThirdOrderCountableImage.subset_l h₀ h₃
  intro g hg
  obtain ⟨f, a, hf, ha, hg⟩ := PowerlessAppendGraph.decompose_l h₀ ((hQ g).mp hg) hm
  exact (hB g).mpr ⟨f, (hP f).mpr hf, a, ha, hg⟩

theorem countable_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω A : carrier_l ℳ} (hω : omega_l ω) (hA : ThirdOrderOmegaOne.countable_l ω A) :
    ∀ n, member_l ℳ n ω → ∀ P, family_l n A P → ThirdOrderOmegaOne.countable_l ω P := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 2 :=
    { bound := Fin.cases A (fun _ => ω), free := fun _ => ω }
  let φ : Formula ℒ [] [.set, .set, .set] := .forallE .set (.imp
    (family_m (.fvar .here) (.fvar (.there .here)) (.bvar .here))
    (ThirdOrderOmegaOne.countable_m (.fvar (.there (.there .here))) (.bvar .here)))
  have h : ∀ n, φ.satisfies ((PowerlessComprehension.env_l η).pushFree n) ↔
      ∀ P, family_l n A P → ThirdOrderOmegaOne.countable_l ω P := by
    intro n
    simp only [φ, Formula.satisfies, family_formula_l, ThirdOrderOmegaOne.countable_formula_l]
    rfl
  have h₁ := PowerlessNatural.induction_l h₀ φ η hω
    (fun e he => (h e).mpr (fun P hP => zero_l h₀ hω he hP))
    (fun n m hn hm h₂ => (h m).mpr (by
      intro Q hQ
      obtain ⟨P, hP⟩ := PowerlessFiniteAssignments.exists_l h₀ hω A n hn
      exact successor_l hℳ hω hA hP hQ ((h n).mp h₂ P hP) hm))
  exact fun n hn => (h n).mp (h₁ n hn)

theorem all_exists_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω A : carrier_l ℳ} (hω : omega_l ω) (hA : ThirdOrderOmegaOne.countable_l ω A) :
    ∃ S, (∀ f, member_l ℳ f S ↔ ∃ n, member_l ℳ n ω ∧ map_l f n A) ∧ ThirdOrderOmegaOne.countable_l ω S := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  obtain ⟨F, B, hF, hB, h₁⟩ := family_graph_l h₀ hω A
  obtain ⟨i, hi, hI, _⟩ := PowerlessIdentity.exists_l h₀ ω
  have h₂ := ThirdOrderCountableImage.surjective_l hℳ hF ⟨i, hi, hI⟩ (by
    intro P hP
    obtain ⟨n, hn, hP⟩ := (hB P).mp hP
    exact ⟨n, (h₁ n hn P).mpr hP⟩)
  obtain ⟨S, hS, h₃⟩ := ThirdOrderCountableUnion.exists_l hℳ hω h₂ (by
    intro P hP
    obtain ⟨n, hn, hP⟩ := (hB P).mp hP
    exact countable_l hℳ hω hA n hn P hP)
  refine ⟨S, fun f => (hS f).trans ?_, h₃⟩
  constructor
  · rintro ⟨P, hP, hf⟩
    obtain ⟨n, hn, hP⟩ := (hB P).mp hP
    exact ⟨n, hn, (hP f).mp hf⟩
  · rintro ⟨n, hn, hf⟩
    obtain ⟨P, hP⟩ := PowerlessFiniteAssignments.exists_l h₀ hω A n hn
    exact ⟨P, (hB P).mpr ⟨n, hn, hP⟩, (hP f).mpr hf⟩

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderFiniteAssignments
