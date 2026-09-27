import BMSConstructibleBridge.PowerlessSourceWitnessStep
import BMSConstructibleBridge.PowerlessOmegaRecursion
import BMSConstructibleBridge.PowerlessStagePair

/-!
# 无预设上端点的固定公式见证闭包

按最小推进序数构造真实内部 ω 序列，证明所有值是序数且每步严格增长。
值域之并给出实际极限层，并对指定二元源公式关闭存在见证。
该二元闭包不等于全部公式初等性；公式见证覆盖及无幂集核心仍是明确前提。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceWitnessSequence

open Logic FirstOrder ThirdOrderSemantics PowerlessHierarchyStage

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def sequence_l {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ)) (η : Env ℳ [] Γ)
    (ω e T t₁ t₂ t₃ α f : carrier_l ℳ) : Prop :=
  ∃ S, map_l f ω S ∧ value_l f e α ∧
    (∀ n β, value_l f n β → PowerlessOrdinal.ordinal_l β) ∧
    ∀ n m β γ, member_l ℳ n ω → PowerlessNatural.successor_l n m →
      value_l f n β → value_l f m γ →
        PowerlessSourceWitnessStep.step_l φ η ω e T t₁ t₂ t₃ β γ

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (ω e T t₁ t₂ t₃ : Term ℒ [] Γ .set) (α : carrier_l ℳ)
    (hω : omega_l (ω.eval (PowerlessComprehension.env_l η)))
    (he : PowerlessNatural.zero_l (e.eval (PowerlessComprehension.env_l η)))
    (hα : PowerlessOrdinal.ordinal_l α)
    (hC : ∀ x y,
      φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) → ∃ γ U,
      stage_l (ω.eval (PowerlessComprehension.env_l η)) (e.eval (PowerlessComprehension.env_l η))
        (T.eval (PowerlessComprehension.env_l η)) (t₁.eval (PowerlessComprehension.env_l η))
        (t₂.eval (PowerlessComprehension.env_l η)) (t₃.eval (PowerlessComprehension.env_l η)) γ U ∧
      member_l ℳ y U) :
    ∃ f, sequence_l φ (PowerlessComprehension.env_l η)
      (ω.eval (PowerlessComprehension.env_l η)) (e.eval (PowerlessComprehension.env_l η))
      (T.eval (PowerlessComprehension.env_l η)) (t₁.eval (PowerlessComprehension.env_l η))
      (t₂.eval (PowerlessComprehension.env_l η)) (t₃.eval (PowerlessComprehension.env_l η)) α f := by
  let ρ := PowerlessComprehension.env_l η
  obtain ⟨f, S, hf, hF, h₀⟩ := PowerlessOmegaRecursion.exists_l hℳ
    (PowerlessSourceWitnessStep.select_m φ ω e T t₁ t₂ t₃) η
    (PowerlessSourceWitnessStep.select_exists_l hℳ φ η ω e T t₁ t₂ t₃ hω hC)
    (fun x y z => PowerlessSourceWitnessStep.select_unique_l hℳ φ ρ ω e T t₁ t₂ t₃)
    hω he α
  let ξ : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 1 :=
    { bound := fun _ => f, free := fun _ => f }
  let ψ : Formula ℒ [] [.set, .set] :=
    .forallE .set (.imp (SecondOrderObjectSyntax.value_m (.fvar (.there .here)) (.fvar .here) (.bvar .here))
      (PowerlessOrdinal.ordinal_m (.bvar .here)))
  have hψ : ∀ n, ψ.satisfies ((PowerlessComprehension.env_l ξ).pushFree n) ↔
      ∀ β, value_l f n β → PowerlessOrdinal.ordinal_l β := by
    intro n
    simp only [ψ, Formula.satisfies, value_formula_l, PowerlessOrdinal.ordinal_formula_l hℳ]
    rfl
  have h₁ := PowerlessNatural.induction_l hℳ ψ ξ hω
    (fun z hz => (hψ z).mpr (by
      have h := PowerlessNatural.zero_unique_l hℳ hz he
      subst z
      intro β hβ
      exact (PowerlessFunction.value_unique_l hℳ hf hβ hF).symm ▸ hα))
    (fun n m hn hm h => (hψ m).mpr (by
      intro γ hγ
      obtain ⟨β, hβ, _⟩ := hf.2 n hn
      have hβ₀ := (hψ n).mp h β hβ.2
      obtain ⟨_, A, B, _, hB, _⟩ := PowerlessSourceWitnessStep.selected_step_l hℳ
        φ ρ ω e T t₁ t₂ t₃ hβ₀ (h₀ n m β γ hn hm hβ.2 hγ)
      exact hB.1))
  have h₂ : ∀ n β, value_l f n β → PowerlessOrdinal.ordinal_l β :=
    fun n β hβ => (hψ n).mp (h₁ n (PowerlessFunction.value_mem_l hℳ hf hβ).1) β hβ
  exact ⟨f, S, hf, hF, h₂, fun n m β γ hn hm hβ hγ =>
    PowerlessSourceWitnessStep.selected_step_l hℳ φ ρ ω e T t₁ t₂ t₃
      (h₂ n β hβ) (h₀ n m β γ hn hm hβ hγ)⟩

/-- 真实序列值域之并产生闭包层，不把 ω 序列替换成宿主 Nat 序列。 -/
theorem limit_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Γ)} {η : Env ℳ [] Γ}
    {ω e T t₁ t₂ t₃ α f : carrier_l ℳ} (hω : omega_l ω)
    (h : sequence_l φ η ω e T t₁ t₂ t₃ α f) :
    ∃ δ U, PowerlessStagePair.limit_l δ ∧ member_l ℳ α δ ∧
      stage_l ω e T t₁ t₂ t₃ δ U ∧ ∀ x, member_l ℳ x U →
        (∃ y, φ.satisfies ((η.pushFree x).pushFree y)) →
        ∃ y, member_l ℳ y U ∧ φ.satisfies ((η.pushFree x).pushFree y) := by
  obtain ⟨S, hf, hF, hO, h⟩ := h
  obtain ⟨R, hR⟩ := PowerlessCoordinates.range_exists_l hℳ f
  obtain ⟨δ, hδ, h₀⟩ := PowerlessOrdinalCollection.union_l hℳ (A := R)
    (fun β hβ => by
      obtain ⟨n, hn⟩ := (hR β).mp hβ
      exact hO n β hn)
  have h₁ : ∀ n β, value_l f n β → member_l ℳ β δ := by
    intro n β hβ
    have hn := (PowerlessFunction.value_mem_l hℳ hf hβ).1
    obtain ⟨m, hm⟩ := PowerlessNatural.successor_exists_l hℳ n
    obtain ⟨γ, hγ, _⟩ := hf.2 m (PowerlessNatural.successor_mem_l hℳ hω hn hm)
    exact (h₀ β).mpr ⟨γ, (hR γ).mpr ⟨m, hγ.2⟩, (h n m β γ hn hm hβ hγ.2).1⟩
  have hL : ∀ x, member_l ℳ x δ → ∃ β, member_l ℳ β δ ∧ member_l ℳ x β := by
    intro x hx
    obtain ⟨β, hβ, hx⟩ := (h₀ x).mp hx
    obtain ⟨n, hn⟩ := (hR β).mp hβ
    exact ⟨β, h₁ n β hn, hx⟩
  obtain ⟨U, hU⟩ := PowerlessHierarchyStage.exists_l hℳ hω hδ e T t₁ t₂ t₃
  refine ⟨δ, U, ⟨hδ, ⟨α, h₁ e α hF⟩, hL⟩, h₁ e α hF, hU, ?_⟩
  intro x hx hxφ
  obtain ⟨ξ, V, hξ, hV, hxV⟩ := (PowerlessStageStructure.limit_l hℳ hω hU hL x).mp hx
  obtain ⟨β, hβ, hξβ⟩ := (h₀ ξ).mp hξ
  obtain ⟨n, hnβ⟩ := (hR β).mp hβ
  have hn := (PowerlessFunction.value_mem_l hℳ hf hnβ).1
  obtain ⟨m, hm⟩ := PowerlessNatural.successor_exists_l hℳ n
  obtain ⟨γ, hγ, _⟩ := hf.2 m (PowerlessNatural.successor_mem_l hℳ hω hn hm)
  obtain ⟨_, A, B, hA, hB, h₂⟩ := h n m β γ hn hm hnβ hγ.2
  obtain ⟨y, hy, hyφ⟩ := h₂ x (PowerlessStageStructure.subset_l hℳ hω hV hA hξβ x hxV) hxφ
  exact ⟨y, PowerlessStageStructure.subset_l hℳ hω hB hU (h₁ m γ hγ.2) y hy, hyφ⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceWitnessSequence
