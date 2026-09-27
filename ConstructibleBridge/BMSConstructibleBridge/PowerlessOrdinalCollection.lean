import BMSConstructibleBridge.PowerlessCollect
import BMSConstructibleBridge.PowerlessOrdinalOrder
import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Closure

/-!
# 固定原公式的序数见证界

从真实分离与收集构造见证集合，再取其序数部分的并及后继。
不需要首个不可数序数、全真值集或已存在的稳定对。
该结果仍使用无幂集核心的 Collection，不宣称裸 Z₂ 已验证该背景。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessOrdinalCollection

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

/-- 只对有见证的输入收集，不假定原关系在输入集合上处处有定义。 -/
theorem partial_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (A : carrier_l ℳ) :
    ∃ B, ∀ x, member_l ℳ x A →
      (∃ y, φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y)) →
      ∃ y, member_l ℳ y B ∧
        φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) := by
  have hφ : ∀ x, (φ.existsFreeTop SetTheory.SetSort.set).satisfies
      ((PowerlessComprehension.env_l η).pushFree x) ↔
        ∃ y, φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) :=
    fun x => Formula.satisfies_existsFreeTop _ _
  obtain ⟨C, hC⟩ := PowerlessComprehension.separation_l hℳ
    (φ.existsFreeTop SetTheory.SetSort.set) η A
  obtain ⟨B, hB⟩ := PowerlessCollect.exists_l hℳ φ η C
    (fun x hx => (hφ x).mp ((hC x).mp hx).2)
  exact ⟨B, fun x hx h => hB x ((hC x).mpr ⟨hx, (hφ x).mpr h⟩)⟩

/-- 任意实际序数集合都有并序数；不预先假定共同序数界。 -/
theorem union_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {A : carrier_l ℳ} (hA : ∀ α, member_l ℳ α A → PowerlessOrdinal.ordinal_l α) :
    ∃ β, PowerlessOrdinal.ordinal_l β ∧
      ∀ x, member_l ℳ x β ↔ ∃ α, member_l ℳ α A ∧ member_l ℳ x α := by
  obtain ⟨β, hβ⟩ := PowerlessBasic.union_l hℳ A
  have h₀ : ∀ x, member_l ℳ x β → PowerlessOrdinal.ordinal_l x := by
    intro x hx
    obtain ⟨α, hα, hx⟩ := (hβ x).mp hx
    exact PowerlessOrdinal.mem_l (hA α hα) hx
  refine ⟨β, PowerlessOrdinal.of_transitive_l hℳ ?_ ?_ ?_, hβ⟩
  · intro x y hx hy
    obtain ⟨α, hα, hx⟩ := (hβ x).mp hx
    exact (hβ y).mpr ⟨α, hα, PowerlessOrdinal.transitive_l (hA α hα) x y hx hy⟩
  · exact fun x hx => PowerlessOrdinal.transitive_l (h₀ x hx)
  · exact fun x y hx hy => PowerlessOrdinalOrder.trichotomy_l hℳ (h₀ x hx) (h₀ y hy)

/-- 并的后继严格容纳所有输入序数，包含空输入集合情形。 -/
theorem bound_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {A : carrier_l ℳ} (hA : ∀ α, member_l ℳ α A → PowerlessOrdinal.ordinal_l α) :
    ∃ β, PowerlessOrdinal.ordinal_l β ∧ ∀ α, member_l ℳ α A → member_l ℳ α β := by
  obtain ⟨γ, hγ, h₀⟩ := union_l hℳ hA
  obtain ⟨β, hβ⟩ := PowerlessNatural.successor_exists_l hℳ γ
  refine ⟨β, PowerlessOrdinalOrder.successor_l hℳ hγ hβ, fun α hα => ?_⟩
  apply (hβ α).mpr
  rcases PowerlessOrdinalOrder.trichotomy_l hℳ (hA α hα) hγ with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · have h₁ := (h₀ γ).mpr ⟨α, hα, h⟩
    exact (PowerlessNatural.asymmetry_l hℳ h₁ h₁).elim

/-- 有定义的原公式序数见证可同时放入一个实际序数；收集上界中的杂项先被分离。 -/
theorem witnesses_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (A : carrier_l ℳ)
    (hφ : ∀ x, member_l ℳ x A → ∀ α,
      φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree α) →
        PowerlessOrdinal.ordinal_l α) :
    ∃ β, PowerlessOrdinal.ordinal_l β ∧ ∀ x, member_l ℳ x A →
      (∃ α, φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree α)) →
      ∃ α, member_l ℳ α β ∧
        φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree α) := by
  obtain ⟨B, hB⟩ := partial_l hℳ φ η A
  let θ : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 0 :=
    { bound := Fin.elim0, free := fun _ => A }
  let ψ : Formula ℒ [] [.set] := PowerlessOrdinal.ordinal_m (.fvar .here)
  have hψ : ∀ α, ψ.satisfies ((PowerlessComprehension.env_l θ).pushFree α) ↔
      PowerlessOrdinal.ordinal_l α := fun α => PowerlessOrdinal.ordinal_formula_l hℳ _ _
  obtain ⟨C, hC⟩ := PowerlessComprehension.separation_l hℳ ψ θ B
  obtain ⟨β, hβ, h₀⟩ := bound_l hℳ
    (fun α hα => (hψ α).mp ((hC α).mp hα).2)
  refine ⟨β, hβ, fun x hx h => ?_⟩
  obtain ⟨α, hα, h₁⟩ := hB x hx h
  exact ⟨α, h₀ α ((hC α).mpr ⟨hα, (hψ α).mpr (hφ x hx α h₁)⟩), h₁⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessOrdinalCollection

