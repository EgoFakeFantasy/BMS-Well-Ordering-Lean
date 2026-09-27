import BMSConstructibleBridge.PowerlessSourceReflection
import BMSConstructibleBridge.PowerlessStageTriangular

/-!
# 实际层次类的基本闭包

共同层、传递性、序数及固定编码参数属于类，和基本集合操作的
闭包均由实际层方程推出。不预设类满足核心、选择或幂集。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassBasic

open Logic FirstOrder ThirdOrderSemantics PowerlessHierarchyStage PowerlessSourceWitnessDomain

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)

include hℳ hω

theorem common_l {a b : carrier_l ℳ}
    (ha : domain_l ω e T t₁ t₂ t₃ a) (hb : domain_l ω e T t₁ t₂ t₃ b) :
    ∃ α U, stage_l ω e T t₁ t₂ t₃ α U ∧ member_l ℳ a U ∧ member_l ℳ b U := by
  let f : Variable (S := (ℒ).SortSymbol) [.set, .set] .set → carrier_l ℳ
    | .here => a
    | .there .here => b
  have hf : ∀ v, domain_l ω e T t₁ t₂ t₃ (f v) := by
    intro v
    match v with
    | .here => exact ha
    | .there .here => exact hb
  obtain ⟨α, U, _, hU, h⟩ := PowerlessSourceReflection.parameters_l hℳ hω
    ω (PowerlessOmegaOrdinal.ordinal_l hℳ hω) [.set, .set] f hf
  exact ⟨α, U, hU, h .here, h (.there .here)⟩

variable (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
  (hT : PowerlessTriangular.triangular_l ω e T)

include ht hT

theorem transitive_l {a x : carrier_l ℳ} (ha : domain_l ω e T t₁ t₂ t₃ a)
    (hx : member_l ℳ x a) : domain_l ω e T t₁ t₂ t₃ x := by
  obtain ⟨α, U, hU, ha⟩ := ha
  exact ⟨α, U, hU, PowerlessStageStructure.transitive_l hℳ hω ht hT hU a x ha hx⟩

theorem stage_member_l {α U : carrier_l ℳ} (hU : stage_l ω e T t₁ t₂ t₃ α U) :
    domain_l ω e T t₁ t₂ t₃ U := by
  obtain ⟨β, hβ⟩ := PowerlessNatural.successor_exists_l hℳ α
  obtain ⟨V, hV⟩ := PowerlessHierarchyStage.exists_l hℳ hω
    (PowerlessOrdinalOrder.successor_l hℳ hU.1 hβ) e T t₁ t₂ t₃
  exact ⟨β, V, hV, PowerlessStageStructure.member_l hℳ hω ht hT hU hV
    ((hβ α).mpr (Or.inr rfl))⟩

theorem ordinal_l {α : carrier_l ℳ} (hα : PowerlessOrdinal.ordinal_l α) :
    domain_l ω e T t₁ t₂ t₃ α := by
  obtain ⟨β, hβ⟩ := PowerlessNatural.successor_exists_l hℳ α
  obtain ⟨U, hU⟩ := PowerlessHierarchyStage.exists_l hℳ hω
    (PowerlessOrdinalOrder.successor_l hℳ hα hβ) e T t₁ t₂ t₃
  exact ⟨β, U, hU, PowerlessStageOrdinal.subset_l hℳ hω ht hT hU α
    ((hβ α).mpr (Or.inr rfl))⟩

theorem parameters_l :
    domain_l ω e T t₁ t₂ t₃ ω ∧ domain_l ω e T t₁ t₂ t₃ e ∧
    domain_l ω e T t₁ t₂ t₃ T ∧ domain_l ω e T t₁ t₂ t₃ t₁ ∧
    domain_l ω e T t₁ t₂ t₃ t₂ ∧ domain_l ω e T t₁ t₂ t₃ t₃ := by
  have hω₀ := ordinal_l hℳ hω ht hT (PowerlessOmegaOrdinal.ordinal_l hℳ hω)
  obtain ⟨he, h₁, h₂, h₃⟩ := PowerlessEvaluationTags.natural_l hℳ hω ht
  obtain ⟨α, β, U, _, _, hU, hTU⟩ := PowerlessStageTriangular.second_l hℳ hω ht hT
  exact ⟨hω₀, transitive_l hℳ hω ht hT hω₀ he, ⟨β, U, hU, hTU⟩,
    transitive_l hℳ hω ht hT hω₀ h₁, transitive_l hℳ hω ht hT hω₀ h₂,
    transitive_l hℳ hω ht hT hω₀ h₃⟩

theorem empty_l {z : carrier_l ℳ} (hz : PowerlessNatural.zero_l z) :
    domain_l ω e T t₁ t₂ t₃ z := by
  have h := (parameters_l hℳ hω ht hT).2.1
  exact (PowerlessNatural.zero_unique_l hℳ ht.1 hz) ▸ h

theorem pair_l {a b p : carrier_l ℳ}
    (ha : domain_l ω e T t₁ t₂ t₃ a) (hb : domain_l ω e T t₁ t₂ t₃ b)
    (hp : ThirdOrderSemantics.pair_l a b p) : domain_l ω e T t₁ t₂ t₃ p := by
  obtain ⟨α, U, hU, ha, hb⟩ := common_l hℳ hω ha hb
  obtain ⟨β, hβ⟩ := PowerlessNatural.successor_exists_l hℳ α
  obtain ⟨V, hV⟩ := PowerlessHierarchyStage.exists_l hℳ hω
    (PowerlessOrdinalOrder.successor_l hℳ hU.1 hβ) e T t₁ t₂ t₃
  exact ⟨β, V, hV, PowerlessOperatorClosure.pair_l hℳ hω ht hT
    (PowerlessStageStructure.successor_l hℳ hω ht hT hU hV hβ) ha hb hp⟩

theorem union_l {a b : carrier_l ℳ} (ha : domain_l ω e T t₁ t₂ t₃ a)
    (hb : ∀ x, member_l ℳ x b ↔ ∃ y, member_l ℳ y a ∧ member_l ℳ x y) :
    domain_l ω e T t₁ t₂ t₃ b := by
  obtain ⟨α, U, hU, ha⟩ := ha
  obtain ⟨β, hβ⟩ := PowerlessNatural.successor_exists_l hℳ α
  obtain ⟨V, hV⟩ := PowerlessHierarchyStage.exists_l hℳ hω
    (PowerlessOrdinalOrder.successor_l hℳ hU.1 hβ) e T t₁ t₂ t₃
  exact ⟨β, V, hV, PowerlessOperatorClosure.union_l hℳ hω ht hT
    (PowerlessStageStructure.successor_l hℳ hω ht hT hU hV hβ)
    (PowerlessStageStructure.transitive_l hℳ hω ht hT hU) ha hb⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassBasic
