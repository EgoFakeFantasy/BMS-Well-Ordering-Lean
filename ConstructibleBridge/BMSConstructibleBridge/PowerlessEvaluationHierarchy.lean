import BMSConstructibleBridge.PowerlessHierarchyStep
import BMSConstructibleBridge.PowerlessEvaluationHistory

/-!
# 累计求值层次的实际内部序数递归

Cα 是所有 β∈α 的 D(Cβ) 之并。此模块构造内部序数上的唯一集合函数图，
并给出其精确成员方程；尚不把该层次认作经典 L，也不使用宿主序数递归。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationHierarchy

open Logic FirstOrder ThirdOrderSemantics PowerlessHierarchyStep

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def env_l (ω e T t₁ t₂ t₃ : carrier_l ℳ) :
    SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 6 :=
  { bound := Fin.cases ω (Fin.cases e (Fin.cases T (Fin.cases t₁ (Fin.cases t₂ (fun _ => t₃))))),
    free := fun _ => ω }

def operator_m : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] :=
  step_m (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
    (.fvar (.there .here)) (.fvar .here)

theorem operator_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (ω e T t₁ t₂ t₃ H a Y : carrier_l ℳ) :
    PowerlessWellRecursionSyntax.rule_l operator_m (env_l ω e T t₁ t₂ t₃) a H Y ↔
      step_l ω e T t₁ t₂ t₃ H Y := by
  simp only [PowerlessWellRecursionSyntax.rule_l, operator_m, step_formula_l hℳ]
  rfl

def hierarchy_l (ω e T t₁ t₂ t₃ f α : carrier_l ℳ) : Prop :=
  ∃ B, map_l f α B ∧ ∀ a Y, value_l f a Y → ∃ H,
    PowerlessOrdinalRecursion.history_l H f a ∧ step_l ω e T t₁ t₂ t₃ H Y

theorem recursion_iff_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (ω e T t₁ t₂ t₃ f α : carrier_l ℳ) :
    PowerlessOrdinalRecursion.recursion_l operator_m (env_l ω e T t₁ t₂ t₃) f α ↔
      hierarchy_l ω e T t₁ t₂ t₃ f α := by
  apply exists_congr
  intro B
  apply and_congr Iff.rfl
  apply forall_congr'
  intro a
  apply forall_congr'
  intro Y
  apply imp_congr_right
  intro _
  apply exists_congr
  intro H
  exact and_congr Iff.rfl (operator_formula_l hℳ ω e T t₁ t₂ t₃ H a Y)

theorem exists_unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω α : carrier_l ℳ} (hω : omega_l ω) (hα : PowerlessOrdinal.ordinal_l α)
    (e T t₁ t₂ t₃ : carrier_l ℳ) : ∃! f, hierarchy_l ω e T t₁ t₂ t₃ f α := by
  obtain ⟨f, hf, h⟩ := PowerlessOrdinalRecursion.exists_unique_l hℳ operator_m (env_l ω e T t₁ t₂ t₃)
    (fun a H Y Z hY hZ => PowerlessHierarchyStep.unique_l hℳ
      ((operator_formula_l hℳ ω e T t₁ t₂ t₃ H a Y).mp hY)
      ((operator_formula_l hℳ ω e T t₁ t₂ t₃ H a Z).mp hZ)) hα
    (fun a _ H => by
      obtain ⟨Y, hY⟩ := PowerlessHierarchyStep.exists_l hℳ hω e T t₁ t₂ t₃ H
      exact ⟨Y, (operator_formula_l hℳ ω e T t₁ t₂ t₃ H a Y).mpr hY⟩)
  exact ⟨f, (recursion_iff_l hℳ ω e T t₁ t₂ t₃ f α).mp hf,
    fun g hg => h g ((recursion_iff_l hℳ ω e T t₁ t₂ t₃ g α).mpr hg)⟩

theorem equation_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ f α a Y : carrier_l ℳ} (hf : hierarchy_l ω e T t₁ t₂ t₃ f α)
    (hY : value_l f a Y) (x : carrier_l ℳ) :
    member_l ℳ x Y ↔ ∃ b B D, member_l ℳ b a ∧ value_l f b B ∧
      PowerlessEvaluationOperator.operator_l ω e T t₁ t₂ t₃ B D ∧ member_l ℳ x D := by
  obtain ⟨_, _, h⟩ := hf
  obtain ⟨H, hH, h₀⟩ := h a Y hY
  refine (h₀ x).trans ?_
  constructor
  · rintro ⟨b, B, D, hB, hD, hx⟩
    have h₁ := (PowerlessEvaluationHistory.value_l hℳ hH).mp hB
    exact ⟨b, B, D, h₁.2, h₁.1, hD, hx⟩
  · rintro ⟨b, B, D, hb, hB, hD, hx⟩
    exact ⟨b, B, D, (PowerlessEvaluationHistory.value_l hℳ hH).mpr ⟨hB, hb⟩, hD, hx⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationHierarchy
