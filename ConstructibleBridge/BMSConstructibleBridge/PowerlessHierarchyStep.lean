import BMSConstructibleBridge.PowerlessEvaluationImage
import BMSConstructibleBridge.PowerlessCoordinates

/-!
# 子集算子在前史值域上的累计并

对任意 H，取所有实际坐标值 B 的算子输出 D，再取这些 D 的并。
纯步骤对任意 H 总唯一；不预设 H 已经是某个层次的函数图。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHierarchyStep

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def step_l (ω e T t₁ t₂ t₃ H Y : carrier_l ℳ) : Prop :=
  ∀ x, member_l ℳ x Y ↔ ∃ a B D, value_l H a B ∧
    PowerlessEvaluationOperator.operator_l ω e T t₁ t₂ t₃ B D ∧ member_l ℳ x D

def step_m {Γ Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ H Y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) :=
    (((t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .forallE .set (.iff (SecondOrderObjectSyntax.member_m (.bvar .here) (Y.weakenBound SetTheory.SetSort.set))
    (.existsE .set (.existsE .set (.existsE .set (.conj
      (SecondOrderObjectSyntax.value_m (w H) (.bvar (.there (.there .here))) (.bvar (.there .here)))
      (.conj (PowerlessEvaluationOperator.operator_m (w ω) (w e) (w T) (w t₁) (w t₂) (w t₃)
        (.bvar (.there .here)) (.bvar .here))
        (SecondOrderObjectSyntax.member_m (.bvar (.there (.there (.there .here)))) (.bvar .here))))))))

theorem step_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ H Y : Term ℒ Γ Δ .set) :
    (step_m ω e T t₁ t₂ t₃ H Y).satisfies η ↔
      step_l (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (H.eval η) (Y.eval η) := by
  simp only [step_m, step_l, Formula.satisfies, value_formula_l,
    PowerlessEvaluationOperator.operator_formula_l hℳ, SecondOrderObjectSyntax.member_m,
    Arguments.eval, Term.eval_weakenBound]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω : carrier_l ℳ} (hω : omega_l ω) (e T t₁ t₂ t₃ H : carrier_l ℳ) :
    ∃ Y, step_l ω e T t₁ t₂ t₃ H Y := by
  obtain ⟨R, hR⟩ := PowerlessCoordinates.range_exists_l hℳ H
  obtain ⟨_, E, _, _, hE⟩ := PowerlessEvaluationImage.exists_l hℳ hω e T t₁ t₂ t₃ R
  obtain ⟨Y, hY⟩ := PowerlessBasic.union_l hℳ E
  refine ⟨Y, fun x => (hY x).trans ?_⟩
  constructor
  · rintro ⟨D, hD, hx⟩
    obtain ⟨B, hB, hD⟩ := (hE D).mp hD
    obtain ⟨a, ha⟩ := (hR B).mp hB
    exact ⟨a, B, D, ha, hD, hx⟩
  · rintro ⟨a, B, D, ha, hD, hx⟩
    exact ⟨D, (hE D).mpr ⟨B, (hR B).mpr ⟨a, ha⟩, hD⟩, hx⟩

theorem unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ H Y Z : carrier_l ℳ}
    (hY : step_l ω e T t₁ t₂ t₃ H Y) (hZ : step_l ω e T t₁ t₂ t₃ H Z) : Y = Z :=
  (PowerlessTheory.ext_l hℳ).eq_of_same_members Y Z (fun x => (hY x).trans (hZ x).symm)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHierarchyStep
