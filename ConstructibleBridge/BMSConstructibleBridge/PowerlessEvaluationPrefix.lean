import BMSConstructibleBridge.PowerlessEvaluationRecursion

/-!
# 原求值算子的初段递归

仅把递归定义域与编码自然数域分开，保留原步骤及原 recursion_m。
长度取 ω 时正是原 evaluation_l；有限长度仍是模型中的集合对象。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationPrefix

open Logic FirstOrder ThirdOrderSemantics PowerlessEvaluationStep

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def prefix_l (ω e T A t₁ t₂ t₃ S F m : carrier_l ℳ) : Prop :=
  ∃ D, map_l F m D ∧ ∀ n Y, value_l F n Y → ∃ H,
    PowerlessOrdinalRecursion.history_l H F n ∧ step_l ω e T A t₁ t₂ t₃ S H n Y

theorem omega_l (ω e T A t₁ t₂ t₃ S F : carrier_l ℳ) :
    prefix_l ω e T A t₁ t₂ t₃ S F ω ↔ PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F := Iff.rfl

theorem recursion_iff_l (ω e T A t₁ t₂ t₃ S F m : carrier_l ℳ) :
    PowerlessOrdinalRecursion.recursion_l operator_m (env_l ω e T A t₁ t₂ t₃ S) F m ↔
      prefix_l ω e T A t₁ t₂ t₃ S F m := by
  apply exists_congr
  intro D
  apply and_congr Iff.rfl
  apply forall_congr'
  intro n
  apply forall_congr'
  intro Y
  apply imp_congr_right
  intro _
  apply exists_congr
  intro H
  exact and_congr Iff.rfl (operator_formula_l ω e T A t₁ t₂ t₃ S H n Y)

def prefix_m {Γ Δ : SortContext ℒ} (ω e T A t₁ t₂ t₃ S F m : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let σ : Substitution ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set] Γ Δ :=
    .map (fun v => nomatch v) (fun {s} v => match s, v with
      | .set, .here => F
      | .set, .there .here => m
      | .set, .there (.there .here) => ω
      | .set, .there (.there (.there .here)) => e
      | .set, .there (.there (.there (.there .here))) => T
      | .set, .there (.there (.there (.there (.there .here)))) => A
      | .set, .there (.there (.there (.there (.there (.there .here))))) => t₁
      | .set, .there (.there (.there (.there (.there (.there (.there .here)))))) => t₂
      | .set, .there (.there (.there (.there (.there (.there (.there (.there .here))))))) => t₃
      | .set, .there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) => S)
  (PowerlessOrdinalRecursion.recursion_m operator_m).substitute σ

theorem presentation_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ)
    (ω e T A t₁ t₂ t₃ S F m : Term ℒ Γ Δ .set) :
    (prefix_m ω e T A t₁ t₂ t₃ S F m).satisfies η ↔
      (PowerlessOrdinalRecursion.recursion_m operator_m).satisfies
        (((PowerlessComprehension.env_l (env_l (ω.eval η) (e.eval η) (T.eval η) (A.eval η)
          (t₁.eval η) (t₂.eval η) (t₃.eval η) (S.eval η))).pushFree (m.eval η)).pushFree (F.eval η)) := by
  simp only [prefix_m, Formula.satisfies_substitute]
  apply Iff.of_eq
  apply congrArg (fun η => (PowerlessOrdinalRecursion.recursion_m operator_m).satisfies η)
  apply Env.ext (bound := []) (fun {_} v => nomatch v)
  · intro s v
    match s, v with
    | .set, .here => rfl
    | .set, .there .here => rfl
    | .set, .there (.there .here) => rfl
    | .set, .there (.there (.there .here)) => rfl
    | .set, .there (.there (.there (.there .here))) => rfl
    | .set, .there (.there (.there (.there (.there .here)))) => rfl
    | .set, .there (.there (.there (.there (.there (.there .here))))) => rfl
    | .set, .there (.there (.there (.there (.there (.there (.there .here)))))) => rfl
    | .set, .there (.there (.there (.there (.there (.there (.there (.there .here))))))) => rfl
    | .set, .there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) => rfl

theorem prefix_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T A t₁ t₂ t₃ S F m : Term ℒ Γ Δ .set) :
    (prefix_m ω e T A t₁ t₂ t₃ S F m).satisfies η ↔
      prefix_l (ω.eval η) (e.eval η) (T.eval η) (A.eval η) (t₁.eval η) (t₂.eval η)
        (t₃.eval η) (S.eval η) (F.eval η) (m.eval η) :=
  (presentation_l η ω e T A t₁ t₂ t₃ S F m).trans
    ((PowerlessOrdinalRecursion.recursion_formula_l hℳ operator_m _ _ _).trans (recursion_iff_l _ _ _ _ _ _ _ _ _ _))

theorem exists_unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A t₁ t₂ t₃ S m : carrier_l ℳ} (hm : PowerlessOrdinal.ordinal_l m) :
    ∃! F, prefix_l ω e T A t₁ t₂ t₃ S F m := by
  obtain ⟨F, hF, h⟩ := PowerlessOrdinalRecursion.exists_unique_l hℳ operator_m (env_l ω e T A t₁ t₂ t₃ S)
    (fun n H Y Z hY hZ => PowerlessEvaluationStep.unique_l hℳ
      ((operator_formula_l ω e T A t₁ t₂ t₃ S H n Y).mp hY)
      ((operator_formula_l ω e T A t₁ t₂ t₃ S H n Z).mp hZ)) hm
    (fun n _ H => by
      obtain ⟨Y, hY⟩ := PowerlessEvaluationStep.exists_l hℳ ω e T A t₁ t₂ t₃ S H n
      exact ⟨Y, (operator_formula_l ω e T A t₁ t₂ t₃ S H n Y).mpr hY⟩)
  exact ⟨F, (recursion_iff_l _ _ _ _ _ _ _ _ _ _).mp hF,
    fun G hG => h G ((recursion_iff_l _ _ _ _ _ _ _ _ _ _).mpr hG)⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationPrefix
