import BMSConstructibleBridge.PowerlessEvaluationClause
import BMSConstructibleBridge.PowerlessWellRecursionSyntax

/-!
# 求值真值子集的实际分离算子

对每个内部编号和任意历史 H，从固定赋值集合 S 分离真值子集。
H 不必预先是函数；总唯一性由分离与外延证明，不是新公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationStep

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def step_l (ω e T A t₁ t₂ t₃ S H n Y : carrier_l ℳ) : Prop :=
  ∀ f, member_l ℳ f Y ↔ member_l ℳ f S ∧ PowerlessEvaluationClause.clause_l ω e T A t₁ t₂ t₃ H n f

def step_m {Γ Δ : SortContext ℒ} (ω e T A t₁ t₂ t₃ S H n Y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
  .forallE .set (.iff (SecondOrderObjectSyntax.member_m (.bvar .here) (w Y))
    (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) (w S))
      (PowerlessEvaluationClause.clause_m (w ω) (w e) (w T) (w A) (w t₁) (w t₂) (w t₃) (w H) (w n) (.bvar .here))))

theorem step_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ)
    (ω e T A t₁ t₂ t₃ S H n Y : Term ℒ Γ Δ .set) :
    (step_m ω e T A t₁ t₂ t₃ S H n Y).satisfies η ↔
      step_l (ω.eval η) (e.eval η) (T.eval η) (A.eval η) (t₁.eval η) (t₂.eval η)
        (t₃.eval η) (S.eval η) (H.eval η) (n.eval η) (Y.eval η) := by
  simp only [step_m, step_l, Formula.satisfies, PowerlessEvaluationClause.clause_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

def env_l (ω e T A t₁ t₂ t₃ S : carrier_l ℳ) :
    SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 8 where
  bound := Fin.cases ω (Fin.cases e (Fin.cases T (Fin.cases A
    (Fin.cases t₁ (Fin.cases t₂ (Fin.cases t₃ (fun _ => S)))))))
  free := fun _ => S

def clause_m : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set] :=
  PowerlessEvaluationClause.clause_m
    (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
    (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)

def operator_m : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set] :=
  step_m
    (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
    (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)

theorem operator_formula_l (ω e T A t₁ t₂ t₃ S H n Y : carrier_l ℳ) :
    PowerlessWellRecursionSyntax.rule_l operator_m (env_l ω e T A t₁ t₂ t₃ S) n H Y ↔
      step_l ω e T A t₁ t₂ t₃ S H n Y := by
  simp only [PowerlessWellRecursionSyntax.rule_l, operator_m, step_formula_l]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (ω e T A t₁ t₂ t₃ S H n : carrier_l ℳ) : ∃ Y, step_l ω e T A t₁ t₂ t₃ S H n Y := by
  let η := ((env_l ω e T A t₁ t₂ t₃ S).push n).push H
  have h : ∀ f, clause_m.satisfies ((PowerlessComprehension.env_l η).pushFree f) ↔
      PowerlessEvaluationClause.clause_l ω e T A t₁ t₂ t₃ H n f := by
    intro f
    simp only [clause_m, PowerlessEvaluationClause.clause_formula_l]
    rfl
  obtain ⟨Y, hY⟩ := PowerlessComprehension.separation_l hℳ clause_m η S
  exact ⟨Y, fun f => (hY f).trans (and_congr Iff.rfl (h f))⟩

theorem unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A t₁ t₂ t₃ S H n Y Z : carrier_l ℳ}
    (hY : step_l ω e T A t₁ t₂ t₃ S H n Y) (hZ : step_l ω e T A t₁ t₂ t₃ S H n Z) : Y = Z :=
  (PowerlessTheory.ext_l hℳ).eq_of_same_members Y Z (fun f => (hY f).trans (hZ f).symm)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationStep
