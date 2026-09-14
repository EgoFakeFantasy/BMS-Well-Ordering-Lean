import BMSConstructibleBridge.PowerlessEvaluationClause

/-!
# 存在量词的实际元素与更新图见证

显式给出见证元素，仍保留内部有限域、变量范围、同域更新及子式求值。
与原存在规则精确等价，不引入新的真谓词或省略函数图条件。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationWitness

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def witness_l (ω U F f i b a : carrier_l ℳ) : Prop :=
  member_l ℳ a U ∧ ∃ n, member_l ℳ n ω ∧ map_l f n U ∧ member_l ℳ i n ∧ ∃ g,
    map_l g n U ∧ PowerlessAssignmentUpdate.update_l f i a g ∧ PowerlessEvaluationClause.query_l F b g

def witness_m {Γ Δ : SortContext ℒ} (ω U F f i b a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
  let v (t : Term ℒ Γ Δ .set) := (w t).weakenBound SetTheory.SetSort.set
  .conj (SecondOrderObjectSyntax.member_m a U) (.existsE .set (.conj
    (SecondOrderObjectSyntax.member_m (.bvar .here) (w ω))
    (.conj (SecondOrderObjectSyntax.map_m (w f) (.bvar .here) (w U))
      (.conj (SecondOrderObjectSyntax.member_m (w i) (.bvar .here))
        (.existsE .set (.conj (SecondOrderObjectSyntax.map_m (.bvar .here) (.bvar (.there .here)) (v U))
          (.conj (PowerlessAssignmentUpdate.update_m (v f) (v i) (v a) (.bvar .here))
            (PowerlessEvaluationClause.query_m (v F) (v b) (.bvar .here)))))))))

theorem witness_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω U F f i b a : Term ℒ Γ Δ .set) :
    (witness_m ω U F f i b a).satisfies η ↔
      witness_l (ω.eval η) (U.eval η) (F.eval η) (f.eval η) (i.eval η) (b.eval η) (a.eval η) := by
  simp only [witness_m, witness_l, Formula.satisfies, map_formula_l,
    PowerlessAssignmentUpdate.update_formula_l, PowerlessEvaluationClause.query_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

theorem exists_iff_l (ω U F f i b : carrier_l ℳ) :
    PowerlessEvaluationClause.exists_l ω U F f i b ↔ ∃ a, witness_l ω U F f i b a := by
  constructor
  · rintro ⟨n, hn, hf, hi, a, ha, g, hg, h₀, h₁⟩
    exact ⟨a, ha, n, hn, hf, hi, g, hg, h₀, h₁⟩
  · rintro ⟨a, ha, n, hn, hf, hi, g, hg, h₀, h₁⟩
    exact ⟨n, hn, hf, hi, a, ha, g, hg, h₀, h₁⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationWitness
