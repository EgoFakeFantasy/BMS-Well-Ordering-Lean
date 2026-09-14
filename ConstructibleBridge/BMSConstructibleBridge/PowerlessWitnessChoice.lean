import BMSConstructibleBridge.PowerlessEvaluationWitness

/-!
# 三坐标请求上的总化见证关系

请求 p=((i,b),f)。原存在规则成立时必须返回实际见证；仅在规则不成立
时允许返回缺省元素 d。实际有序对的唯一坐标保证同一请求没有解释歧义。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessWitnessChoice

open Logic FirstOrder ThirdOrderSemantics PowerlessEvaluationWitness

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def choice_l (ω U F d p a : carrier_l ℳ) : Prop :=
  ∃ q f i b, ordered_l q f p ∧ ordered_l i b q ∧
    (witness_l ω U F f i b a ∨ (¬PowerlessEvaluationClause.exists_l ω U F f i b ∧ a = d))

def choice_m {Γ Δ : SortContext ℒ} (ω U F d p a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) :=
    (((t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .existsE .set (.existsE .set (.existsE .set (.existsE .set (.conj
    (SecondOrderObjectSyntax.ordered_m (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here))) (w p))
    (.conj (SecondOrderObjectSyntax.ordered_m (.bvar (.there .here)) (.bvar .here) (.bvar (.there (.there (.there .here)))))
      (.disj (witness_m (w ω) (w U) (w F) (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here) (w a))
        (.conj (.neg (PowerlessEvaluationClause.exists_m (w ω) (w U) (w F)
          (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))) (.equal (w a) (w d)))))))))

theorem choice_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω U F d p a : Term ℒ Γ Δ .set) :
    (choice_m ω U F d p a).satisfies η ↔
      choice_l (ω.eval η) (U.eval η) (F.eval η) (d.eval η) (p.eval η) (a.eval η) := by
  simp only [choice_m, choice_l, Formula.satisfies, ordered_formula_l,
    witness_formula_l, PowerlessEvaluationClause.exists_formula_l, Term.eval_weakenBound]
  rfl

theorem exists_l {ω U F d p q f i b : carrier_l ℳ}
    (hp : ordered_l q f p) (hq : ordered_l i b q) : ∃ a, choice_l ω U F d p a := by
  classical
  by_cases h : PowerlessEvaluationClause.exists_l ω U F f i b
  · obtain ⟨a, ha⟩ := (exists_iff_l ω U F f i b).mp h
    exact ⟨a, q, f, i, b, hp, hq, Or.inl ha⟩
  · exact ⟨d, q, f, i, b, hp, hq, Or.inr ⟨h, rfl⟩⟩

theorem member_l {ω U F d p a : carrier_l ℳ} (hd : ThirdOrderSemantics.member_l ℳ d U)
    (h : choice_l ω U F d p a) : ThirdOrderSemantics.member_l ℳ a U := by
  obtain ⟨_, _, _, _, _, _, h | ⟨_, h⟩⟩ := h
  · exact h.1
  · exact h.symm ▸ hd

theorem witness_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω U F d p a q f i b : carrier_l ℳ} (h : choice_l ω U F d p a)
    (hp : ordered_l q f p) (hq : ordered_l i b q) (h₀ : PowerlessEvaluationClause.exists_l ω U F f i b) :
    PowerlessEvaluationWitness.witness_l ω U F f i b a := by
  obtain ⟨r, g, j, c, hp₀, hq₀, h⟩ := h
  obtain ⟨hr, hg⟩ := (PowerlessBasic.ordered_eq_l hℳ hp₀ hp).mp rfl
  subst r
  subst g
  obtain ⟨hj, hc⟩ := (PowerlessBasic.ordered_eq_l hℳ hq₀ hq).mp rfl
  subst j
  subst c
  exact h.elim id (fun h => (h.1 h₀).elim)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessWitnessChoice
