import BMSConstructibleBridge.PowerlessEvaluationClause

/-!
# 实际有限赋值上的成员有界量词

界集由更新前赋值读取。传递子域把界集中的见证取回，再对整个实际
更新图收缩值域；此处不需要全初等性或 Skolem 见证闭包。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundedQuantifier

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def exists_l (ω A F f i j b : carrier_l ℳ) : Prop :=
  ∃ n, member_l ℳ n ω ∧ map_l f n A ∧ member_l ℳ i n ∧
    ∃ z, value_l f j z ∧ ∃ a, member_l ℳ a z ∧ ∃ g,
      map_l g n A ∧ PowerlessAssignmentUpdate.update_l f i a g ∧ PowerlessEvaluationClause.query_l F b g

def exists_m {Γ Δ : SortContext ℒ} (ω A F f i j b : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
  let v (t : Term ℒ Γ Δ .set) := (w t).weakenBound SetTheory.SetSort.set
  let q (t : Term ℒ Γ Δ .set) := ((v t).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .existsE .set (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) (w ω))
    (.conj (SecondOrderObjectSyntax.map_m (w f) (.bvar .here) (w A))
      (.conj (SecondOrderObjectSyntax.member_m (w i) (.bvar .here))
        (.existsE .set (.conj (SecondOrderObjectSyntax.value_m (v f) (v j) (.bvar .here))
          (.existsE .set (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there .here)))
            (.existsE .set (.conj
              (SecondOrderObjectSyntax.map_m (.bvar .here) (.bvar (.there (.there (.there .here)))) (q A))
              (.conj (PowerlessAssignmentUpdate.update_m (q f) (q i) (.bvar (.there .here)) (.bvar .here))
                (PowerlessEvaluationClause.query_m (q F) (q b) (.bvar .here))))))))))))

theorem exists_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω A F f i j b : Term ℒ Γ Δ .set) :
    (exists_m ω A F f i j b).satisfies η ↔
      exists_l (ω.eval η) (A.eval η) (F.eval η) (f.eval η) (i.eval η) (j.eval η) (b.eval η) := by
  simp only [exists_m, exists_l, Formula.satisfies, map_formula_l, value_formula_l,
    PowerlessAssignmentUpdate.update_formula_l, PowerlessEvaluationClause.query_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

theorem guard_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {f g n A i j a : carrier_l ℳ} (hg : map_l g n A)
    (h : PowerlessAssignmentUpdate.update_l f i a g) (hij : i ≠ j) :
    PowerlessEvaluationClause.member_l g i j ↔ ∃ z, value_l f j z ∧ member_l ℳ a z := by
  constructor
  · rintro ⟨x, z, hx, hz, h₀⟩
    have h₁ := PowerlessFunction.value_unique_l hℳ hg hx (PowerlessAssignmentUpdate.at_l h)
    exact ⟨z, (PowerlessAssignmentUpdate.away_l h hij.symm).mp hz, h₁ ▸ h₀⟩
  · rintro ⟨z, hz, h₀⟩
    exact ⟨a, z, PowerlessAssignmentUpdate.at_l h, (PowerlessAssignmentUpdate.away_l h hij.symm).mpr hz, h₀⟩

theorem compare_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω A U F G f i j b : carrier_l ℳ} (hAU : subset_l A U)
    (hA : PowerlessNaturalOrder.transitive_l A) (hf : ∃ m, member_l ℳ m ω ∧ map_l f m A)
    (h : ∀ g, (∃ m, member_l ℳ m ω ∧ map_l g m A) →
      (PowerlessEvaluationClause.query_l F b g ↔ PowerlessEvaluationClause.query_l G b g)) :
    exists_l ω U F f i j b ↔ exists_l ω A G f i j b := by
  constructor
  · rintro ⟨n, hn, hf₀, hi, z, hz, a, ha, g, hg, h₀, h₁⟩
    obtain ⟨m, _, hf⟩ := hf
    have h₂ := PowerlessAssignmentUpdate.length_unique_l hℳ hf hf₀
    subst m
    have ha₀ := hA z a (PowerlessFunction.value_mem_l hℳ hf hz).2 ha
    have hg₀ := PowerlessAssignmentUpdate.range_l hℳ hf hg ha₀ h₀
    exact ⟨n, hn, hf, hi, z, hz, a, ha, g, hg₀, h₀, (h g ⟨n, hn, hg₀⟩).mp h₁⟩
  · rintro ⟨n, hn, hf, hi, z, hz, a, ha, g, hg, h₀, h₁⟩
    exact ⟨n, hn, PowerlessFunction.range_l hℳ hf
      (fun _ y hy => hAU y (PowerlessFunction.value_mem_l hℳ hf hy).2), hi, z, hz, a, ha, g,
      PowerlessFunction.range_l hℳ hg (fun _ y hy => hAU y (PowerlessFunction.value_mem_l hℳ hg hy).2),
      h₀, (h g ⟨n, hn, hg⟩).mpr h₁⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundedQuantifier
