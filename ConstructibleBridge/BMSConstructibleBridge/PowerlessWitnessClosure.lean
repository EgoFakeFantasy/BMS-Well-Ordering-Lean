import BMSConstructibleBridge.PowerlessEvaluationWitness

/-!
# 两个参数域之间的存在见证闭包条件

A 上任意内部有限赋值的真实存在请求，在 B 内已有一个见证。
条件以原有纯公式表达，供对象层选择、递归和归纳使用。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessWitnessClosure

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def closure_l (ω U F A B : carrier_l ℳ) : Prop :=
  ∀ i b f, member_l ℳ i ω → member_l ℳ b ω → (∃ n, member_l ℳ n ω ∧ map_l f n A) →
    PowerlessEvaluationClause.exists_l ω U F f i b →
    ∃ a, member_l ℳ a B ∧ PowerlessEvaluationWitness.witness_l ω U F f i b a

def closure_m {Γ Δ : SortContext ℒ} (ω U F A B : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) :=
    ((t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .forallE .set (.forallE .set (.forallE .set (.imp
    (SecondOrderObjectSyntax.member_m (.bvar (.there (.there .here))) (w ω)) (.imp
      (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (w ω)) (.imp
        (.existsE .set (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) ((w ω).weakenBound SetTheory.SetSort.set))
          (SecondOrderObjectSyntax.map_m (.bvar (.there .here)) (.bvar .here) ((w A).weakenBound SetTheory.SetSort.set)))) (.imp
          (PowerlessEvaluationClause.exists_m (w ω) (w U) (w F) (.bvar .here)
            (.bvar (.there (.there .here))) (.bvar (.there .here)))
          (.existsE .set (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) ((w B).weakenBound SetTheory.SetSort.set))
            (PowerlessEvaluationWitness.witness_m ((w ω).weakenBound SetTheory.SetSort.set) ((w U).weakenBound SetTheory.SetSort.set)
              ((w F).weakenBound SetTheory.SetSort.set) (.bvar (.there .here)) (.bvar (.there (.there (.there .here))))
              (.bvar (.there (.there .here))) (.bvar .here))))))))))

theorem closure_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω U F A B : Term ℒ Γ Δ .set) :
    (closure_m ω U F A B).satisfies η ↔ closure_l (ω.eval η) (U.eval η) (F.eval η) (A.eval η) (B.eval η) := by
  simp only [closure_m, closure_l, Formula.satisfies, SecondOrderObjectSyntax.member_m,
    Arguments.eval, map_formula_l, PowerlessEvaluationClause.exists_formula_l,
    PowerlessEvaluationWitness.witness_formula_l, Term.eval_weakenBound]
  rfl

theorem subset_left_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω U F A B C : carrier_l ℳ} (h : closure_l ω U F B C) (hAB : subset_l A B) : closure_l ω U F A C := by
  intro i b f hi hb hf h₀
  obtain ⟨n, hn, hf⟩ := hf
  exact h i b f hi hb ⟨n, hn, PowerlessFunction.range_l hℳ hf
    (fun x a ha => hAB a (PowerlessFunction.value_mem_l hℳ hf ha).2)⟩ h₀

theorem subset_right_l {ω U F A B C : carrier_l ℳ} (h : closure_l ω U F A B) (hBC : subset_l B C) :
    closure_l ω U F A C := by
  intro i b f hi hb hf h₀
  obtain ⟨a, ha, h₁⟩ := h i b f hi hb hf h₀
  exact ⟨a, hBC a ha, h₁⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessWitnessClosure
