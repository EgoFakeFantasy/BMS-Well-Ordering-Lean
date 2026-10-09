import BMSConstructibleBridge.PowerlessSatisfactionSpecificationBounded

/-! # 完整 Sat 有界检查器的原 Z₂ 等价模式

对象语言为纯隶属 ℒ，背景为原 Z₂；数值序列、实际三角图与母集赋值
集的规格作为对象守卫保留。结论是完整原 Sat 规格与纯 Δ₀ 检查器的
等价，不是 Sat 存在或共同层界。最终出口消费原 GraphTranslation
及已核验的原推导核，不新增对象公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSatisfactionSpecificationBoundedDerives

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderObjectSyntax (member_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def schema_m {Δ : SortContext ℒ} (ω A e N T S t₁ t₂ t₃ F R : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .imp (.forallE .set (.neg (member_m (.bvar .here) (up e)))) <|
      .imp (PowerlessFiniteSequencesSyntax.spec_m ω ω N) <|
        .imp (SecondOrderObjectSyntax.map_m T ω ω) <|
          .imp (PowerlessFiniteSequencesSyntax.spec_m ω A S) <|
            .iff (PowerlessSatisfactionSpecificationBounded.spec_m ω A e N T S t₁ t₂ t₃ F R)
              (PowerlessSatisfactionSpecification.spec_m ω A e t₁ t₂ t₃ T F R)

def sentence_m {Δ : SortContext ℒ} (ω A e N T S t₁ t₂ t₃ F R : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m ω A e N T S t₁ t₂ t₃ F R)

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (ω A e N T S t₁ t₂ t₃ F R : Term ℒ [] Δ .set) :
    (sentence_m ω A e N T S t₁ t₂ t₃ F R).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hω he hN hT hS
  have hω' := (omega_formula_l η ω).mp hω
  have he' : ∀ x, ¬SecondOrderQuotient.mem_l hℳ x (e.eval η) := by
    have he'' := he
    simp only [Formula.satisfies, member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval] at he''
    simpa only [Env.pushBound, Assignment.push, SecondOrderQuotient.structure_l] using he''
  have hN' := (PowerlessFiniteSequencesSyntax.spec_formula_l η ω ω N).mp hN
  have hT' := (map_formula_l η T ω ω).mp hT
  have hS' := (PowerlessFiniteSequencesSyntax.spec_formula_l η ω A S).mp hS
  exact (PowerlessSatisfactionSpecificationBounded.spec_formula_l η ω A e N T S t₁ t₂ t₃ F R).trans
    ((PowerlessSatisfactionSpecificationBounded.guarded_iff_l (hℳ := hℳ) hω' he' hN' hT' hS').trans
      (PowerlessSatisfactionSpecification.spec_formula_l η ω A e t₁ t₂ t₃ T F R).symm)

theorem derives_m {Δ : SortContext ℒ} (ω A e N T S t₁ t₂ t₃ F R : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m ω A e N T S t₁ t₂ t₃ F R)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ ω A e N T S t₁ t₂ t₃ F R)

#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSatisfactionSpecificationBoundedDerives
