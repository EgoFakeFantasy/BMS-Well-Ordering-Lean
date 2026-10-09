import BMSConstructibleBridge.PowerlessEvaluationClauseBounded
import BMSConstructibleBridge.PowerlessEvaluationStep

/-! # 求值列完整成员规格的纯 Δ₀ 检查

列 Y 明确为赋值集 S 的子集，且在 S 上逐赋值检查局部规则。只有有界
双向式而没有 Y⊆S 会允许额外成员，不能等价于原全对象求值步。
原 ω、空集及数值／赋值序列规格 guard 下，等价回传原 Z₂ Derives。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationStepBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def formula_m {Γ Δ : SortContext ℒ} (ω e N T A S t₁ t₂ t₃ H n Y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ := .conj
  (membershipLevyBound.boundedForall Y (SecondOrderObjectSyntax.member_m (.bvar .here) (up S)))
  (membershipLevyBound.boundedForall S <| .iff
    (SecondOrderObjectSyntax.member_m (.bvar .here) (up Y))
    (PowerlessEvaluationClauseBounded.formula_m (up ω) (up e) (up N) (up T) (up A) (up S)
      (up t₁) (up t₂) (up t₃) (up H) (up n) (.bvar .here)))

theorem delta_l {Γ Δ : SortContext ℒ} (ω e N T A S t₁ t₂ t₃ H n Y : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m ω e N T A S t₁ t₂ t₃ H n Y) :=
  .conj (.bounded_forall Y (.rel _ _)) (.bounded_forall S
    (.iff (.rel _ _) (PowerlessEvaluationClauseBounded.delta_l _ _ _ _ _ _ _ _ _ _ _ _)))

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e N T A S t₁ t₂ t₃ H n Y : carrier_l 𝒩) : Prop :=
  (∀ f, member_l 𝒩 f Y → member_l 𝒩 f S) ∧ ∀ f, member_l 𝒩 f S →
    (member_l 𝒩 f Y ↔ PowerlessEvaluationClauseBounded.holds_l ω e N T A S t₁ t₂ t₃ H n f)

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N T A S t₁ t₂ t₃ H n Y : Term ℒ Γ Δ .set) :
    (formula_m ω e N T A S t₁ t₂ t₃ H n Y).satisfies η ↔
      holds_l (ω.eval η) (e.eval η) (N.eval η) (T.eval η) (A.eval η) (S.eval η)
        (t₁.eval η) (t₂.eval η) (t₃.eval η) (H.eval η) (n.eval η) (Y.eval η) := by
  simp only [formula_m, holds_l, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessEvaluationClauseBounded.formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem step_iff_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {ω e N T A S t₁ t₂ t₃ H n Y : type_l hℳ}
    (hω : omega_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω)
    (he : PowerlessNatural.zero_l (ℳ := SecondOrderQuotient.structure_l hℳ) e)
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω ω N)
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T ω ω)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω A S) :
    holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) ω e N T A S t₁ t₂ t₃ H n Y ↔
      PowerlessEvaluationStep.step_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω e T A t₁ t₂ t₃ S H n Y := by
  constructor
  · rintro ⟨hSubset, hRead⟩ f
    constructor
    · intro hf
      have hfS := hSubset f hf
      exact ⟨hfS, (PowerlessEvaluationClauseBounded.guarded_iff_l hω he hN hT hS hfS).mp ((hRead f hfS).mp hf)⟩
    · rintro ⟨hfS, hClause⟩
      exact (hRead f hfS).mpr ((PowerlessEvaluationClauseBounded.guarded_iff_l hω he hN hT hS hfS).mpr hClause)
  · intro hStep
    refine ⟨fun f hf => ((hStep f).mp hf).1, fun f hfS => ?_⟩
    exact (hStep f).trans ((and_iff_right hfS).trans
      (PowerlessEvaluationClauseBounded.guarded_iff_l hω he hN hT hS hfS).symm)

def schema_m {Δ : SortContext ℒ} (ω e N T A S t₁ t₂ t₃ H n Y : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .imp (.forallE .set (.neg (SecondOrderObjectSyntax.member_m (.bvar .here) (up e)))) <|
      .imp (PowerlessFiniteSequencesSyntax.spec_m ω ω N) <|
        .imp (SecondOrderObjectSyntax.map_m T ω ω) <|
          .imp (PowerlessFiniteSequencesSyntax.spec_m ω A S) <|
            .iff (formula_m ω e N T A S t₁ t₂ t₃ H n Y)
              (PowerlessEvaluationStep.step_m ω e T A t₁ t₂ t₃ S H n Y)

def sentence_m {Δ : SortContext ℒ} (ω e N T A S t₁ t₂ t₃ H n Y : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m ω e N T A S t₁ t₂ t₃ H n Y)

theorem derives_m {Δ : SortContext ℒ} (ω e N T A S t₁ t₂ t₃ H n Y : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m ω e N T A S t₁ t₂ t₃ H n Y)) := by
  apply SecondOrderAxioms.interpretation_m
  intro ℳ hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hω he hN hT hS
  have hω' := (omega_formula_l η ω).mp hω
  have he' : PowerlessNatural.zero_l (ℳ := SecondOrderQuotient.structure_l hℳ) (e.eval η) := by
    simpa only [PowerlessNatural.zero_l, ThirdOrderSemantics.member_l, Formula.satisfies,
      SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval,
      Env.pushBound_bound_here] using he
  have hN' := (PowerlessFiniteSequencesSyntax.spec_formula_l η ω ω N).mp hN
  have hT' := (map_formula_l η T ω ω).mp hT
  have hS' := (PowerlessFiniteSequencesSyntax.spec_formula_l η ω A S).mp hS
  exact (formula_l η ω e N T A S t₁ t₂ t₃ H n Y).trans
    ((step_iff_l hω' he' hN' hT' hS').trans (PowerlessEvaluationStep.step_formula_l η ω e T A t₁ t₂ t₃ S H n Y).symm)

#print axioms delta_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationStepBounded
