import BMSConstructibleBridge.PowerlessEvaluationFiniteHistory
import BMSConstructibleBridge.PowerlessHistoryBounded
import BMSConstructibleBridge.PowerlessEvaluationStepBounded
import BMSConstructibleBridge.SecondOrderOmegaOrdinal

/-! # 有限求值历史的纯 Δ₀ 检查

图、列值、精确前史均显式限于固定层 C。原有限历史中的前史见证起初
可以不在 C；先构造同层的精确限制图，再用外延唯一性识别二者。
等价性使用模型内部的有限序数，不要求 C∈C 或 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationFiniteHistoryBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def formula_m {Γ Δ : SortContext ℒ} (C ω e N T A S t₁ t₂ t₃ F n : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up (up t))
  .conj (PowerlessMapBounded.formula_m F n C) <|
    membershipLevyBound.boundedForall n <|
      membershipLevyBound.boundedForall (up C) <| .imp
        (PowerlessValueBounded.formula_m (up (up F)) (.bvar (.there .here)) (.bvar .here)) <|
        membershipLevyBound.boundedExists (up (up C)) <| .conj
          (PowerlessHistoryBounded.formula_m (.bvar .here) (w F) (.bvar (.there (.there .here))) (w C))
          (PowerlessEvaluationStepBounded.formula_m (w ω) (w e) (w N) (w T) (w A) (w S)
            (w t₁) (w t₂) (w t₃) (.bvar .here) (.bvar (.there (.there .here))) (.bvar (.there .here)))

theorem delta_l {Γ Δ : SortContext ℒ} (C ω e N T A S t₁ t₂ t₃ F n : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m C ω e N T A S t₁ t₂ t₃ F n) :=
  .conj (PowerlessMapBounded.delta_l _ _ _) (.bounded_forall n
    (.bounded_forall (up C) (.imp (PowerlessValueBounded.delta_l _ _ _)
      (.bounded_exists (up (up C)) (.conj (PowerlessHistoryBounded.delta_l _ _ _ _)
        (PowerlessEvaluationStepBounded.delta_l _ _ _ _ _ _ _ _ _ _ _ _))))))

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (C ω e N T A S t₁ t₂ t₃ F n : carrier_l 𝒩) : Prop :=
  map_l (ℳ := 𝒩) F n C ∧ ∀ k, member_l 𝒩 k n → ∀ Y, member_l 𝒩 Y C →
    value_l (ℳ := 𝒩) F k Y → ∃ H, member_l 𝒩 H C ∧
      PowerlessHistoryBounded.holds_l H F k C ∧
      PowerlessEvaluationStepBounded.holds_l ω e N T A S t₁ t₂ t₃ H k Y

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (C ω e N T A S t₁ t₂ t₃ F n : Term ℒ Γ Δ .set) :
    (formula_m C ω e N T A S t₁ t₂ t₃ F n).satisfies η ↔
      holds_l (C.eval η) (ω.eval η) (e.eval η) (N.eval η) (T.eval η) (A.eval η) (S.eval η)
        (t₁.eval η) (t₂.eval η) (t₃.eval η) (F.eval η) (n.eval η) := by
  simp only [formula_m, holds_l, Formula.LevyBound.boundedForall, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessMapBounded.formula_l, PowerlessValueBounded.formula_l,
    PowerlessHistoryBounded.formula_l, PowerlessEvaluationStepBounded.formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem trace_iff_l (K : source_coding_l hℳ) {B β C e N T A S t₁ t₂ t₃ F n : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C) (hωC : mem_l hℳ K.omega C)
    (he : PowerlessNatural.zero_l (ℳ := SecondOrderQuotient.structure_l hℳ) e)
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega N)
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T K.omega K.omega)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega A S)
    (hn : mem_l hℳ n K.omega) :
    holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) C K.omega e N T A S t₁ t₂ t₃ F n ↔
      PowerlessEvaluationFiniteHistory.trace_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
        C K.omega e T A t₁ t₂ t₃ S F n := by
  have hω : omega_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega := K.omega_spec
  have hOrdinal : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)) n := by
    apply SetTheory.Structure.IsOrdinal.mem (α := K.omega)
      (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)
    exact hn
  constructor
  · rintro ⟨hF, hRead⟩
    refine ⟨hF, fun k Y hValue => ?_⟩
    have hBounds := SecondOrderFunctionProperties.value_mem_l hℳ hF hValue
    obtain ⟨H, _, hHistory, hStep⟩ := hRead k hBounds.1 Y hBounds.2 hValue
    exact ⟨H, (PowerlessHistoryBounded.history_iff_l hℳ hF).mp hHistory,
      (PowerlessEvaluationStepBounded.step_iff_l (hℳ := hℳ) hω he hN hT hS).mp hStep⟩
  · rintro ⟨hF, hRead⟩
    refine ⟨hF, fun k hk Y _ hValue => ?_⟩
    obtain ⟨H, hHistory, hStep⟩ := hRead k Y hValue
    have hkω := SecondOrderOmegaTransitive.member_l hℳ K.omega_spec hn hk
    obtain ⟨J, hJC, _, hJ⟩ := PowerlessRelativeLimitHistory.exists_l K hBase hLimit hC hωC hkω hF
      (fun x hx => hOrdinal.transitive k hk x hx)
    have hHJ : H = J := PowerlessRelativeLimitHistory.unique_l hHistory hJ
    subst J
    exact ⟨H, hJC, (PowerlessHistoryBounded.history_iff_l hℳ hF).mpr hHistory,
      (PowerlessEvaluationStepBounded.step_iff_l (hℳ := hℳ) hω he hN hT hS).mpr hStep⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationFiniteHistoryBounded
