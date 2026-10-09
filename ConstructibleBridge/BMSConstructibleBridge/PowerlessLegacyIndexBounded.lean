import BMSConstructibleBridge.PowerlessLegacyNumericReading
import BMSConstructibleBridge.SecondOrderLegacyAssignmentReversal

/-! # 原反转槽关系的纯 Δ₀ 检查

精确保留 i + succ r = l。全部算术见证在原 ω 内，数字读数涵盖任意
内部长度；不抽取 Type 层反转函数，也不假定完整源模型。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyIndexBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l)
open SecondOrderModel (num_l)
open PowerlessFormulaValidityReading (code_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def formula_m {Γ Δ : SortContext ℒ} (ω e N l i r : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| .conj
    (PowerlessSuccessorBounded.formula_m (up r) (.bvar .here))
    (PowerlessBoundedAddition.formula_m (up ω) (up e) (up N) (up i) (.bvar .here) (up l))

theorem delta_l {Γ Δ : SortContext ℒ} (ω e N l i r : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m ω e N l i r) :=
  .bounded_exists ω (.conj (PowerlessSuccessorBounded.delta_l _ _)
    (PowerlessBoundedAddition.delta_l _ _ _ _ _ _))

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e N l i r : carrier_l 𝒩) : Prop :=
  ∃ s, member_l 𝒩 s ω ∧ PowerlessNatural.successor_l r s ∧
    PowerlessBoundedAddition.holds_l ω e N i s l

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N l i r : Term ℒ Γ Δ .set) :
    (formula_m ω e N l i r).satisfies η ↔
      holds_l (ω.eval η) (e.eval η) (N.eval η) (l.eval η) (i.eval η) (r.eval η) := by
  simp only [formula_m, holds_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessSuccessorBounded.formula_l,
    PowerlessBoundedAddition.formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem reading_l (K : source_coding_l hℳ) {N : type_l hℳ}
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega K.omega N) (l i r : num_l ℳ) :
    holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega
      (code_l K (SecondOrderModel.zero_l ℳ)) N (code_l K l) (code_l K i) (code_l K r) ↔
        SecondOrderLegacyAssignmentReversal.index_l l i r := by
  constructor
  · rintro ⟨s, _, hs, hAdd⟩
    rw [(PowerlessNumberSuccessorReading.successor_l K r s).mp hs] at hAdd
    exact (PowerlessLegacyNumericReading.code_eq_l K _ _).mp
      ((PowerlessBoundedAddition.instance_l K hN i (SecondOrderModel.succ_l r) _).mp hAdd).symm
  · intro hIndex
    refine ⟨code_l K (SecondOrderModel.succ_l r), (numberCode_l K _).property,
      (PowerlessNumberSuccessorReading.successor_l K r _).mpr rfl, ?_⟩
    exact (PowerlessBoundedAddition.instance_l K hN i (SecondOrderModel.succ_l r) _).mpr
      (congrArg (code_l K) hIndex.symm)

#print axioms delta_l
#print axioms reading_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyIndexBounded
