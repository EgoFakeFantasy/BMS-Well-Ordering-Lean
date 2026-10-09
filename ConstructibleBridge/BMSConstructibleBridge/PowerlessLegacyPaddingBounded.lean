import BMSConstructibleBridge.PowerlessLegacyAssignmentBounded
import BMSConstructibleBridge.PowerlessLegacyIndexBounded
import BMSConstructibleBridge.SecondOrderLegacyAssignmentPadding

/-! # 原反转补齐关系的纯 Δ₀ 检查

严格沿用原 padded_l：目标槽 i 必须小于 L；反转分支的源槽 k 满足
k + succ i = l，并读取原码 c 的第 k 项；默认分支恰为 ¬i < l 且 j = z。
全部数值见证由内部 ω 界定，不假设 l ≤ L、原赋值有效性或内部长度
外部标准。给定 P 的数字图读数已足够，原实数 E 无须另加幂图正确性。

本模块只交付纯集合 AST、Δ₀ 证书及任意原模型中的精确读数；最终原
对象理论中的 Derives 仍须由调用端正式接线，不能由语义定理替代。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyPaddingBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def formula_m {Γ Δ : SortContext ℒ}
    (ω e N P c l L z i j : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (SecondOrderObjectSyntax.member_m i L) <| .disj
    (membershipLevyBound.boundedExists ω <| .conj
      (PowerlessLegacyIndexBounded.formula_m (up ω) (up e) (up N) (up l) (.bvar .here) (up i))
      (PowerlessLegacyAssignmentBounded.read_m
        (up ω) (up e) (up N) (up P) (up c) (.bvar .here) (up j)))
    (.conj (.neg (SecondOrderObjectSyntax.member_m i l)) (.equal j z))

theorem delta_l {Γ Δ : SortContext ℒ}
    (ω e N P c l L z i j : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m ω e N P c l L z i j) :=
  .conj (.rel _ _) <| .disj
    (.bounded_exists ω (.conj (PowerlessLegacyIndexBounded.delta_l _ _ _ _ _ _)
      (PowerlessLegacyAssignmentBounded.read_delta_l _ _ _ _ _ _ _)))
    (.conj (.neg (.rel _ _)) (.equal _ _))

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e N P c l L z i j : carrier_l 𝒩) : Prop :=
  member_l 𝒩 i L ∧
    ((∃ k, member_l 𝒩 k ω ∧
      PowerlessLegacyIndexBounded.holds_l (𝒩 := 𝒩) ω e N l k i ∧
        PowerlessLegacyAssignmentBounded.read_holds_l (𝒩 := 𝒩) ω e N P c k j) ∨
      ¬member_l 𝒩 i l ∧ j = z)

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N P c l L z i j : Term ℒ Γ Δ .set) :
    (formula_m ω e N P c l L z i j).satisfies η ↔
      holds_l (ω.eval η) (e.eval η) (N.eval η) (P.eval η) (c.eval η)
        (l.eval η) (L.eval η) (z.eval η) (i.eval η) (j.eval η) := by
  simp only [formula_m, holds_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessLegacyIndexBounded.formula_l, PowerlessLegacyAssignmentBounded.read_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

/-- 精确读取全部内部槽的原补齐关系，包含原默认分支；不增加 E 的正确性前提。 -/
theorem reading_l (K : source_coding_l hℳ) {N P : type_l hℳ}
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega K.omega N) {E : SecondOrderModel.set_l ℳ}
    (hPnumeric : ∀ n m, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) P
      (numberCode_l K n).val (numberCode_l K m).val ↔ SecondOrderPairing.relation_l E n m)
    (c l L z i j : SecondOrderModel.num_l ℳ) :
    holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val N P
        (numberCode_l K c).val (numberCode_l K l).val (numberCode_l K L).val
        (numberCode_l K z).val (numberCode_l K i).val (numberCode_l K j).val ↔
          SecondOrderLegacyAssignmentPadding.padded_l E c l L z i j := by
  unfold holds_l SecondOrderLegacyAssignmentPadding.padded_l
  constructor
  · rintro ⟨hiL, hReverse | ⟨hiNot, hjEq⟩⟩
    · obtain ⟨k, hkω, hIndex, hRead⟩ := hReverse
      obtain ⟨a, ha⟩ := numberCode_surjective_l K ⟨k, hkω⟩
      have hkEq : k = (numberCode_l K a).val := (congrArg Subtype.val ha).symm
      rw [hkEq] at hIndex hRead
      exact ⟨(numberCode_mem_iff_lt_l K i L).mp hiL, Or.inl
        ⟨a, (PowerlessLegacyIndexBounded.reading_l K hN l a i).mp hIndex,
          (PowerlessLegacyAssignmentBounded.read_reading_l K hN hPnumeric c a j).mp hRead⟩⟩
    · exact ⟨(numberCode_mem_iff_lt_l K i L).mp hiL, Or.inr
        ⟨fun hi => hiNot ((numberCode_mem_iff_lt_l K i l).mpr hi),
          numberCode_injective_l K (Subtype.ext hjEq)⟩⟩
  · rintro ⟨hiL, hReverse | ⟨hiNot, hjEq⟩⟩
    · obtain ⟨k, hIndex, hRead⟩ := hReverse
      exact ⟨(numberCode_mem_iff_lt_l K i L).mpr hiL, Or.inl
        ⟨(numberCode_l K k).val, (numberCode_l K k).property,
          (PowerlessLegacyIndexBounded.reading_l K hN l k i).mpr hIndex,
          (PowerlessLegacyAssignmentBounded.read_reading_l K hN hPnumeric c k j).mpr hRead⟩⟩
    · exact ⟨(numberCode_mem_iff_lt_l K i L).mpr hiL, Or.inr
        ⟨fun hi => hiNot ((numberCode_mem_iff_lt_l K i l).mp hi),
          congrArg (fun n => (numberCode_l K n).val) hjEq⟩⟩

#print axioms delta_l
#print axioms formula_l
#print axioms reading_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyPaddingBounded
