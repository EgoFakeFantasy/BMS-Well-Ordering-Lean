import BMSConstructibleBridge.PowerlessBoundedNumericPairing
import BMSConstructibleBridge.PowerlessBoundedDigit
import BMSConstructibleBridge.PowerlessValueBounded
import BMSConstructibleBridge.SecondOrderAssignmentSyntax

/-! # 原有限赋值读取及有效性的纯 Δ₀ 检查

读取使用给定数值幂图 P、完整 Seq(ω,ω) 母集 N 和原数字位关系。
所有数值见证及检查坐标均在内部 ω 中；有效性同时保留界内总唯一与界外
无边，不假定内部长度外部标准。读取只要求 P 的数字坐标对应原实数 E，
不增加 E 的幂图正确性前提，也不选择原实数为宿主 Type 数据。

本模块提供有界 AST 和任意原模型中的精确读数；这些语义接口本身不能
替代最终原对象理论中的 Derives 交付。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyAssignmentBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)

private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)

def read_m {Γ Δ : SortContext ℒ} (ω e N P c i b : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| .conj
    (PowerlessBoundedNumericPairing.formula_m (up ω) (up e) (up N) (up i) (up b) (.bvar .here)) <|
      membershipLevyBound.boundedExists (up ω) <| .conj
        (PowerlessValueBounded.formula_m (up₂ P) (.bvar (.there .here)) (.bvar .here))
        (PowerlessBoundedDigit.formula_m (up₂ ω) (up₂ e) (up₂ N) (up₂ c) (.bvar .here))

theorem read_delta_l {Γ Δ : SortContext ℒ} (ω e N P c i b : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (read_m ω e N P c i b) :=
  .bounded_exists ω (.conj (PowerlessBoundedNumericPairing.delta_l _ _ _ _ _ _)
    (.bounded_exists (up ω) (.conj (PowerlessValueBounded.delta_l _ _ _)
      (PowerlessBoundedDigit.delta_l _ _ _ _ _))))

def read_holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e N P c i b : carrier_l 𝒩) : Prop :=
  ∃ z, member_l 𝒩 z ω ∧
    PowerlessBoundedNumericPairing.holds_l (𝒩 := 𝒩) ω e N i b z ∧
      ∃ p, member_l 𝒩 p ω ∧ value_l (ℳ := 𝒩) P z p ∧
        PowerlessBoundedDigit.holds_l (𝒩 := 𝒩) ω e N c p

theorem read_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N P c i b : Term ℒ Γ Δ .set) :
    (read_m ω e N P c i b).satisfies η ↔
      read_holds_l (ω.eval η) (e.eval η) (N.eval η) (P.eval η) (c.eval η) (i.eval η) (b.eval η) := by
  simp only [read_m, read_holds_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessBoundedNumericPairing.formula_l,
    PowerlessValueBounded.formula_l, PowerlessBoundedDigit.formula_l, Arguments.eval,
    up, up₂, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

/-- 数字坐标的图对应已足够；原 E 可以是任意关系实数。 -/
theorem read_reading_l (K : source_coding_l hℳ) {N P : type_l hℳ}
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega K.omega N) {E : SecondOrderModel.set_l ℳ}
    (hPnumeric : ∀ n m, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) P
      (numberCode_l K n).val (numberCode_l K m).val ↔ SecondOrderPairing.relation_l E n m)
    (c i b : SecondOrderModel.num_l ℳ) :
    read_holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val N P
        (numberCode_l K c).val (numberCode_l K i).val (numberCode_l K b).val ↔
          SecondOrderSequenceSyntax.read_l E c i b := by
  constructor
  · rintro ⟨z, _hz, hPair, p, hp, hPower, hDigit⟩
    have hzEq := (PowerlessBoundedNumericPairing.instance_l K hN i b z).mp hPair
    obtain ⟨j, hj⟩ := numberCode_surjective_l K ⟨p, hp⟩
    have hpEq : p = (numberCode_l K j).val := (congrArg Subtype.val hj).symm
    rw [hzEq, hpEq] at hPower
    rw [hpEq] at hDigit
    exact ⟨SecondOrderPairing.value_l i b, j, rfl,
      (hPnumeric _ j).mp hPower, (PowerlessBoundedDigit.instance_l K hN c j).mp hDigit⟩
  · rintro ⟨z, p, rfl, hPower, hDigit⟩
    exact ⟨(numberCode_l K (SecondOrderPairing.value_l i b)).val,
      (numberCode_l K (SecondOrderPairing.value_l i b)).property,
      (PowerlessBoundedNumericPairing.instance_l K hN i b _).mpr rfl,
      (numberCode_l K p).val, (numberCode_l K p).property,
      (hPnumeric _ p).mpr hPower, (PowerlessBoundedDigit.instance_l K hN c p).mpr hDigit⟩

def valid_m {Γ Δ : SortContext ℒ} (ω e N P c l : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj
    (membershipLevyBound.boundedForall ω <| .imp
      (SecondOrderObjectSyntax.member_m (.bvar .here) (up l)) <|
        membershipLevyBound.boundedExists (up ω) <| .conj
          (read_m (up₂ ω) (up₂ e) (up₂ N) (up₂ P) (up₂ c) (.bvar (.there .here)) (.bvar .here))
          (membershipLevyBound.boundedForall (up₂ ω) <| .imp
            (read_m (up₃ ω) (up₃ e) (up₃ N) (up₃ P) (up₃ c)
              (.bvar (.there (.there .here))) (.bvar .here))
            (.equal (.bvar .here) (.bvar (.there .here)))))
    (membershipLevyBound.boundedForall ω <| membershipLevyBound.boundedForall (up ω) <| .imp
      (read_m (up₂ ω) (up₂ e) (up₂ N) (up₂ P) (up₂ c) (.bvar (.there .here)) (.bvar .here))
      (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (up₂ l)))

theorem valid_delta_l {Γ Δ : SortContext ℒ} (ω e N P c l : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (valid_m ω e N P c l) :=
  .conj
    (.bounded_forall ω (.imp (.rel _ _) (.bounded_exists (up ω)
      (.conj (read_delta_l _ _ _ _ _ _ _) (.bounded_forall (up₂ ω)
        (.imp (read_delta_l _ _ _ _ _ _ _) (.equal _ _)))))))
    (.bounded_forall ω (.bounded_forall (up ω) (.imp (read_delta_l _ _ _ _ _ _ _) (.rel _ _))))

def valid_holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e N P c l : carrier_l 𝒩) : Prop :=
  (∀ i, member_l 𝒩 i ω → member_l 𝒩 i l →
    ∃ b, member_l 𝒩 b ω ∧ read_holds_l (𝒩 := 𝒩) ω e N P c i b ∧
      ∀ d, member_l 𝒩 d ω → read_holds_l (𝒩 := 𝒩) ω e N P c i d → d = b) ∧
    ∀ i, member_l 𝒩 i ω → ∀ b, member_l 𝒩 b ω →
      read_holds_l (𝒩 := 𝒩) ω e N P c i b → member_l 𝒩 i l

theorem valid_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N P c l : Term ℒ Γ Δ .set) :
    (valid_m ω e N P c l).satisfies η ↔
      valid_holds_l (ω.eval η) (e.eval η) (N.eval η) (P.eval η) (c.eval η) (l.eval η) := by
  simp only [valid_m, valid_holds_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.boundedForall, Formula.LevyBound.membership, membershipLevyBound,
    Formula.satisfies, read_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval,
    up, up₂, up₃, Term.eval_weakenBound, Term.eval]
  rfl

/-- 全部内部数上的有效性，包含界外无边；不只读取已知的有限值表。 -/
theorem valid_reading_l (K : source_coding_l hℳ) {N P : type_l hℳ}
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega K.omega N) {E : SecondOrderModel.set_l ℳ}
    (hPnumeric : ∀ n m, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) P
      (numberCode_l K n).val (numberCode_l K m).val ↔ SecondOrderPairing.relation_l E n m)
    (c l : SecondOrderModel.num_l ℳ) :
    valid_holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val N P
        (numberCode_l K c).val (numberCode_l K l).val ↔
          SecondOrderAssignmentSyntax.valid_l E c l := by
  unfold valid_holds_l SecondOrderAssignmentSyntax.valid_l
  constructor
  · rintro ⟨hTotal, hNoExtra⟩
    refine ⟨?_, ?_⟩
    · intro i hi
      obtain ⟨b, hb, hRead, hUnique⟩ := hTotal (numberCode_l K i).val
        (numberCode_l K i).property ((numberCode_mem_iff_lt_l K i l).mpr hi)
      obtain ⟨j, hj⟩ := numberCode_surjective_l K ⟨b, hb⟩
      have hbEq : b = (numberCode_l K j).val := (congrArg Subtype.val hj).symm
      rw [hbEq] at hRead hUnique
      refine ⟨j, (read_reading_l K hN hPnumeric c i j).mp hRead, ?_⟩
      intro k hk
      have hEq := hUnique (numberCode_l K k).val (numberCode_l K k).property
        ((read_reading_l K hN hPnumeric c i k).mpr hk)
      exact numberCode_injective_l K (Subtype.ext hEq)
    · intro i b hRead
      exact (numberCode_mem_iff_lt_l K i l).mp
        (hNoExtra (numberCode_l K i).val (numberCode_l K i).property
          (numberCode_l K b).val (numberCode_l K b).property
            ((read_reading_l K hN hPnumeric c i b).mpr hRead))
  · rintro ⟨hTotal, hNoExtra⟩
    refine ⟨?_, ?_⟩
    · intro i hiω hil
      obtain ⟨k, hk⟩ := numberCode_surjective_l K ⟨i, hiω⟩
      have hiEq : i = (numberCode_l K k).val := (congrArg Subtype.val hk).symm
      rw [hiEq] at hil ⊢
      obtain ⟨b, hb, hUnique⟩ := hTotal k ((numberCode_mem_iff_lt_l K k l).mp hil)
      refine ⟨(numberCode_l K b).val, (numberCode_l K b).property,
        (read_reading_l K hN hPnumeric c k b).mpr hb, ?_⟩
      intro d hdω hRead
      obtain ⟨j, hj⟩ := numberCode_surjective_l K ⟨d, hdω⟩
      have hdEq : d = (numberCode_l K j).val := (congrArg Subtype.val hj).symm
      rw [hdEq] at hRead ⊢
      exact congrArg (fun n => (numberCode_l K n).val)
        (hUnique j ((read_reading_l K hN hPnumeric c k j).mp hRead))
    · intro i hiω b hbω hRead
      obtain ⟨k, hk⟩ := numberCode_surjective_l K ⟨i, hiω⟩
      obtain ⟨j, hj⟩ := numberCode_surjective_l K ⟨b, hbω⟩
      have hiEq : i = (numberCode_l K k).val := (congrArg Subtype.val hk).symm
      have hbEq : b = (numberCode_l K j).val := (congrArg Subtype.val hj).symm
      rw [hiEq, hbEq] at hRead
      rw [hiEq]
      exact (numberCode_mem_iff_lt_l K k l).mpr
        (hNoExtra k j ((read_reading_l K hN hPnumeric c k j).mp hRead))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyAssignmentBounded
