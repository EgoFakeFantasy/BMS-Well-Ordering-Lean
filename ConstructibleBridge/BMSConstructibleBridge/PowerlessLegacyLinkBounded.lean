import BMSConstructibleBridge.PowerlessLegacyPaddingBounded
import BMSConstructibleBridge.PowerlessLegacyAssignmentSyntax

/-! # 原有限赋值链接的纯 Δ₀ 检查

检查坐标 i、补齐值 j 均由内部 ω 界定，输出 y 由共同陪域 A 界定。
恢复原 link_l 的全部环境输出时，不删除类外输出量词：任一 f 边或 U 边
都由给定映射规格推出 y ∈ A，故 y ∉ A 时两侧均不可能成立。
完整数码满射覆盖全部内部 i、j，不要求内部长度外部标准。

本模块只提供有界 AST 及其原模型语义读数，不宣称完成原对象理论的
Derives，也不要求原关系实数 E 的幂图正确性或作 Type 层选择。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyLinkBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)

private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)

def formula_m {Γ Δ : SortContext ℒ}
    (ω e N P c l L z A U f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall ω <|
    membershipLevyBound.boundedForall (up A) <| .iff
      (PowerlessValueBounded.formula_m (up₂ f) (.bvar (.there .here)) (.bvar .here))
      (membershipLevyBound.boundedExists (up₂ ω) <| .conj
        (PowerlessLegacyPaddingBounded.formula_m
          (up₃ ω) (up₃ e) (up₃ N) (up₃ P) (up₃ c) (up₃ l) (up₃ L) (up₃ z)
          (.bvar (.there (.there .here))) (.bvar .here))
        (PowerlessValueBounded.formula_m (up₃ U) (.bvar .here) (.bvar (.there .here))))

theorem delta_l {Γ Δ : SortContext ℒ}
    (ω e N P c l L z A U f : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m ω e N P c l L z A U f) :=
  .bounded_forall ω (.bounded_forall (up A) (.iff (PowerlessValueBounded.delta_l _ _ _)
    (.bounded_exists (up₂ ω) (.conj (PowerlessLegacyPaddingBounded.delta_l _ _ _ _ _ _ _ _ _ _)
      (PowerlessValueBounded.delta_l _ _ _)))))

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e N P c l L z A U f : carrier_l 𝒩) : Prop :=
  ∀ i, member_l 𝒩 i ω → ∀ y, member_l 𝒩 y A →
    (value_l (ℳ := 𝒩) f i y ↔
      ∃ j, member_l 𝒩 j ω ∧
        PowerlessLegacyPaddingBounded.holds_l (𝒩 := 𝒩) ω e N P c l L z i j ∧
          value_l (ℳ := 𝒩) U j y)

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N P c l L z A U f : Term ℒ Γ Δ .set) :
    (formula_m ω e N P c l L z A U f).satisfies η ↔
      holds_l (ω.eval η) (e.eval η) (N.eval η) (P.eval η) (c.eval η)
        (l.eval η) (L.eval η) (z.eval η) (A.eval η) (U.eval η) (f.eval η) := by
  simp only [formula_m, holds_l, Formula.LevyBound.boundedForall,
    Formula.LevyBound.boundedExists, Formula.LevyBound.membership, membershipLevyBound,
    Formula.satisfies, PowerlessValueBounded.formula_l, PowerlessLegacyPaddingBounded.formula_l,
    Arguments.eval, up, up₂, up₃, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

/-- 两张实际映射的陪域守卫恢复原链接中的全部 raw 输出，数量词读取全部内部数。 -/
theorem reading_l (K : source_coding_l hℳ) {N P A U f : type_l hℳ}
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega K.omega N) {E : SecondOrderModel.set_l ℳ}
    (hPnumeric : ∀ n m, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) P
      (numberCode_l K n).val (numberCode_l K m).val ↔ SecondOrderPairing.relation_l E n m)
    (c l L z : SecondOrderModel.num_l ℳ)
    (hU : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) U K.omega A)
    (hf : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) f (numberCode_l K L).val A) :
    holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val N P
        (numberCode_l K c).val (numberCode_l K l).val (numberCode_l K L).val
        (numberCode_l K z).val A U f ↔
          PowerlessLegacyAssignmentSyntax.link_l K E c l L z U f := by
  unfold holds_l PowerlessLegacyAssignmentSyntax.link_l
  constructor
  · intro hBound i y
    constructor
    · intro hfy
      -- 左侧边必落在 A 中；y ∉ A 时左侧不可能成立。
      have hyA := (SecondOrderFunctionProperties.value_mem_l hℳ hf hfy).2
      obtain ⟨j, hjω, hPad, hUy⟩ :=
        (hBound (numberCode_l K i).val (numberCode_l K i).property y hyA).mp hfy
      obtain ⟨a, ha⟩ := numberCode_surjective_l K ⟨j, hjω⟩
      have hjEq : j = (numberCode_l K a).val := (congrArg Subtype.val ha).symm
      rw [hjEq] at hPad hUy
      exact ⟨a, (PowerlessLegacyPaddingBounded.reading_l K hN hPnumeric c l L z i a).mp hPad, hUy⟩
    · rintro ⟨j, hPad, hUy⟩
      -- 右侧的 U 边也必落在 A 中；y ∉ A 时右侧不可能成立。
      have hyA := (SecondOrderFunctionProperties.value_mem_l hℳ hU hUy).2
      exact (hBound (numberCode_l K i).val (numberCode_l K i).property y hyA).mpr
        ⟨(numberCode_l K j).val, (numberCode_l K j).property,
          (PowerlessLegacyPaddingBounded.reading_l K hN hPnumeric c l L z i j).mpr hPad, hUy⟩
  · intro hLink i hiω y _hyA
    obtain ⟨a, ha⟩ := numberCode_surjective_l K ⟨i, hiω⟩
    have hiEq : i = (numberCode_l K a).val := (congrArg Subtype.val ha).symm
    rw [hiEq]
    constructor
    · intro hfy
      obtain ⟨j, hPad, hUy⟩ := (hLink a y).mp hfy
      exact ⟨(numberCode_l K j).val, (numberCode_l K j).property,
        (PowerlessLegacyPaddingBounded.reading_l K hN hPnumeric c l L z a j).mpr hPad, hUy⟩
    · rintro ⟨j, hjω, hPad, hUy⟩
      obtain ⟨b, hb⟩ := numberCode_surjective_l K ⟨j, hjω⟩
      have hjEq : j = (numberCode_l K b).val := (congrArg Subtype.val hb).symm
      rw [hjEq] at hPad hUy
      exact (hLink a y).mpr
        ⟨b, (PowerlessLegacyPaddingBounded.reading_l K hN hPnumeric c l L z a b).mp hPad, hUy⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyLinkBounded
