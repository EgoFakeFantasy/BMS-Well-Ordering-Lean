import BMSConstructibleBridge.PowerlessBoundedMultiplication
import BMSConstructibleBridge.SecondOrderDigit

/-! # 二进制位的纯集合 Δ₀ 检查式

原带余除法见证及全部加乘中间值统一由 ω 界定，运算历史统一由 S 界定。
位权是实际内部自然数，不把原模型中的余数或位运算替换成宿主 Nat 计算。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundedDigit

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def body_m {Γ Δ : SortContext ℒ} (ω e S a p t q r v : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessBoundedAddition.formula_m ω e S p p t) <|
    .conj (PowerlessBoundedMultiplication.formula_m ω e S q t v) <|
      .conj (PowerlessBoundedAddition.formula_m ω e S v r a) <|
        .conj (.neg (SecondOrderObjectSyntax.member_m r p)) (SecondOrderObjectSyntax.member_m r t)

theorem body_delta_l {Γ Δ : SortContext ℒ} (ω e S a p t q r v : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (body_m ω e S a p t q r v) :=
  .conj (PowerlessBoundedAddition.delta_l _ _ _ _ _ _)
    (.conj (PowerlessBoundedMultiplication.delta_l _ _ _ _ _ _)
      (.conj (PowerlessBoundedAddition.delta_l _ _ _ _ _ _) (.conj (.neg (.rel _ _)) (.rel _ _))))

def formula_m {Γ Δ : SortContext ℒ} (ω e S a p : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up (up (up t)))
  membershipLevyBound.boundedExists ω <| membershipLevyBound.boundedExists (up ω) <|
    membershipLevyBound.boundedExists (up (up ω)) <|
      membershipLevyBound.boundedExists (up (up (up ω))) <|
        body_m (w ω) (w e) (w S) (w a) (w p) (.bvar (.there (.there (.there .here))))
          (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)

theorem delta_l {Γ Δ : SortContext ℒ} (ω e S a p : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m ω e S a p) :=
  .bounded_exists ω (.bounded_exists (up ω) (.bounded_exists (up (up ω))
    (.bounded_exists (up (up (up ω))) (body_delta_l _ _ _ _ _ _ _ _ _))))

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e S a p : carrier_l 𝒩) : Prop :=
  ∃ t, member_l 𝒩 t ω ∧ ∃ q, member_l 𝒩 q ω ∧ ∃ r, member_l 𝒩 r ω ∧ ∃ v, member_l 𝒩 v ω ∧
    PowerlessBoundedAddition.holds_l (𝒩 := 𝒩) ω e S p p t ∧
    PowerlessBoundedMultiplication.holds_l (𝒩 := 𝒩) ω e S q t v ∧
    PowerlessBoundedAddition.holds_l (𝒩 := 𝒩) ω e S v r a ∧ ¬member_l 𝒩 r p ∧ member_l 𝒩 r t

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e S a p : Term ℒ Γ Δ .set) : (formula_m ω e S a p).satisfies η ↔
      holds_l (ω.eval η) (e.eval η) (S.eval η) (a.eval η) (p.eval η) := by
  simp only [formula_m, body_m, holds_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessBoundedMultiplication.formula_l,
    PowerlessBoundedAddition.formula_l, SecondOrderObjectSyntax.member_m,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem instance_l (K : source_coding_l hℳ) {S : type_l hℳ}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega S)
    (a p : SecondOrderModel.num_l ℳ) :
    holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val S (numberCode_l K a).val (numberCode_l K p).val ↔
        SecondOrderDigit.holds_l a p := by
  constructor
  · rintro ⟨t, _, q, hq, r, hr, v, _, hDouble, hMul, hAdd, hNot, hLt⟩
    obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨q, hq⟩
    obtain ⟨j, hj⟩ := numberCode_surjective_l K ⟨r, hr⟩
    have hi' : q = (numberCode_l K i).val := (congrArg Subtype.val hi).symm
    have hj' : r = (numberCode_l K j).val := (congrArg Subtype.val hj).symm
    have ht' := (PowerlessBoundedAddition.instance_l K hS p p t).mp hDouble
    rw [hi', ht'] at hMul
    have hv' := (PowerlessBoundedMultiplication.instance_l K hS i (SecondOrderModel.add_l p p) v).mp hMul
    rw [hv', hj'] at hAdd
    have ha' := (PowerlessBoundedAddition.instance_l K hS
      (SecondOrderModel.mul_l i (SecondOrderModel.add_l p p)) j (numberCode_l K a).val).mp hAdd
    have haEq := numberCode_injective_l K (Subtype.ext ha')
    rw [hj'] at hNot
    rw [hj', ht'] at hLt
    exact ⟨i, j, haEq, (fun h => hNot ((numberCode_mem_iff_lt_l K j p).mpr h)),
      (numberCode_mem_iff_lt_l K j (SecondOrderModel.add_l p p)).mp hLt⟩
  · rintro ⟨q, r, ha, hNot, hLt⟩
    refine ⟨(numberCode_l K (SecondOrderModel.add_l p p)).val,
      (numberCode_l K (SecondOrderModel.add_l p p)).property,
      (numberCode_l K q).val, (numberCode_l K q).property,
      (numberCode_l K r).val, (numberCode_l K r).property,
      (numberCode_l K (SecondOrderModel.mul_l q (SecondOrderModel.add_l p p))).val,
      (numberCode_l K (SecondOrderModel.mul_l q (SecondOrderModel.add_l p p))).property,
      (PowerlessBoundedAddition.instance_l K hS p p _).mpr rfl,
      (PowerlessBoundedMultiplication.instance_l K hS q (SecondOrderModel.add_l p p) _).mpr rfl,
      (PowerlessBoundedAddition.instance_l K hS (SecondOrderModel.mul_l q (SecondOrderModel.add_l p p)) r _).mpr
        (congrArg (fun n => (numberCode_l K n).val) ha),
      (fun h => hNot ((numberCode_mem_iff_lt_l K r p).mp h)),
      (numberCode_mem_iff_lt_l K r (SecondOrderModel.add_l p p)).mpr hLt⟩

#print axioms delta_l
#print axioms instance_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundedDigit
