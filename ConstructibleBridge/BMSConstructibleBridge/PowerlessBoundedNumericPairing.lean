import BMSConstructibleBridge.PowerlessBoundedMultiplication
import BMSConstructibleBridge.SecondOrderPairing

/-! # 原平方分支配数的纯 Δ₀ 图

数值配数不是 Kuratowski 集合对，也不读取原签名中没有对应公理的额外
配对函数。严格使用 m<n 与 m≥n 两分支，全部中间数受 ω 界定。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundedNumericPairing

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def formula_m {Γ Δ : SortContext ℒ} (ω e S a b c : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj
    (.conj (SecondOrderObjectSyntax.member_m a b) <| membershipLevyBound.boundedExists ω <| .conj
      (PowerlessBoundedMultiplication.formula_m (up ω) (up e) (up S) (up b) (up b) (.bvar .here))
      (PowerlessBoundedAddition.formula_m (up ω) (up e) (up S) (.bvar .here) (up a) (up c)))
    (.conj (.neg (SecondOrderObjectSyntax.member_m a b)) <| membershipLevyBound.boundedExists ω <| .conj
      (PowerlessBoundedMultiplication.formula_m (up ω) (up e) (up S) (up a) (up a) (.bvar .here)) <|
      membershipLevyBound.boundedExists (up ω) <| .conj
        (PowerlessBoundedAddition.formula_m (up (up ω)) (up (up e)) (up (up S))
          (.bvar (.there .here)) (up (up a)) (.bvar .here))
        (PowerlessBoundedAddition.formula_m (up (up ω)) (up (up e)) (up (up S))
          (.bvar .here) (up (up b)) (up (up c))))

theorem delta_l {Γ Δ : SortContext ℒ} (ω e S a b c : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m ω e S a b c) :=
  .disj (.conj (.rel _ _) (.bounded_exists ω (.conj (PowerlessBoundedMultiplication.delta_l _ _ _ _ _ _)
    (PowerlessBoundedAddition.delta_l _ _ _ _ _ _))))
    (.conj (.neg (.rel _ _)) (.bounded_exists ω (.conj (PowerlessBoundedMultiplication.delta_l _ _ _ _ _ _)
      (.bounded_exists (up ω) (.conj (PowerlessBoundedAddition.delta_l _ _ _ _ _ _)
        (PowerlessBoundedAddition.delta_l _ _ _ _ _ _))))))

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e S a b c : carrier_l 𝒩) : Prop :=
  (member_l 𝒩 a b ∧ ∃ q, member_l 𝒩 q ω ∧
    PowerlessBoundedMultiplication.holds_l (𝒩 := 𝒩) ω e S b b q ∧
    PowerlessBoundedAddition.holds_l (𝒩 := 𝒩) ω e S q a c) ∨
  (¬member_l 𝒩 a b ∧ ∃ q, member_l 𝒩 q ω ∧
    PowerlessBoundedMultiplication.holds_l (𝒩 := 𝒩) ω e S a a q ∧
    ∃ r, member_l 𝒩 r ω ∧ PowerlessBoundedAddition.holds_l (𝒩 := 𝒩) ω e S q a r ∧
      PowerlessBoundedAddition.holds_l (𝒩 := 𝒩) ω e S r b c)

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e S a b c : Term ℒ Γ Δ .set) : (formula_m ω e S a b c).satisfies η ↔
      holds_l (ω.eval η) (e.eval η) (S.eval η) (a.eval η) (b.eval η) (c.eval η) := by
  simp only [formula_m, holds_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessBoundedMultiplication.formula_l,
    PowerlessBoundedAddition.formula_l, SecondOrderObjectSyntax.member_m,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem instance_l (K : source_coding_l hℳ) {S : type_l hℳ}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega S)
    (i j : SecondOrderModel.num_l ℳ) (c : type_l hℳ) :
    holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val S (numberCode_l K i).val (numberCode_l K j).val c ↔
        c = (numberCode_l K (SecondOrderPairing.value_l i j)).val := by
  classical
  constructor
  · rintro (⟨hLt, q, _, hSquare, hAdd⟩ | ⟨hLt, q, _, hSquare, r, _, hAdd₁, hAdd₂⟩)
    · have hLt' := (numberCode_mem_iff_lt_l K i j).mp hLt
      have hQ := (PowerlessBoundedMultiplication.instance_l K hS j j q).mp hSquare
      rw [hQ] at hAdd
      have hC := (PowerlessBoundedAddition.instance_l K hS (SecondOrderModel.mul_l j j) i c).mp hAdd
      simpa only [SecondOrderPairing.value_l, if_pos hLt'] using hC
    · have hLt' : ¬SecondOrderOrder.lt_l i j := fun h => hLt ((numberCode_mem_iff_lt_l K i j).mpr h)
      have hQ := (PowerlessBoundedMultiplication.instance_l K hS i i q).mp hSquare
      rw [hQ] at hAdd₁
      have hR := (PowerlessBoundedAddition.instance_l K hS (SecondOrderModel.mul_l i i) i r).mp hAdd₁
      rw [hR] at hAdd₂
      have hC := (PowerlessBoundedAddition.instance_l K hS
        (SecondOrderModel.add_l (SecondOrderModel.mul_l i i) i) j c).mp hAdd₂
      simpa only [SecondOrderPairing.value_l, if_neg hLt'] using hC
  · intro hc
    by_cases hLt : SecondOrderOrder.lt_l i j
    · refine Or.inl ⟨(numberCode_mem_iff_lt_l K i j).mpr hLt,
        (numberCode_l K (SecondOrderModel.mul_l j j)).val,
        (numberCode_l K (SecondOrderModel.mul_l j j)).property,
        (PowerlessBoundedMultiplication.instance_l K hS j j _).mpr rfl, ?_⟩
      apply (PowerlessBoundedAddition.instance_l K hS (SecondOrderModel.mul_l j j) i c).mpr
      simpa only [SecondOrderPairing.value_l, if_pos hLt] using hc
    · refine Or.inr ⟨(fun h => hLt ((numberCode_mem_iff_lt_l K i j).mp h)),
        (numberCode_l K (SecondOrderModel.mul_l i i)).val,
        (numberCode_l K (SecondOrderModel.mul_l i i)).property,
        (PowerlessBoundedMultiplication.instance_l K hS i i _).mpr rfl,
        (numberCode_l K (SecondOrderModel.add_l (SecondOrderModel.mul_l i i) i)).val,
        (numberCode_l K (SecondOrderModel.add_l (SecondOrderModel.mul_l i i) i)).property,
        (PowerlessBoundedAddition.instance_l K hS (SecondOrderModel.mul_l i i) i _).mpr rfl, ?_⟩
      apply (PowerlessBoundedAddition.instance_l K hS (SecondOrderModel.add_l (SecondOrderModel.mul_l i i) i) j c).mpr
      simpa only [SecondOrderPairing.value_l, if_neg hLt] using hc

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundedNumericPairing
