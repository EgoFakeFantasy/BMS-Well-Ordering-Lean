import BMSConstructibleBridge.SecondOrderTriangularArithmetic
import BMSConstructibleBridge.PowerlessBoundedMultiplication

/-! # 三角数关系的纯 Δ₀ 检查

用全有限 ω 值序列集界定乘法与倍增加法，全部中间数限于 ω。
在原商任意内部数根码上精确等于 2t=n(n+1)，不替换成平方分支配数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundedTriangular

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def formula_m {Γ Δ : SortContext ℒ} (ω e S n t : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up t)
  membershipLevyBound.boundedExists ω <|
    membershipLevyBound.boundedExists (up ω) <| .conj
      (PowerlessSuccessorBounded.formula_m (w n) (.bvar (.there .here))) <| .conj
        (PowerlessBoundedMultiplication.formula_m (w ω) (w e) (w S) (w n)
          (.bvar (.there .here)) (.bvar .here))
        (PowerlessBoundedAddition.formula_m (w ω) (w e) (w S) (w t) (w t) (.bvar .here))

theorem delta_l {Γ Δ : SortContext ℒ} (ω e S n t : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m ω e S n t) :=
  .bounded_exists ω (.bounded_exists (up ω) (.conj (PowerlessSuccessorBounded.delta_l _ _)
    (.conj (PowerlessBoundedMultiplication.delta_l _ _ _ _ _ _) (PowerlessBoundedAddition.delta_l _ _ _ _ _ _))))

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e S n t : carrier_l 𝒩) : Prop :=
  ∃ m, member_l 𝒩 m ω ∧ ∃ d, member_l 𝒩 d ω ∧
    PowerlessNatural.successor_l (ℳ := 𝒩) n m ∧
    PowerlessBoundedMultiplication.holds_l ω e S n m d ∧ PowerlessBoundedAddition.holds_l ω e S t t d

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e S n t : Term ℒ Γ Δ .set) :
    (formula_m ω e S n t).satisfies η ↔ holds_l (ω.eval η) (e.eval η) (S.eval η) (n.eval η) (t.eval η) := by
  simp only [formula_m, holds_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessSuccessorBounded.formula_l,
    PowerlessBoundedMultiplication.formula_l, PowerlessBoundedAddition.formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem instance_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} (K : source_coding_l hℳ) {S : type_l hℳ}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega S)
    (i j : SecondOrderModel.num_l ℳ) :
    holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val S (numberCode_l K i).val (numberCode_l K j).val ↔
      SecondOrderTriangularArithmetic.relation_l i j := by
  constructor
  · rintro ⟨m, _, d, _, hSucc, hMul, hAdd⟩
    have hm : m = (numberCode_l K (SecondOrderModel.succ_l i)).val :=
      PowerlessBMSQuotientRecursion.successor_unique_l (hM := hℳ)
        (a := (numberCode_l K i).val) hSucc (PowerlessBMSQuotientSuccessor.successor_l K i)
    rw [hm] at hMul
    have hdMul := (PowerlessBoundedMultiplication.instance_l K hS i (SecondOrderModel.succ_l i) d).mp hMul
    have hdAdd := (PowerlessBoundedAddition.instance_l K hS j j d).mp hAdd
    exact numberCode_injective_l K (Subtype.ext (hdAdd.symm.trans hdMul))
  · intro hRelation
    refine ⟨(numberCode_l K (SecondOrderModel.succ_l i)).val,
      (numberCode_l K (SecondOrderModel.succ_l i)).property,
      (numberCode_l K (SecondOrderModel.mul_l i (SecondOrderModel.succ_l i))).val,
      (numberCode_l K (SecondOrderModel.mul_l i (SecondOrderModel.succ_l i))).property,
      PowerlessBMSQuotientSuccessor.successor_l K i,
      (PowerlessBoundedMultiplication.instance_l K hS i (SecondOrderModel.succ_l i) _).mpr rfl, ?_⟩
    apply (PowerlessBoundedAddition.instance_l K hS j j _).mpr
    exact congrArg (fun q => (numberCode_l K q).val) hRelation.symm

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundedTriangular
