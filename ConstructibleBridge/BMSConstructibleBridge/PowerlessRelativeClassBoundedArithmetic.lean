import BMSConstructibleBridge.PowerlessBoundedMultiplication
import BMSConstructibleBridge.PowerlessRelativeClassMultiplicationAbsolute
import BMSConstructibleBridge.PowerlessRelativeClassFiniteSequencesDerives

/-! # 有界运算检查式与相对类原算术关系对应

同一个 S 必须在原商中包含所有有限自然数序列；类内有限序列规格本身
不直接等价于这个环境全称断言。使用已构造 S 的双重规格，不隐藏此义务。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassBoundedArithmetic

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem addition_absolute_l (ω e S a b c : type_l hℳ B) :
    PowerlessBoundedAddition.holds_l (𝒩 := structure_l hℳ B hBase) ω e S a b c ↔
      PowerlessBoundedAddition.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
        ω.val e.val S.val a.val b.val c.val := by
  let η : Env (structure_l hℳ B hBase) [] [.set, .set, .set, .set, .set, .set] :=
    ((((((Env.empty).pushFree c).pushFree b).pushFree a).pushFree S).pushFree e).pushFree ω
  let w : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar .here
  let z : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let s : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let x : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let y : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  let t : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there .here)))))
  exact (PowerlessBoundedAddition.formula_l η w z s x y t).symm.trans
    ((PowerlessRelativeClassBounded.formula_l (hBase := hBase)
      (PowerlessBoundedAddition.delta_l w z s x y t) η).trans
      (PowerlessBoundedAddition.formula_l (PowerlessRelativeClassRelativization.env_l η) w z s x y t))

theorem multiplication_absolute_l (ω e S a b c : type_l hℳ B) :
    PowerlessBoundedMultiplication.holds_l (𝒩 := structure_l hℳ B hBase) ω e S a b c ↔
      PowerlessBoundedMultiplication.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
        ω.val e.val S.val a.val b.val c.val := by
  let η : Env (structure_l hℳ B hBase) [] [.set, .set, .set, .set, .set, .set] :=
    ((((((Env.empty).pushFree c).pushFree b).pushFree a).pushFree S).pushFree e).pushFree ω
  let w : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar .here
  let z : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let s : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let x : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let y : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  let t : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there .here)))))
  exact (PowerlessBoundedMultiplication.formula_l η w z s x y t).symm.trans
    ((PowerlessRelativeClassBounded.formula_l (hBase := hBase)
      (PowerlessBoundedMultiplication.delta_l w z s x y t) η).trans
      (PowerlessBoundedMultiplication.formula_l (PowerlessRelativeClassRelativization.env_l η) w z s x y t))

theorem addition_l (K : source_coding_l hℳ) {i j : SecondOrderModel.num_l ℳ}
    {ω e S a b c : type_l hℳ B}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega S.val)
    (hω : ω.val = K.omega) (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (ha : a.val = (numberCode_l K i).val) (hb : b.val = (numberCode_l K j).val) :
    PowerlessBoundedAddition.holds_l (𝒩 := structure_l hℳ B hBase) ω e S a b c ↔
      PowerlessAddition.addition_l (ℳ := structure_l hℳ B hBase) ω e a b c := by
  have hAbs := addition_absolute_l (hBase := hBase) ω e S a b c
  rw [hω, he, ha, hb] at hAbs
  exact hAbs.trans ((PowerlessBoundedAddition.instance_l K hS i j c.val).trans
    (PowerlessRelativeClassAdditionAbsolute.instance_l K hω he ha hb).symm)

theorem multiplication_l (K : source_coding_l hℳ) {i j : SecondOrderModel.num_l ℳ}
    {ω e S a b c : type_l hℳ B}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega S.val)
    (hω : ω.val = K.omega) (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (ha : a.val = (numberCode_l K i).val) (hb : b.val = (numberCode_l K j).val) :
    PowerlessBoundedMultiplication.holds_l (𝒩 := structure_l hℳ B hBase) ω e S a b c ↔
      PowerlessMultiplication.multiplication_l (ℳ := structure_l hℳ B hBase) ω e a b c := by
  have hAbs := multiplication_absolute_l (hBase := hBase) ω e S a b c
  rw [hω, he, ha, hb] at hAbs
  exact hAbs.trans ((PowerlessBoundedMultiplication.instance_l K hS i j c.val).trans
    (PowerlessRelativeClassMultiplicationAbsolute.instance_l K hω he ha hb).symm)

#print axioms addition_l
#print axioms multiplication_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassBoundedArithmetic
