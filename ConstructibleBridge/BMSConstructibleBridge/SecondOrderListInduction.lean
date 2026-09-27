import BMSConstructibleBridge.SecondOrderProgramListCode
import BMSConstructibleBridge.SecondOrderMinimum

/-!
# 实际公式上的内部强归纳与列表归纳

只对原语言公式所定义的性质归纳。反例由该公式的否定经理解形成内部集合，再用
已证模型内部最小元原理；这不是模型数序的外部良基性。原列表的尾码严格小于非空码，
因此同一原理给出覆盖所有内部列表码的零／非空构造归纳规则。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderListInduction

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderProgramListCode

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 实际公式定义的性质可作内部强归纳；公式、语言证据和参数环境均不可省略。 -/
theorem strong_induct_l (hℳ : Theory.Models ℳ theory_m) {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: Δ)) (hφ : language_m φ = true) (η : Env ℳ [] Δ)
    (P : num_l ℳ → Prop) (hP : ∀ n, Formula.satisfies (η.pushFree n) φ ↔ P n)
    (hstep : ∀ n, (∀ k, SecondOrderOrder.lt_l k n → P k) → P n) : ∀ n, P n := by
  classical
  intro n
  by_contra hn
  obtain ⟨X, hX⟩ := comprehension_l hℳ (.neg φ) hφ η
  have hcounter (k : num_l ℳ) : mem_l k X ↔ ¬P k := (hX k).trans (not_congr (hP k))
  obtain ⟨k, hk, hmin⟩ := SecondOrderMinimum.exists_l hℳ X ⟨n, (hcounter n).mpr hn⟩
  apply (hcounter k).mp hk
  apply hstep k
  intro j hj
  by_contra hbad
  exact hmin j hj ((hcounter j).mpr hbad)

/-- 给定内部界以下的强归纳。最小反例不晚于已知的界内反例，故不需要为
原公式重新编码一个有界版本，也不要求界外满足归纳步。 -/
theorem strong_induct_below_l (hℳ : Theory.Models ℳ theory_m)
    {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: Δ)) (hφ : language_m φ = true) (η : Env ℳ [] Δ)
    (P : num_l ℳ → Prop) (hP : ∀ n, Formula.satisfies (η.pushFree n) φ ↔ P n)
    (bound : num_l ℳ)
    (hstep : ∀ n, SecondOrderOrder.lt_l n bound →
      (∀ k, SecondOrderOrder.lt_l k n → P k) → P n) :
    ∀ n, SecondOrderOrder.lt_l n bound → P n := by
  classical
  intro n hnBound
  by_contra hn
  obtain ⟨X, hX⟩ := comprehension_l hℳ (.neg φ) hφ η
  have hcounter (k : num_l ℳ) : mem_l k X ↔ ¬P k := (hX k).trans (not_congr (hP k))
  obtain ⟨k, hk, hmin⟩ := SecondOrderMinimum.exists_l hℳ X ⟨n, (hcounter n).mpr hn⟩
  have hkBound : SecondOrderOrder.lt_l k bound := by
    rcases SecondOrderOrder.trichotomy_l hℳ k n with hkn | rfl | hnk
    · exact SecondOrderOrder.trans_l hℳ hkn hnBound
    · exact hnBound
    · exact False.elim (hmin n hnk ((hcounter n).mpr hn))
  apply (hcounter k).mp hk
  apply hstep k hkBound
  intro j hj
  by_contra hbad
  exact hmin j hj ((hcounter j).mpr hbad)

/-- 原列表码的内部结构归纳，不先把内部列表外部解码为有限列表。 -/
theorem list_induct_l (hℳ : Theory.Models ℳ theory_m) {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: Δ)) (hφ : language_m φ = true) (η : Env ℳ [] Δ)
    (P : num_l ℳ → Prop) (hP : ∀ n, Formula.satisfies (η.pushFree n) φ ↔ P n)
    (hzero : P (zero_l ℳ)) (hcons : ∀ a t, P t → P (succ_l (value_l a t))) : ∀ n, P n := by
  apply strong_induct_l hℳ φ hφ η P hP
  intro n ih
  rcases predecessor_l hℳ n with rfl | ⟨p, rfl⟩
  · exact hzero
  · obtain ⟨a, t, rfl⟩ := SecondOrderUnpairing.surjective_l hℳ p
    exact hcons a t (ih t (coordinates_lt_cons_l hℳ a t).2)

#print axioms strong_induct_l
#print axioms strong_induct_below_l
#print axioms list_induct_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderListInduction
