import BMSConstructibleBridge.SecondOrderTriangularMonotone
import BMSConstructibleBridge.SecondOrderTriangularPairing

/-! # 原三角配数的内部坐标单射性

第 s 条对角线的码严格小于 T(s+1)，相异对角线因此不相交。
同一对角线上先消去三角数，再消去第一坐标；全程保留原内部数域。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderTriangularInjective

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel SecondOrderNumbers
open SecondOrderTriangularArithmetic (relation_l)
open SecondOrderTriangularPairing (code_l code_m)
open SecondOrderOrder (lt_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem interval_l (hℳ : Theory.Models ℳ theory_m) {a b t v : num_l ℳ}
    (ht : relation_l (add_l a b) t) (hv : relation_l (succ_l (add_l a b)) v) :
    lt_l (add_l t a) v := by
  refine ⟨b, ?_⟩
  rw [add_assoc_l hℳ, add_succ_l hℳ]
  exact (SecondOrderTriangularArithmetic.successor_l hℳ ht hv).symm

theorem diagonal_l (hℳ : Theory.Models ℳ theory_m) {a b c d f g : num_l ℳ}
    (hc : code_l a b c) (hg : code_l d f g) (hSum : lt_l (add_l a b) (add_l d f)) : lt_l c g := by
  obtain ⟨t, ht, rfl⟩ := hc
  obtain ⟨v, hv, rfl⟩ := hg
  obtain ⟨q, hq⟩ := SecondOrderTriangularArithmetic.exists_l hℳ (succ_l (add_l a b))
  have hUpper := interval_l hℳ ht hq
  have hBelow : lt_l (add_l t a) v := by
    rcases SecondOrderTriangularMonotone.successor_lower_l hℳ hSum with hEq | hLt
    · have hqv := SecondOrderTriangularArithmetic.unique_l hℳ (hEq ▸ hq) hv
      exact hqv ▸ hUpper
    · exact SecondOrderOrder.trans_l hℳ hUpper (SecondOrderTriangularMonotone.monotone_l hℳ hq hv hLt)
  rcases SecondOrderTriangularPairing.addition_lower_l hℳ v d with hEq | hLt
  · exact hEq ▸ hBelow
  · exact SecondOrderOrder.trans_l hℳ hBelow hLt

theorem injective_l (hℳ : Theory.Models ℳ theory_m) {a b c d f : num_l ℳ}
    (hc : code_l a b c) (hd : code_l d f c) : a = d ∧ b = f := by
  rcases SecondOrderOrder.trichotomy_l hℳ (add_l a b) (add_l d f) with hLt | hEq | hLt
  · exact (SecondOrderOrder.irrefl_l hℳ c (diagonal_l hℳ hc hd hLt)).elim
  · obtain ⟨t, ht, hc⟩ := hc
    obtain ⟨v, hv, hd⟩ := hd
    have htv := SecondOrderTriangularArithmetic.unique_l hℳ (hEq ▸ ht) hv
    have ha : a = d := (add_cancel_l hℳ t a d).mp (by simpa only [htv] using hc.symm.trans hd)
    refine ⟨ha, (add_cancel_l hℳ d b f).mp ?_⟩
    simpa only [ha] using hEq
  · exact (SecondOrderOrder.irrefl_l hℳ c (diagonal_l hℳ hd hc hLt)).elim

def formula_m : Formula signature_m [] [.num, .num, .num, .num, .num] :=
  let a : Term signature_m [] [.num, .num, .num, .num, .num] .num := .fvar .here
  let b : Term signature_m [] [.num, .num, .num, .num, .num] .num := .fvar (.there .here)
  let c : Term signature_m [] [.num, .num, .num, .num, .num] .num := .fvar (.there (.there .here))
  let d : Term signature_m [] [.num, .num, .num, .num, .num] .num := .fvar (.there (.there (.there .here)))
  let f : Term signature_m [] [.num, .num, .num, .num, .num] .num := .fvar (.there (.there (.there (.there .here))))
  .imp (code_m a b c) (.imp (code_m d f c) (.conj (.equal a d) (.equal b f)))

def sentence_m : Sentence signature_m := Metatheory.Formula.forall_close formula_m

theorem derives_m : Derives theory_m [] sentence_m := by
  apply SecondOrderCompleteness.derives_m
  intro ℳ hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [formula_m, Formula.satisfies, SecondOrderTriangularPairing.formula_l, Term.eval]
  exact fun hc hd => injective_l hℳ hc hd

#print axioms injective_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderTriangularInjective
