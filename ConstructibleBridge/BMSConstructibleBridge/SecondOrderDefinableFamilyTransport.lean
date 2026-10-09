import BMSConstructibleBridge.SecondOrderEvaluationTransport
import BMSConstructibleBridge.SecondOrderAssignmentTransport
import BMSConstructibleBridge.SecondOrderLegalFormulaIndex

/-!
# 合法内部定义切片在两套数域呈现间的双向迁移

量词域为全部内部数；关系 K 双向全域且保持两种原子真值。内部参数赋值
重新编码后，同一合法公式在两套呈现中定义同一对应切片。输出索引可以不同，
不能误要求逐码相等。这里只提供呈现迁移证书，尚不是纯集合 Def 对象定理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDefinableFamilyTransport

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)
open SecondOrderAssignmentSyntax (valid_l)
open SecondOrderRelatedAssignments (related_l)
open SecondOrderDefinableFamily (index_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

structure correspondence_l (E D D' K Q Q' R R' T U F G : set_l ℳ) : Prop where
  powers : SecondOrderBinaryPowers.spec_l E
  domain : ∀ x, mem_l x D
  domain' : ∀ x, mem_l x D'
  left_total : ∀ x, ∃ y, relation_l K x y
  right_total : ∀ y, ∃ x, relation_l K x y
  equality : SecondOrderEvaluationTransport.atoms_l K Q Q'
  membership : SecondOrderEvaluationTransport.atoms_l K R R'
  evaluation : SecondOrderEvaluationEquations.spec_l E D Q R T
  evaluation' : SecondOrderEvaluationEquations.spec_l E D' Q' R' U
  family : SecondOrderDefinableFamily.spec_l E D T F
  family' : SecondOrderDefinableFamily.spec_l E D' U G

variable (hℳ : Theory.Models ℳ theory_m) {E D D' K Q Q' R R' T U F G : set_l ℳ}
  (C : correspondence_l E D D' K Q Q' R R' T U F G)

include hℳ C

theorem row_l (p l c d : num_l ℳ) (hc : valid_l E c l) (hd : valid_l E d l)
    (h : related_l E K c d) (x y : num_l ℳ) (hxy : relation_l K x y) :
    relation_l F (index_l p l c) x ↔ relation_l G (index_l p l d) y := by
  rw [SecondOrderDefinableFamily.row_index_l hℳ E D T F C.family,
    SecondOrderDefinableFamily.row_index_l hℳ E D' U G C.family',
    and_iff_right (C.domain x), and_iff_right (C.domain' y), and_iff_right hc, and_iff_right hd]
  have hP := SecondOrderEvaluationTransport.transport_l hℳ C.powers D D' K Q Q' R R' T U
    (fun x _ => by obtain ⟨y, hxy⟩ := C.left_total x; exact ⟨y, C.domain' y, hxy⟩)
    (fun y _ => by obtain ⟨x, hxy⟩ := C.right_total y; exact ⟨x, C.domain x, hxy⟩)
    C.equality C.membership C.evaluation C.evaluation' p
  constructor
  · rintro ⟨a, ha, hT⟩
    obtain ⟨b, hb⟩ := SecondOrderAssignmentCongruence.extension_exists_l hℳ C.powers d l y hd
    have hAB := SecondOrderRelatedAssignments.extension_l hℳ E K l c d a b x y h ha hb hxy
    exact ⟨b, hb, (hP _ _ _ ha.1 hb.1 hAB).mp hT⟩
  · rintro ⟨b, hb, hU⟩
    obtain ⟨a, ha⟩ := SecondOrderAssignmentCongruence.extension_exists_l hℳ C.powers c l x hc
    have hAB := SecondOrderRelatedAssignments.extension_l hℳ E K l c d a b x y h ha hb hxy
    exact ⟨a, ha, (hP _ _ _ ha.1 hb.1 hAB).mpr hU⟩

theorem left_l (V : set_l ℳ) (i : num_l ℳ) (hi : SecondOrderLegalFormulaIndex.spec_l V E i) :
    ∃ j, SecondOrderLegalFormulaIndex.spec_l V E j ∧
      ∀ x y, relation_l K x y → (relation_l F i x ↔ relation_l G j y) := by
  obtain ⟨p, l, c, rfl, hc, hV⟩ := hi
  obtain ⟨d, hd, h⟩ := SecondOrderAssignmentTransport.exists_l hℳ C.powers K C.left_total c l hc
  exact ⟨index_l p l d, ⟨p, l, d, rfl, hd, hV⟩, row_l hℳ C p l c d hc hd h⟩

theorem right_l (V : set_l ℳ) (j : num_l ℳ) (hj : SecondOrderLegalFormulaIndex.spec_l V E j) :
    ∃ i, SecondOrderLegalFormulaIndex.spec_l V E i ∧
      ∀ x y, relation_l K x y → (relation_l F i x ↔ relation_l G j y) := by
  obtain ⟨p, l, d, rfl, hd, hV⟩ := hj
  obtain ⟨c, hc, h⟩ := SecondOrderAssignmentTransport.exists_reverse_l hℳ C.powers K C.right_total d l hd
  exact ⟨index_l p l c, ⟨p, l, c, rfl, hc, hV⟩, row_l hℳ C p l c d hc hd h⟩

#print axioms left_l
#print axioms right_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDefinableFamilyTransport
