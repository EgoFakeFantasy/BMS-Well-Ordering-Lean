import BMSConstructibleBridge.SecondOrderMemberCorrespondence
import BMSConstructibleBridge.SecondOrderLegalMemberExact

/-!
# 非空集合的合法内部定义子集族与呈现无关

两张母图、首成员见证、求值参数及索引码均可不同。合法性和幂图由唯一性
对齐，再用内部参数换代表及双向切片迁移证明两套集合具有相同成员。
结论是实际图商对象相等；纯集合 Def AST 和该句的对象推导仍未在此提供。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderLegalMemberIndependence

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem common_l (hℳ : Theory.Models ℳ theory_m) (A B : SecondOrderGraph.code_l ℳ)
    (a b : num_l ℳ) (ha : relation_l A.real a A.root) (hb : relation_l B.real b B.root)
    (hAB : SecondOrderQuotient.mk_l hℳ A = SecondOrderQuotient.mk_l hℳ B)
    (V E D D' Q Q' R R' T U F G : set_l ℳ) (H J : SecondOrderGraph.code_l ℳ)
    (P : SecondOrderLegalMemberCollection.presentation_l hℳ A a ha V E D Q R T F H)
    (P' : SecondOrderLegalMemberCollection.presentation_l hℳ B b hb V E D' Q' R' U G J) :
    SecondOrderGraph.eq_l H J := by
  obtain ⟨K, hK, C⟩ := SecondOrderMemberCorrespondence.family_l hℳ A B a b ha hb hAB
    V E D D' Q Q' R R' T U F G H J P P'
  apply (SecondOrderGraph.ext_l hℳ H J).mpr
  intro Z
  rw [SecondOrderLegalMemberExact.collection_l hℳ A a ha P Z,
    SecondOrderLegalMemberExact.collection_l hℳ B b hb P' Z]
  constructor
  · rintro ⟨i, hi, hSlice⟩
    obtain ⟨j, hj, hRows⟩ := SecondOrderDefinableFamilyTransport.left_l hℳ C V i hi
    refine ⟨j, hj, fun W => (hSlice W).trans ?_⟩
    constructor
    · rintro ⟨n, hn, hW⟩
      obtain ⟨m, hnm⟩ := C.left_total n
      exact ⟨m, (hRows n m hnm).mp hn, hW.trans ((hK n m).mp hnm)⟩
    · rintro ⟨m, hm, hW⟩
      obtain ⟨n, hnm⟩ := C.right_total m
      exact ⟨n, (hRows n m hnm).mpr hm, hW.trans ((hK n m).mp hnm).symm⟩
  · rintro ⟨j, hj, hSlice⟩
    obtain ⟨i, hi, hRows⟩ := SecondOrderDefinableFamilyTransport.right_l hℳ C V j hj
    refine ⟨i, hi, fun W => (hSlice W).trans ?_⟩
    constructor
    · rintro ⟨m, hm, hW⟩
      obtain ⟨n, hnm⟩ := C.right_total m
      exact ⟨n, (hRows n m hnm).mpr hm, hW.trans ((hK n m).mp hnm).symm⟩
    · rintro ⟨n, hn, hW⟩
      obtain ⟨m, hnm⟩ := C.left_total n
      exact ⟨m, (hRows n m hnm).mp hn, hW.trans ((hK n m).mp hnm)⟩

/-- 去掉共同语法图与幂图前提；其余呈现参数均保持独立。 -/
theorem unique_l (hℳ : Theory.Models ℳ theory_m) (A B : SecondOrderGraph.code_l ℳ)
    (a b : num_l ℳ) (ha : relation_l A.real a A.root) (hb : relation_l B.real b B.root)
    (hAB : SecondOrderQuotient.mk_l hℳ A = SecondOrderQuotient.mk_l hℳ B)
    (V V' E E' D D' Q Q' R R' T U F G : set_l ℳ) (H J : SecondOrderGraph.code_l ℳ)
    (P : SecondOrderLegalMemberCollection.presentation_l hℳ A a ha V E D Q R T F H)
    (P' : SecondOrderLegalMemberCollection.presentation_l hℳ B b hb V' E' D' Q' R' U G J) :
    SecondOrderGraph.eq_l H J := by
  obtain ⟨W, _, hUnique⟩ := SecondOrderInternalFormulaSyntax.exists_l hℳ
  have hV : V' = V := (hUnique V' P'.formula_codes).trans (hUnique V P.formula_codes).symm
  subst V'
  have hE : E' = E := SecondOrderPowers.unique_l hℳ P'.powers P.powers
  subst E'
  exact common_l hℳ A B a b ha hb hAB V E D D' Q Q' R R' T U F G H J P P'

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderLegalMemberIndependence
