import BMSConstructibleBridge.SecondOrderLegalMemberCollection

/-!
# 合法定义切片收集的全数域精确成员规格

把母根子节点上的规格提升到全部正规化数值代表。全部内部索引的切片
对同一成员的不同代表不变，不只对编译自外部公式的切片成立。
这是呈现的精确性辅助定理，纯集合 Def 公式仍需另行封装。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderLegalMemberExact

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
  (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
  (a : num_l ℳ) (ha : relation_l A.real a A.root)
  {V E D Q R T F : set_l ℳ} {H : SecondOrderGraph.code_l ℳ}
  (P : SecondOrderLegalMemberCollection.presentation_l hℳ A a ha V E D Q R T F H)

include P

theorem respect_l (i n m : num_l ℳ)
    (h : (SecondOrderMemberStructure.value_l hℳ A a ha n).val =
      (SecondOrderMemberStructure.value_l hℳ A a ha m).val) :
    relation_l F i n ↔ relation_l F i m := by
  apply SecondOrderDefinableRespect.row_l hℳ P.powers D Q R T F
    (fun x => (P.equality x x).mpr rfl) _ _ P.evaluation P.family i n m (P.domain n) (P.domain m)
    ((P.equality n m).mpr (Subtype.ext h))
  · intro x y n m hx hy
    rw [P.equality] at hx hy
    rw [P.equality x y, P.equality n m]
    rw [hx, hy]
  · intro x y n m hx hy
    have hx' := congrArg Subtype.val ((P.equality x n).mp hx)
    have hy' := congrArg Subtype.val ((P.equality y m).mp hy)
    rw [P.membership, P.membership]
    change SecondOrderQuotient.mem_l hℳ
      (SecondOrderMemberStructure.value_l hℳ A a ha x).val
      (SecondOrderMemberStructure.value_l hℳ A a ha y).val ↔ _
    rw [hx', hy']
    rfl

theorem normalized_l (i n : num_l ℳ) : relation_l F i n ↔
    relation_l F i (SecondOrderMemberNormalizer.value_l A.real A.root a n) := by
  apply respect_l hℳ A a ha P i n _
  change SecondOrderQuotient.mk_l hℳ (SecondOrderMemberNormalizer.code_l hℳ A a ha n) =
    SecondOrderQuotient.mk_l hℳ (SecondOrderMemberNormalizer.code_l hℳ A a ha
      (SecondOrderMemberNormalizer.value_l A.real A.root a n))
  rw [SecondOrderMemberNormalizer.code_fixed_l hℳ A a ha _
    (SecondOrderMemberNormalizer.member_l A.real A.root a ha n)]
  rfl

theorem slice_l (i : num_l ℳ) (C : SecondOrderGraph.code_l ℳ) :
    (∃ n, relation_l A.real n A.root ∧ relation_l F i n ∧
      SecondOrderBisimulation.eq_l C.real A.real C.root n) ↔
      ∃ n, relation_l F i n ∧ SecondOrderQuotient.mk_l hℳ C =
        (SecondOrderMemberStructure.value_l hℳ A a ha n).val := by
  constructor
  · rintro ⟨n, hn, hF, hC⟩
    refine ⟨n, hF, ?_⟩
    change SecondOrderQuotient.mk_l hℳ C =
      SecondOrderQuotient.mk_l hℳ (SecondOrderMemberNormalizer.code_l hℳ A a ha n)
    rw [SecondOrderMemberNormalizer.code_fixed_l hℳ A a ha n hn]
    exact (SecondOrderQuotient.eq_iff_l hℳ _ _).mpr hC
  · rintro ⟨n, hF, hC⟩
    have hn := SecondOrderMemberNormalizer.member_l A.real A.root a ha n
    refine ⟨_, hn, (normalized_l hℳ A a ha P i n).mp hF, ?_⟩
    exact (SecondOrderQuotient.eq_iff_l hℳ C
      (SecondOrderMemberNormalizer.code_l hℳ A a ha n)).mp hC

theorem collection_l (B : SecondOrderGraph.code_l ℳ) : SecondOrderGraph.mem_l B H ↔
    ∃ i, SecondOrderLegalFormulaIndex.spec_l V E i ∧ ∀ C, SecondOrderGraph.mem_l C B ↔
      ∃ n, relation_l F i n ∧ SecondOrderQuotient.mk_l hℳ C =
        (SecondOrderMemberStructure.value_l hℳ A a ha n).val := by
  refine (P.collection B).trans (exists_congr (fun i => and_congr Iff.rfl ?_))
  apply forall_congr'
  intro C
  exact iff_congr Iff.rfl (slice_l hℳ A a ha P i C)

#print axioms respect_l
#print axioms collection_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderLegalMemberExact
