import BMSConstructibleBridge.SecondOrderLegalMemberCollection
import BMSConstructibleBridge.SecondOrderDefinableFamilyTransport

/-!
# 同一商集合的两套成员呈现具有内部对应关系

正规化关系和最大内部双模拟构造 K；两个图只须表示同一个母集。K 双向
全域，并保持实际相等与成员图，从而填满全部内部定义切片迁移的前提。
合法性与幂图在此使用共同参数；整体 Def 对象仍须封装并证明唯一性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberCorrespondence

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def formula_m : Formula signature_m [] [.num, .num, .set, .set, .set] :=
  .existsE .num <| .existsE .num <|
    .conj (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.fvar .here) (.bvar (.there .here))) <|
      .conj (GraphSyntax.edge_m (.fvar (.there (.there (.there .here)))) (.fvar (.there .here)) (.bvar .here))
        (GraphSyntax.edge_m (.fvar (.there (.there (.there (.there .here)))))
          (.bvar (.there .here)) (.bvar .here))

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (A B : SecondOrderGraph.code_l ℳ)
    (a b : num_l ℳ) (ha : relation_l A.real a A.root) (hb : relation_l B.real b B.root) :
    ∃ K : set_l ℳ, ∀ n m, relation_l K n m ↔
      (SecondOrderMemberStructure.value_l hℳ A a ha n).val =
        (SecondOrderMemberStructure.value_l hℳ B b hb m).val := by
  obtain ⟨N, hN⟩ := SecondOrderMemberNormalizer.exists_l hℳ A.real A.root a
  obtain ⟨N', hN'⟩ := SecondOrderMemberNormalizer.exists_l hℳ B.real B.root b
  obtain ⟨P, hP⟩ := SecondOrderBisimulation.maximum_l hℳ A.real B.real
  obtain ⟨K, hK⟩ := SecondOrderRelations.comprehension_l hℳ formula_m (pure_language_m _ rfl)
    ((((Env.empty (M := ℳ)).pushFree P).pushFree N').pushFree N)
  refine ⟨K, fun n m => (hK n m).trans ?_⟩
  simp only [formula_m, Formula.satisfies, SecondOrderPairing.edge_l]
  change (∃ x y, relation_l N n x ∧ relation_l N' m y ∧ relation_l P x y) ↔ _
  simp only [hN, hN', hP]
  constructor
  · rintro ⟨x, y, rfl, rfl, hxy⟩
    exact (SecondOrderQuotient.eq_iff_l hℳ _ _).mpr hxy
  · intro h
    exact ⟨_, _, rfl, rfl, (SecondOrderQuotient.eq_iff_l hℳ _ _).mp h⟩

theorem family_l (hℳ : Theory.Models ℳ theory_m) (A B : SecondOrderGraph.code_l ℳ)
    (a b : num_l ℳ) (ha : relation_l A.real a A.root) (hb : relation_l B.real b B.root)
    (hAB : SecondOrderQuotient.mk_l hℳ A = SecondOrderQuotient.mk_l hℳ B)
    (V E D D' Q Q' R R' T U F G : set_l ℳ) (H J : SecondOrderGraph.code_l ℳ)
    (hA : SecondOrderLegalMemberCollection.presentation_l hℳ A a ha V E D Q R T F H)
    (hB : SecondOrderLegalMemberCollection.presentation_l hℳ B b hb V E D' Q' R' U G J) :
    ∃ K, (∀ n m, relation_l K n m ↔
      (SecondOrderMemberStructure.value_l hℳ A a ha n).val =
        (SecondOrderMemberStructure.value_l hℳ B b hb m).val) ∧
      SecondOrderDefinableFamilyTransport.correspondence_l E D D' K Q Q' R R' T U F G := by
  obtain ⟨K, hK⟩ := exists_l hℳ A B a b ha hb
  refine ⟨K, hK, ⟨hA.powers, hA.domain, hB.domain, ?_, ?_, ?_, ?_,
    hA.evaluation, hB.evaluation, hA.family, hB.family⟩⟩
  · intro n
    have hMem : SecondOrderQuotient.mem_l hℳ
        (SecondOrderMemberStructure.value_l hℳ A a ha n).val (SecondOrderQuotient.mk_l hℳ B) :=
      (congrArg (SecondOrderQuotient.mem_l hℳ
        (SecondOrderMemberStructure.value_l hℳ A a ha n).val) hAB) ▸
          (SecondOrderMemberStructure.value_l hℳ A a ha n).property
    obtain ⟨m, hm⟩ := SecondOrderMemberStructure.surjective_l hℳ B b hb ⟨_, hMem⟩
    exact ⟨m, (hK n m).mpr (congrArg Subtype.val hm).symm⟩
  · intro m
    have hMem : SecondOrderQuotient.mem_l hℳ
        (SecondOrderMemberStructure.value_l hℳ B b hb m).val (SecondOrderQuotient.mk_l hℳ A) :=
      (congrArg (SecondOrderQuotient.mem_l hℳ
        (SecondOrderMemberStructure.value_l hℳ B b hb m).val) hAB.symm) ▸
          (SecondOrderMemberStructure.value_l hℳ B b hb m).property
    obtain ⟨n, hn⟩ := SecondOrderMemberStructure.surjective_l hℳ A a ha ⟨_, hMem⟩
    exact ⟨n, (hK n m).mpr (congrArg Subtype.val hn)⟩
  · intro x y n m hx hy
    rw [hA.equality, hB.equality]
    have hx' := (hK x n).mp hx
    have hy' := (hK y m).mp hy
    constructor
    · intro h
      exact Subtype.ext (hx'.symm.trans ((congrArg Subtype.val h).trans hy'))
    · intro h
      exact Subtype.ext (hx'.trans ((congrArg Subtype.val h).trans hy'.symm))
  · intro x y n m hx hy
    rw [hA.membership, hB.membership]
    change SecondOrderQuotient.mem_l hℳ
      (SecondOrderMemberStructure.value_l hℳ A a ha x).val
      (SecondOrderMemberStructure.value_l hℳ A a ha y).val ↔ _
    rw [(hK x n).mp hx, (hK y m).mp hy]
    rfl

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberCorrespondence
