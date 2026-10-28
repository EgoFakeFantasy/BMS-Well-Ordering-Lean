import BMSConstructibleBridge.SecondOrderComparisonDecodeSyntax

/-! # 纯解码公式逐内部数读取原比较实数

ω 子集代表由逐数成员规格约束，配数使用原关系实数的配数。
自然数码满射只在 Prop 中逐点使用；不构造逆枚举或选择实数呈现。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonDecodeReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderComparisonDecodeSyntax

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem query_l (K : source_coding_l hℳ)
    (A : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega) (R : SecondOrderModel.set_l ℳ)
    (hA : setRel_l K A R) (f x y : type_l hℳ) :
    SecondOrderComparisonDecodeSyntax.query_l (𝒩 := 𝒱) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val A.val f x y ↔
      ∃ i j, SecondOrderPairing.relation_l R i j ∧
        value_l (ℳ := 𝒱) f (numberCode_l K i).val x ∧
        value_l (ℳ := 𝒱) f (numberCode_l K j).val y := by
  let η : Env 𝒱 [] [.set, .set, .set, .set, .set, .set] :=
    ((((((Env.empty.pushFree f).pushFree A.val).pushFree
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val).pushFree K.omega).pushFree y).pushFree x)
  let w : Term ℒ [.set, .set] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let z : Term ℒ [.set, .set] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let Q : Term ℒ [.set, .set] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  let n : Term ℒ [.set, .set] [.set, .set, .set, .set, .set, .set] .set := .bvar (.there .here)
  let m : Term ℒ [.set, .set] [.set, .set, .set, .set, .set, .set] .set := .bvar .here
  have hEdge i j : (PowerlessMemberDefSyntax.edge_m w z Q n m).satisfies
      ((η.pushBound (numberCode_l K i).val).pushBound (numberCode_l K j).val) ↔
      SecondOrderPairing.relation_l R i j :=
    PowerlessMemberDefArithmeticSemantics.edge_formula_l K _ w z Q n m A R i j
      rfl rfl rfl rfl rfl hA
  have hQuery : SecondOrderComparisonDecodeSyntax.query_l (𝒩 := 𝒱) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val A.val f x y ↔
      ∃ i j, mem_l hℳ i K.omega ∧ mem_l hℳ j K.omega ∧
        value_l (ℳ := 𝒱) f i x ∧ value_l (ℳ := 𝒱) f j y ∧
        (PowerlessMemberDefSyntax.edge_m w z Q n m).satisfies ((η.pushBound i).pushBound j) := by
    simp only [SecondOrderComparisonDecodeSyntax.query_l, query_template_m,
      Formula.satisfies, SecondOrderObjectSyntax.member_m, value_formula_l,
      Arguments.eval, Term.eval]
    rfl
  rw [hQuery]
  constructor
  · rintro ⟨i, j, hi, hj, hix, hjy, hφ⟩
    obtain ⟨a, ha⟩ := numberCode_surjective_l K ⟨i, hi⟩
    obtain ⟨b, hb⟩ := numberCode_surjective_l K ⟨j, hj⟩
    have ha' : (numberCode_l K a).val = i := congrArg Subtype.val ha
    have hb' : (numberCode_l K b).val = j := congrArg Subtype.val hb
    rw [← ha'] at hix
    rw [← hb'] at hjy
    rw [← ha', ← hb'] at hφ
    exact ⟨a, b, (hEdge a b).mp hφ, hix, hjy⟩
  · rintro ⟨i, j, hij, hix, hjy⟩
    exact ⟨(numberCode_l K i).val, (numberCode_l K j).val,
      (numberCode_l K i).property, (numberCode_l K j).property, hix, hjy, (hEdge i j).mpr hij⟩

theorem graph_l (K : source_coding_l hℳ)
    (A : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega) (R : SecondOrderModel.set_l ℳ)
    (hA : setRel_l K A R) (C f P : type_l hℳ) :
    SecondOrderComparisonDecodeSyntax.graph_l (𝒩 := 𝒱) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val A.val f C P ↔
      SecondOrderComparisonDecode.graph_l K C f R P := by
  unfold SecondOrderComparisonDecodeSyntax.graph_l SecondOrderComparisonDecode.graph_l
    SecondOrderComparisonDecode.read_l
  apply forall_congr'
  intro p
  apply iff_congr Iff.rfl
  apply exists_congr
  intro x
  apply exists_congr
  intro y
  constructor
  · rintro ⟨hx, hy, h, hp⟩
    exact ⟨⟨hx, hy, (query_l K A R hA f x y).mp h⟩, hp⟩
  · rintro ⟨⟨hx, hy, h⟩, hp⟩
    exact ⟨hx, hy, (query_l K A R hA f x y).mpr h, hp⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonDecodeReading
