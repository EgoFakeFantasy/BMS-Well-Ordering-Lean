import BMSConstructibleBridge.SecondOrderMemberFunctionPullback
import BMSConstructibleBridge.SecondOrderFunctionProperties
import BMSConstructibleBridge.SecondOrderAssignmentCongruence
import BMSConstructibleBridge.SecondOrderMinimum
import BMSConstructibleBridge.SecondOrderFiniteEnumerationRoots

/-! # 任意原商有限函数的实际参数赋值

先沿母集枚举拉回函数，再用模型内部数值最小元选择代表，最后编码有限
函数图。没有选择集合族或建立宿主见证函数；函数和内部长度均可非标准。
满射函数的精确值域因而成为可送入原 Def 的实际赋值值域。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberFiniteFunctionAssignment

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)
open SecondOrderSequenceSyntax (read_l)
open SecondOrderQuotient (mem_l)
open PowerlessBMSQuotientCoding

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
  {hℳ : Theory.Models ℳ theory_m}

theorem exists_l (K : source_coding_l hℳ) (A : SecondOrderGraph.code_l ℳ)
    (a : num_l ℳ) (ha : relation_l A.real a A.root) {E : set_l ℳ}
    (hE : SecondOrderBinaryPowers.spec_l E) (n : num_l ℳ)
    {f Y : SecondOrderQuotient.type_l hℳ}
    (hf : SecondOrderFunctionObjects.map_l hℳ f (numberCode_l K n).val Y)
    (hY : ∀ y, mem_l hℳ y Y → mem_l hℳ y (SecondOrderQuotient.mk_l hℳ A)) :
    ∃ c, SecondOrderAssignmentSyntax.valid_l E c n ∧ ∀ i j, read_l E c i j →
      SecondOrderFunctionObjects.value_l hℳ f (numberCode_l K i).val
        (SecondOrderMemberStructure.value_l hℳ A a ha j).val := by
  classical
  obtain ⟨J, hJ⟩ := SecondOrderMemberFunctionPullback.exists_l K A a ha f
  have hTotal : ∀ i, SecondOrderOrder.lt_l i n → ∃ j, relation_l J i j := by
    intro i hi
    obtain ⟨y, hy, _⟩ := hf.2 (numberCode_l K i).val ((numberCode_mem_iff_lt_l K i n).mpr hi)
    obtain ⟨j, hj⟩ := SecondOrderMemberStructure.surjective_l hℳ A a ha ⟨y, hY y hy.1⟩
    refine ⟨j, (hJ i j).mpr ?_⟩
    have hj' := congrArg Subtype.val hj
    rw [hj']
    exact hy.2
  let ψ : Formula signature_m [] [.num, .num, .num, .set] :=
    .disj (.conj (PrimitiveFormulas.lt_m (.fvar .here) (.fvar (.there (.there .here))))
      (GraphSyntax.edge_m (.fvar (.there (.there (.there .here)))) (.fvar .here) (.fvar (.there .here))))
      (.conj (.neg (PrimitiveFormulas.lt_m (.fvar .here) (.fvar (.there (.there .here)))))
        (.equal (.fvar (.there .here)) (numeral_m 0)))
  obtain ⟨L, hL⟩ := SecondOrderRelations.comprehension_l hℳ ψ (pure_language_m _ rfl)
    (((Env.empty (M := ℳ)).pushFree J).pushFree n)
  have hL' i j : relation_l L i j ↔
      (SecondOrderOrder.lt_l i n ∧ relation_l J i j) ∨
        (¬SecondOrderOrder.lt_l i n ∧ j = zero_l ℳ) := by
    refine (hL i j).trans ?_
    simp only [ψ, Formula.satisfies, SecondOrderPairing.edge_l, SecondOrderOrder.formula_l]
    rfl
  obtain ⟨B, hB, hBL⟩ := SecondOrderMinimum.choice_l hℳ L (fun i => by
    by_cases hi : SecondOrderOrder.lt_l i n
    · obtain ⟨j, hj⟩ := hTotal i hi
      exact ⟨j, (hL' i j).mpr (Or.inl ⟨hi, hj⟩)⟩
    · exact ⟨zero_l ℳ, (hL' i _).mpr (Or.inr ⟨hi, rfl⟩)⟩)
  obtain ⟨c, hc, hRead⟩ := SecondOrderAssignment.encode_l hℳ hE B n (fun i _ => hB i)
  refine ⟨c, (SecondOrderAssignmentCongruence.valid_iff_l hE c n).mpr hc, ?_⟩
  intro i j hij
  have h := (hRead i j).mp ((SecondOrderSequenceSyntax.read_eq_l hE c i j).mp hij)
  rcases (hL' i j).mp (hBL i j h.2) with hJij | hNot
  · exact (hJ i j).mp hJij.2
  · exact False.elim (hNot.1 h.1)

/-- 保留全商满射条件，得到一般有限集合与内部赋值值域的精确对应。 -/
theorem range_l (K : source_coding_l hℳ) (A : SecondOrderGraph.code_l ℳ)
    (a : num_l ℳ) (ha : relation_l A.real a A.root) {E : set_l ℳ}
    (hE : SecondOrderBinaryPowers.spec_l E) (n : num_l ℳ)
    {f Y : SecondOrderQuotient.type_l hℳ}
    (hf : SecondOrderFunctionObjects.map_l hℳ f (numberCode_l K n).val Y)
    (hCover : ∀ y, mem_l hℳ y Y → ∃ x, mem_l hℳ x (numberCode_l K n).val ∧
      SecondOrderFunctionObjects.value_l hℳ f x y)
    (hY : ∀ y, mem_l hℳ y Y → mem_l hℳ y (SecondOrderQuotient.mk_l hℳ A)) :
    ∃ c, SecondOrderAssignmentSyntax.valid_l E c n ∧ ∀ x, mem_l hℳ x Y ↔
      ∃ i j, SecondOrderOrder.lt_l i n ∧ read_l E c i j ∧
        x = (SecondOrderMemberStructure.value_l hℳ A a ha j).val := by
  obtain ⟨c, hc, hValue⟩ := exists_l K A a ha hE n hf hY
  refine ⟨c, hc, fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨v, hv, hvx⟩ := hCover x hx
    obtain ⟨i, hi, hvi⟩ := SecondOrderFiniteEnumerationRoots.member_number_l K n v hv
    rw [← hvi] at hvx
    obtain ⟨j, hj, _⟩ := hc.1 i hi
    exact ⟨i, j, hi, hj, SecondOrderFunctionProperties.value_unique_l hℳ hf hvx (hValue i j hj)⟩
  · rintro ⟨i, j, _, hj, rfl⟩
    exact (SecondOrderFunctionProperties.value_mem_l hℳ hf (hValue i j hj)).2

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberFiniteFunctionAssignment
