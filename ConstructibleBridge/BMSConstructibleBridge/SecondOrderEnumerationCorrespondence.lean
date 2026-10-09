import BMSConstructibleBridge.SecondOrderMemberEnumeration
import BMSConstructibleBridge.SecondOrderGraphFormulaRelation
import BMSConstructibleBridge.SecondOrderObjectSyntax

/-!
# 任意实际成员枚举与正规化呈现的内部对应

枚举是商中的集合函数，不是抽取出的宿主函数。对应图直接通过纯公式理解
读取实际函数值，再与正规化图复合；全部存在见证保留在 Prop 中。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEnumerationCorrespondence

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)
open PowerlessBMSQuotientCoding SecondOrderFunctionObjects SecondOrderQuotient

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
  {hℳ : Theory.Models ℳ theory_m}

def composition_m : Formula signature_m [] [.num, .num, .set, .set] :=
  .existsE .num <| .conj
    (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.fvar (.there .here)) (.bvar .here))
    (GraphSyntax.edge_m (.fvar (.there (.there (.there .here)))) (.fvar .here) (.bvar .here))

theorem exists_l (C : source_coding_l hℳ) (f : type_l hℳ)
    (A : SecondOrderGraph.code_l ℳ) (a : num_l ℳ) (ha : relation_l A.real a A.root) :
    ∃ K : set_l ℳ, ∀ n m, relation_l K n m ↔
      value_l hℳ f (numberCode_l C n).val (SecondOrderMemberStructure.value_l hℳ A a ha m).val := by
  let φ : Formula ℒ [] [.set, .set, .set] :=
    SecondOrderObjectSyntax.value_m (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there .here))
  obtain ⟨L, hL⟩ := SecondOrderGraphFormulaRelation.exists_l hℳ φ
    ((Env.empty (M := structure_l hℳ)).pushFree f) C.less A.real
  obtain ⟨N, hN⟩ := SecondOrderMemberNormalizer.exists_l hℳ A.real A.root a
  obtain ⟨K, hK⟩ := SecondOrderRelations.comprehension_l hℳ composition_m (pure_language_m _ rfl)
    (((Env.empty (M := ℳ)).pushFree L).pushFree N)
  refine ⟨K, fun n m => (hK n m).trans ?_⟩
  have hRead (b : num_l ℳ) (hb : SecondOrderDomain.wf_l A.real b) :
      relation_l L n b ↔ value_l hℳ f (numberCode_l C n).val (mk_l hℳ ⟨A.real, b, hb⟩) := by
    exact (hL n b (SecondOrderNaturalGraph.wf_l hℳ C.less C.less_spec n) hb).trans
      (ThirdOrderSemantics.value_formula_l _ _ _ _)
  have hb := SecondOrderDomain.child_l hℳ A.real A.root _ A.wf
    (SecondOrderMemberNormalizer.member_l A.real A.root a ha m)
  simp only [composition_m, Formula.satisfies, SecondOrderPairing.edge_l]
  change (∃ b, relation_l N m b ∧ relation_l L n b) ↔ _
  simp only [hN]
  exact exists_eq_left.trans (hRead _ hb)

/-- 实际满射给出双向全域关系，不使用可数选择来挑选值或原像。 -/
theorem total_l (C : source_coding_l hℳ) (f : type_l hℳ)
    (A : SecondOrderGraph.code_l ℳ) (a : num_l ℳ) (ha : relation_l A.real a A.root)
    (hf : map_l hℳ f C.omega (mk_l hℳ A))
    (hOnto : ∀ y, mem_l hℳ y (mk_l hℳ A) → ∃ x, mem_l hℳ x C.omega ∧ value_l hℳ f x y)
    {K : set_l ℳ} (hK : ∀ n m, relation_l K n m ↔
      value_l hℳ f (numberCode_l C n).val (SecondOrderMemberStructure.value_l hℳ A a ha m).val) :
    (∀ n, ∃ m, relation_l K n m) ∧ (∀ m, ∃ n, relation_l K n m) := by
  constructor
  · intro n
    obtain ⟨y, ⟨hy, hny⟩, _⟩ := hf.2 (numberCode_l C n).val (numberCode_l C n).property
    obtain ⟨m, hm⟩ := SecondOrderMemberStructure.surjective_l hℳ A a ha ⟨y, hy⟩
    have hm' : (SecondOrderMemberStructure.value_l hℳ A a ha m).val = y := congrArg Subtype.val hm
    exact ⟨m, (hK n m).mpr (hm'.symm ▸ hny)⟩
  · intro m
    obtain ⟨x, hx, hxy⟩ := hOnto _ (SecondOrderMemberStructure.value_l hℳ A a ha m).property
    obtain ⟨n, hn⟩ := numberCode_surjective_l C ⟨x, hx⟩
    have hn' : (numberCode_l C n).val = x := congrArg Subtype.val hn
    exact ⟨n, (hK n m).mpr (hn'.symm ▸ hxy)⟩

#print axioms exists_l
#print axioms total_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEnumerationCorrespondence
