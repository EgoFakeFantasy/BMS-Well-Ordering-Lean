import BMSConstructibleBridge.SecondOrderMemberCorrespondence
import BMSConstructibleBridge.SecondOrderGraphFormulaGuard
import BMSConstructibleBridge.SecondOrderFunctionProperties
import BMSConstructibleBridge.SecondOrderObjectSyntax

/-!
# 成员塌缩下两份原 Def 呈现的内部对应

任意原 Z₂ 模型中，给定真实集合函数 H 在两个非空母集的成员结构之间的
满射、单射和成员双向保持规格，实际理解构造内部数码对应实数 K。母集
无需相等，K 也不作为额外前提。原正规化枚举保留指定非空见证；所有函数
输出、对应及赋值迁移证书均留在 Prop，不抽取 Type 选择函数。

两份原 Def 呈现的合法性图和幂图由既有唯一性对齐，再调用全内部公式及
内部有限赋值运输器。这里只对应两个完整实际母集的原呈现，不自动识别
原 Def(X) 在非传递源域中的截迹，也不因此宣称凝聚或 Class 资格完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberCollapseCorrespondence

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 先读真正 H 的集合图，再正规化两侧全内部数域的成员代表。 -/
theorem exists_l (hℳ : Theory.Models ℳ theory_m) (A B : SecondOrderGraph.code_l ℳ)
    (a b : num_l ℳ) (ha : relation_l A.real a A.root) (hb : relation_l B.real b B.root)
    (H : SecondOrderQuotient.type_l hℳ) :
    ∃ K : set_l ℳ, ∀ n m, relation_l K n m ↔
      SecondOrderFunctionObjects.value_l hℳ H
        (SecondOrderMemberStructure.value_l hℳ A a ha n).val
        (SecondOrderMemberStructure.value_l hℳ B b hb m).val := by
  let φ : Formula ℒ [] [.set, .set, .set] :=
    SecondOrderObjectSyntax.value_m (.fvar (.there (.there .here)))
      (.fvar .here) (.fvar (.there .here))
  let η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set] := Env.empty.pushFree H
  obtain ⟨G, hG⟩ := SecondOrderGraphFormulaGuard.exists_l hℳ φ η A.real B.real
  obtain ⟨N, hN⟩ := SecondOrderMemberNormalizer.exists_l hℳ A.real A.root a
  obtain ⟨N', hN'⟩ := SecondOrderMemberNormalizer.exists_l hℳ B.real B.root b
  obtain ⟨K, hK⟩ := SecondOrderRelations.comprehension_l hℳ
    SecondOrderMemberCorrespondence.formula_m (pure_language_m _ rfl)
    ((((Env.empty (M := ℳ)).pushFree G).pushFree N').pushFree N)
  refine ⟨K, fun n m => (hK n m).trans ?_⟩
  simp only [SecondOrderMemberCorrespondence.formula_m, Formula.satisfies,
    SecondOrderPairing.edge_l]
  change (∃ x y, relation_l N n x ∧ relation_l N' m y ∧ relation_l G x y) ↔ _
  constructor
  · rintro ⟨x, y, hx, hy, hxy⟩
    rw [hN] at hx
    rw [hN'] at hy
    subst x
    subst y
    obtain ⟨hn, hm, h⟩ := (hG _ _).mp hxy
    exact (SecondOrderObjectSyntax.value_l hℳ _ _ _ _).mp h
  · intro h
    let C := SecondOrderMemberNormalizer.code_l hℳ A a ha n
    let D := SecondOrderMemberNormalizer.code_l hℳ B b hb m
    refine ⟨C.root, D.root, (hN n C.root).mpr rfl, (hN' m D.root).mpr rfl,
      (hG C.root D.root).mpr ⟨C.wf, D.wf, ?_⟩⟩
    exact (SecondOrderObjectSyntax.value_l hℳ _ _ _ _).mpr h

/-- 同一个内部 K 对全部合法码给出双向行迁移，索引允许不同。 -/
def rows_l (V E K F G : set_l ℳ) : Prop :=
  (∀ i, SecondOrderLegalFormulaIndex.spec_l V E i →
    ∃ j, SecondOrderLegalFormulaIndex.spec_l V E j ∧
      ∀ n m, relation_l K n m → (relation_l F i n ↔ relation_l G j m)) ∧
  ∀ j, SecondOrderLegalFormulaIndex.spec_l V E j →
    ∃ i, SecondOrderLegalFormulaIndex.spec_l V E i ∧
      ∀ n m, relation_l K n m → (relation_l F i n ↔ relation_l G j m)

/-- 两份原呈现可有不同语法及幂图；对齐在证明内进行，不要求母集相等。 -/
theorem family_l (hℳ : Theory.Models ℳ theory_m) (A B : SecondOrderGraph.code_l ℳ)
    (a b : num_l ℳ) (ha : relation_l A.real a A.root) (hb : relation_l B.real b B.root)
    (H : SecondOrderQuotient.type_l hℳ)
    (hH : SecondOrderFunctionObjects.map_l hℳ H
      (SecondOrderQuotient.mk_l hℳ A) (SecondOrderQuotient.mk_l hℳ B))
    (hOnto : ∀ u, SecondOrderQuotient.mem_l hℳ u (SecondOrderQuotient.mk_l hℳ B) →
      ∃ x, SecondOrderQuotient.mem_l hℳ x (SecondOrderQuotient.mk_l hℳ A) ∧
        SecondOrderFunctionObjects.value_l hℳ H x u)
    (hInjective : SecondOrderFunctionObjects.injective_l hℳ H)
    (hMember : ∀ x y u v,
      SecondOrderQuotient.mem_l hℳ x (SecondOrderQuotient.mk_l hℳ A) →
      SecondOrderQuotient.mem_l hℳ y (SecondOrderQuotient.mk_l hℳ A) →
      SecondOrderFunctionObjects.value_l hℳ H x u →
      SecondOrderFunctionObjects.value_l hℳ H y v →
      (SecondOrderQuotient.mem_l hℳ x y ↔ SecondOrderQuotient.mem_l hℳ u v))
    (V V' E E' D D' Q Q' R R' S S' F G : set_l ℳ) (C C' : SecondOrderGraph.code_l ℳ)
    (P : SecondOrderLegalMemberCollection.presentation_l hℳ A a ha V E D Q R S F C)
    (P' : SecondOrderLegalMemberCollection.presentation_l hℳ B b hb V' E' D' Q' R' S' G C') :
    ∃ K, (∀ n m, relation_l K n m ↔ SecondOrderFunctionObjects.value_l hℳ H
      (SecondOrderMemberStructure.value_l hℳ A a ha n).val
      (SecondOrderMemberStructure.value_l hℳ B b hb m).val) ∧
      SecondOrderDefinableFamilyTransport.correspondence_l E D D' K Q Q' R R' S S' F G ∧
      rows_l V E K F G := by
  obtain ⟨W, _, hUnique⟩ := SecondOrderInternalFormulaSyntax.exists_l hℳ
  have hV : V' = V := (hUnique V' P'.formula_codes).trans (hUnique V P.formula_codes).symm
  subst V'
  have hE : E' = E := SecondOrderPowers.unique_l hℳ P'.powers P.powers
  subst E'
  obtain ⟨K, hK⟩ := exists_l hℳ A B a b ha hb H
  have hCorr : SecondOrderDefinableFamilyTransport.correspondence_l
      E D D' K Q Q' R R' S S' F G := by
    refine ⟨P.powers, P.domain, P'.domain, ?_, ?_, ?_, ?_,
      P.evaluation, P'.evaluation, P.family, P'.family⟩
    · intro n
      obtain ⟨u, ⟨hu, hxu⟩, _⟩ := hH.2
        (SecondOrderMemberStructure.value_l hℳ A a ha n).val
        (SecondOrderMemberStructure.value_l hℳ A a ha n).property
      obtain ⟨m, hm⟩ := SecondOrderMemberStructure.surjective_l hℳ B b hb ⟨u, hu⟩
      refine ⟨m, (hK n m).mpr ?_⟩
      rw [congrArg Subtype.val hm]
      exact hxu
    · intro m
      obtain ⟨x, hx, hxu⟩ := hOnto
        (SecondOrderMemberStructure.value_l hℳ B b hb m).val
        (SecondOrderMemberStructure.value_l hℳ B b hb m).property
      obtain ⟨n, hn⟩ := SecondOrderMemberStructure.surjective_l hℳ A a ha ⟨x, hx⟩
      refine ⟨n, (hK n m).mpr ?_⟩
      rw [congrArg Subtype.val hn]
      exact hxu
    · intro x y n m hx hy
      rw [P.equality, P'.equality]
      have hxn := (hK x n).mp hx
      have hym := (hK y m).mp hy
      constructor
      · intro hxy
        have hxy' := congrArg Subtype.val hxy
        exact Subtype.ext (SecondOrderFunctionProperties.value_unique_l hℳ hH
          (hxy' ▸ hxn) hym)
      · intro hnm
        have hnm' := congrArg Subtype.val hnm
        exact Subtype.ext (hInjective _ _ _ (hnm' ▸ hxn) hym)
    · intro x y n m hx hy
      rw [P.membership, P'.membership]
      exact hMember _ _ _ _
        (SecondOrderMemberStructure.value_l hℳ A a ha x).property
        (SecondOrderMemberStructure.value_l hℳ A a ha y).property
        ((hK x n).mp hx) ((hK y m).mp hy)
  refine ⟨K, hK, hCorr, ?_, ?_⟩
  · exact fun i hi => SecondOrderDefinableFamilyTransport.left_l hℳ hCorr V i hi
  · exact fun j hj => SecondOrderDefinableFamilyTransport.right_l hℳ hCorr V j hj

#print axioms exists_l
#print axioms family_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberCollapseCorrespondence
