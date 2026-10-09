import BMSConstructibleBridge.SecondOrderMemberCollapseCorrespondence
import BMSConstructibleBridge.SecondOrderEnumeratedMemberDef

/-!
# 实际成员塌缩下原 Def 集合的双向切片像

合法行迁移的索引允许变化。本模块先实际构造每个合法行的切片对象，再由
原集合收集规格证明其属于 Def 输出；因此不是以未知像集存在作为前提。
成员等价遍历全部原图商对象，不只指定母图中的节点代表。

最后以原 MemberDef 唯一性对齐任意非空母集的实际 Def 输出。这里处理
完整 Def(I) 与完整 Def(T)，不把原 Def(X) 在非传递源域中的截迹当作
Def(I)，也不证明 Class 资格、凝聚或 BMS 终局。见证全留在 Prop，使用
全部内部数码而不假设模型自然数外部标准。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberCollapseDef

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 全实际成员的像规格；函数 H 本身始终是原商中的同一集合图。 -/
def image_l (hℳ : Theory.Models ℳ theory_m)
    (H Y Z : SecondOrderQuotient.type_l hℳ) : Prop :=
  ∀ v, SecondOrderQuotient.mem_l hℳ v Z ↔
    ∃ x, SecondOrderQuotient.mem_l hℳ x Y ∧ SecondOrderFunctionObjects.value_l hℳ H x v

/-- 逆像规格不再外加域护栏；原 map 规格已使每个图值位于定义域。 -/
def preimage_l (hℳ : Theory.Models ℳ theory_m)
    (H Y Z : SecondOrderQuotient.type_l hℳ) : Prop :=
  ∀ x, SecondOrderQuotient.mem_l hℳ x Y ↔
    ∃ v, SecondOrderQuotient.mem_l hℳ v Z ∧ SecondOrderFunctionObjects.value_l hℳ H x v

/-- 任意合法内部行实际给出一个原 Def 成员，并读出全部商对象成员。 -/
theorem slice_exists_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    (a : num_l ℳ) (ha : relation_l A.real a A.root)
    {V E D Q R S F : set_l ℳ} {C : SecondOrderGraph.code_l ℳ}
    (P : SecondOrderLegalMemberCollection.presentation_l hℳ A a ha V E D Q R S F C)
    (i : num_l ℳ) (hi : SecondOrderLegalFormulaIndex.spec_l V E i) :
    ∃ Y : SecondOrderQuotient.type_l hℳ,
      SecondOrderQuotient.mem_l hℳ Y (SecondOrderQuotient.mk_l hℳ C) ∧
        ∀ x, SecondOrderQuotient.mem_l hℳ x Y ↔
          ∃ n, relation_l F i n ∧
            x = (SecondOrderMemberStructure.value_l hℳ A a ha n).val := by
  obtain ⟨U, hU⟩ := SecondOrderSubsetLayer.exists_l hℳ A.real F A.root
  let Y := SecondOrderSubsetLayer.code_l hℳ A F U hU i
  have hYC : SecondOrderGraph.mem_l Y C := (P.collection Y).mpr
    ⟨i, hi, SecondOrderSubsetLayer.mem_l hℳ A F U hU i⟩
  refine ⟨SecondOrderQuotient.mk_l hℳ Y,
    (SecondOrderQuotient.mem_iff_l hℳ Y C).mpr hYC, ?_⟩
  intro x
  obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
  exact (SecondOrderQuotient.mem_iff_l hℳ X Y).trans
    ((SecondOrderSubsetLayer.mem_l hℳ A F U hU i X).trans
      (SecondOrderLegalMemberExact.slice_l hℳ A a ha P i X))

/-- 已证内部对应与行迁移落实为全 raw 成员像及逆像；只作为中间工具。 -/
theorem slice_transport_l (hℳ : Theory.Models ℳ theory_m) (A B : SecondOrderGraph.code_l ℳ)
    (a b : num_l ℳ) (ha : relation_l A.real a A.root) (hb : relation_l B.real b B.root)
    (H : SecondOrderQuotient.type_l hℳ)
    (hH : SecondOrderFunctionObjects.map_l hℳ H
      (SecondOrderQuotient.mk_l hℳ A) (SecondOrderQuotient.mk_l hℳ B))
    (hInjective : SecondOrderFunctionObjects.injective_l hℳ H)
    (K F G : set_l ℳ)
    (hK : ∀ n m, relation_l K n m ↔ SecondOrderFunctionObjects.value_l hℳ H
      (SecondOrderMemberStructure.value_l hℳ A a ha n).val
      (SecondOrderMemberStructure.value_l hℳ B b hb m).val)
    (hLeft : ∀ n, ∃ m, relation_l K n m) (hRight : ∀ m, ∃ n, relation_l K n m)
    (i j : num_l ℳ)
    (hRows : ∀ n m, relation_l K n m → (relation_l F i n ↔ relation_l G j m))
    (Y Z : SecondOrderQuotient.type_l hℳ)
    (hY : ∀ x, SecondOrderQuotient.mem_l hℳ x Y ↔
      ∃ n, relation_l F i n ∧ x = (SecondOrderMemberStructure.value_l hℳ A a ha n).val)
    (hZ : ∀ v, SecondOrderQuotient.mem_l hℳ v Z ↔
      ∃ m, relation_l G j m ∧ v = (SecondOrderMemberStructure.value_l hℳ B b hb m).val) :
    image_l hℳ H Y Z ∧ preimage_l hℳ H Y Z := by
  constructor
  · intro v
    constructor
    · intro hv
      obtain ⟨m, hm, hv⟩ := (hZ v).mp hv
      obtain ⟨n, hnm⟩ := hRight m
      refine ⟨(SecondOrderMemberStructure.value_l hℳ A a ha n).val,
        (hY _).mpr ⟨n, (hRows n m hnm).mpr hm, rfl⟩, ?_⟩
      exact hv.symm ▸ (hK n m).mp hnm
    · rintro ⟨x, hx, hxv⟩
      obtain ⟨n, hn, hx⟩ := (hY x).mp hx
      rw [hx] at hxv
      obtain ⟨m, hnm⟩ := hLeft n
      exact (hZ v).mpr ⟨m, (hRows n m hnm).mp hn,
        SecondOrderFunctionProperties.value_unique_l hℳ hH hxv ((hK n m).mp hnm)⟩
  · intro x
    constructor
    · intro hx
      obtain ⟨n, hn, hx⟩ := (hY x).mp hx
      obtain ⟨m, hnm⟩ := hLeft n
      refine ⟨(SecondOrderMemberStructure.value_l hℳ B b hb m).val,
        (hZ _).mpr ⟨m, (hRows n m hnm).mp hn, rfl⟩, ?_⟩
      exact hx.symm ▸ (hK n m).mp hnm
    · rintro ⟨v, hv, hxv⟩
      obtain ⟨m, hm, hv⟩ := (hZ v).mp hv
      rw [hv] at hxv
      obtain ⟨n, hnm⟩ := hRight m
      exact (hY x).mpr ⟨n, (hRows n m hnm).mpr hm,
        hInjective _ _ _ hxv ((hK n m).mp hnm)⟩

/-- 两份真实原呈现的每个 Def 成员都有对应像，反向亦然。 -/
theorem presentation_l (hℳ : Theory.Models ℳ theory_m) (A B : SecondOrderGraph.code_l ℳ)
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
    (∀ Y, SecondOrderQuotient.mem_l hℳ Y (SecondOrderQuotient.mk_l hℳ C) →
      ∃ Z, SecondOrderQuotient.mem_l hℳ Z (SecondOrderQuotient.mk_l hℳ C') ∧
        image_l hℳ H Y Z ∧ preimage_l hℳ H Y Z) ∧
    ∀ Z, SecondOrderQuotient.mem_l hℳ Z (SecondOrderQuotient.mk_l hℳ C') →
      ∃ Y, SecondOrderQuotient.mem_l hℳ Y (SecondOrderQuotient.mk_l hℳ C) ∧
        image_l hℳ H Y Z ∧ preimage_l hℳ H Y Z := by
  obtain ⟨W, _, hUnique⟩ := SecondOrderInternalFormulaSyntax.exists_l hℳ
  have hV : V' = V := (hUnique V' P'.formula_codes).trans (hUnique V P.formula_codes).symm
  subst V'
  have hE : E' = E := SecondOrderPowers.unique_l hℳ P'.powers P.powers
  subst E'
  obtain ⟨K, hK, hCorr, hRows⟩ := SecondOrderMemberCollapseCorrespondence.family_l
    hℳ A B a b ha hb H hH hOnto hInjective hMember
    V V E E D D' Q Q' R R' S S' F G C C' P P'
  constructor
  · intro Y hYC
    obtain ⟨i, hi, hY⟩ := (SecondOrderEnumeratedMemberDef.original_collection_l A a ha P Y).mp hYC
    obtain ⟨j, hj, hRow⟩ := hRows.1 i hi
    obtain ⟨Z, hZC, hZ⟩ := slice_exists_l hℳ B b hb P' j hj
    obtain ⟨hImage, hPreimage⟩ := slice_transport_l hℳ A B a b ha hb H hH hInjective
      K F G hK hCorr.left_total hCorr.right_total i j hRow Y Z hY hZ
    exact ⟨Z, hZC, hImage, hPreimage⟩
  · intro Z hZC
    obtain ⟨j, hj, hZ⟩ := (SecondOrderEnumeratedMemberDef.original_collection_l B b hb P' Z).mp hZC
    obtain ⟨i, hi, hRow⟩ := hRows.2 j hj
    obtain ⟨Y, hYC, hY⟩ := slice_exists_l hℳ A a ha P i hi
    obtain ⟨hImage, hPreimage⟩ := slice_transport_l hℳ A B a b ha hb H hH hInjective
      K F G hK hCorr.left_total hCorr.right_total i j hRow Y Z hY hZ
    exact ⟨Y, hYC, hImage, hPreimage⟩

/-- 原 Def 关系的任意实际输出由唯一性对齐；非空母集明确列为前提。 -/
theorem nonempty_l (hℳ : Theory.Models ℳ theory_m)
    (I T DI DT H : SecondOrderQuotient.type_l hℳ)
    (hI : ∃ x, SecondOrderQuotient.mem_l hℳ x I)
    (hDI : SecondOrderMemberDef.spec_l hℳ I DI) (hDT : SecondOrderMemberDef.spec_l hℳ T DT)
    (hH : SecondOrderFunctionObjects.map_l hℳ H I T)
    (hOnto : ∀ u, SecondOrderQuotient.mem_l hℳ u T →
      ∃ x, SecondOrderQuotient.mem_l hℳ x I ∧ SecondOrderFunctionObjects.value_l hℳ H x u)
    (hInjective : SecondOrderFunctionObjects.injective_l hℳ H)
    (hMember : ∀ x y u v, SecondOrderQuotient.mem_l hℳ x I → SecondOrderQuotient.mem_l hℳ y I →
      SecondOrderFunctionObjects.value_l hℳ H x u → SecondOrderFunctionObjects.value_l hℳ H y v →
      (SecondOrderQuotient.mem_l hℳ x y ↔ SecondOrderQuotient.mem_l hℳ u v)) :
    (∀ Y, SecondOrderQuotient.mem_l hℳ Y DI →
      ∃ Z, SecondOrderQuotient.mem_l hℳ Z DT ∧ image_l hℳ H Y Z ∧ preimage_l hℳ H Y Z) ∧
    ∀ Z, SecondOrderQuotient.mem_l hℳ Z DT →
      ∃ Y, SecondOrderQuotient.mem_l hℳ Y DI ∧ image_l hℳ H Y Z ∧ preimage_l hℳ H Y Z := by
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ I
  obtain ⟨x, hx⟩ := hI
  obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
  obtain ⟨B, rfl⟩ := SecondOrderQuotient.surj_l hℳ T
  obtain ⟨u, ⟨hu, _⟩, _⟩ := hH.2 (SecondOrderQuotient.mk_l hℳ X) hx
  obtain ⟨a, ha, _⟩ := hx
  obtain ⟨U, rfl⟩ := SecondOrderQuotient.surj_l hℳ u
  obtain ⟨b, hb, _⟩ := hu
  obtain ⟨V, E, D, Q, R, S, F, C, P, _⟩ := SecondOrderLegalMemberCollection.exists_l hℳ A a ha
  obtain ⟨V', E', D', Q', R', S', G, C', P', _⟩ := SecondOrderLegalMemberCollection.exists_l hℳ B b hb
  have hDC : SecondOrderMemberDef.spec_l hℳ (SecondOrderQuotient.mk_l hℳ A)
      (SecondOrderQuotient.mk_l hℳ C) :=
    Or.inr ⟨A, a, ha, V, E, D, Q, R, S, F, C, rfl, P, rfl⟩
  have hDC' : SecondOrderMemberDef.spec_l hℳ (SecondOrderQuotient.mk_l hℳ B)
      (SecondOrderQuotient.mk_l hℳ C') :=
    Or.inr ⟨B, b, hb, V', E', D', Q', R', S', G, C', rfl, P', rfl⟩
  have hCI := SecondOrderMemberDef.unique_l hℳ hDC hDI
  have hCT := SecondOrderMemberDef.unique_l hℳ hDC' hDT
  have hResult := presentation_l hℳ A B a b ha hb H hH hOnto hInjective hMember
    V V' E E' D D' Q Q' R R' S S' F G C C' P P'
  rw [hCI, hCT] at hResult
  exact hResult

/-- 空母集分支也保留：两份原 Def 输出在同一 H 下都有双向实际切片。 -/
theorem spec_l (hℳ : Theory.Models ℳ theory_m)
    (I T DI DT H : SecondOrderQuotient.type_l hℳ)
    (hDI : SecondOrderMemberDef.spec_l hℳ I DI) (hDT : SecondOrderMemberDef.spec_l hℳ T DT)
    (hH : SecondOrderFunctionObjects.map_l hℳ H I T)
    (hOnto : ∀ u, SecondOrderQuotient.mem_l hℳ u T →
      ∃ x, SecondOrderQuotient.mem_l hℳ x I ∧ SecondOrderFunctionObjects.value_l hℳ H x u)
    (hInjective : SecondOrderFunctionObjects.injective_l hℳ H)
    (hMember : ∀ x y u v, SecondOrderQuotient.mem_l hℳ x I → SecondOrderQuotient.mem_l hℳ y I →
      SecondOrderFunctionObjects.value_l hℳ H x u → SecondOrderFunctionObjects.value_l hℳ H y v →
      (SecondOrderQuotient.mem_l hℳ x y ↔ SecondOrderQuotient.mem_l hℳ u v)) :
    (∀ Y, SecondOrderQuotient.mem_l hℳ Y DI →
      ∃ Z, SecondOrderQuotient.mem_l hℳ Z DT ∧ image_l hℳ H Y Z ∧ preimage_l hℳ H Y Z) ∧
    ∀ Z, SecondOrderQuotient.mem_l hℳ Z DT →
      ∃ Y, SecondOrderQuotient.mem_l hℳ Y DI ∧ image_l hℳ H Y Z ∧ preimage_l hℳ H Y Z := by
  classical
  by_cases hI : ∃ x, SecondOrderQuotient.mem_l hℳ x I
  · exact nonempty_l hℳ I T DI DT H hI hDI hDT hH hOnto hInjective hMember
  have hEmptyI : ∀ x, ¬SecondOrderQuotient.mem_l hℳ x I := fun x hx => hI ⟨x, hx⟩
  have hEmptyT : ∀ v, ¬SecondOrderQuotient.mem_l hℳ v T := by
    intro v hv
    obtain ⟨x, hx, _⟩ := hOnto v hv
    exact hEmptyI x hx
  have hPairI : SecondOrderPairObjects.pair_l hℳ I I DI := by
    rcases hDI with ⟨_, hPair⟩ | hNonempty
    · exact hPair
    · obtain ⟨x, hx⟩ := SecondOrderMemberDef.nonempty_member_l hℳ hNonempty
      exact False.elim (hEmptyI x hx)
  have hPairT : SecondOrderPairObjects.pair_l hℳ T T DT := by
    rcases hDT with ⟨_, hPair⟩ | hNonempty
    · exact hPair
    · obtain ⟨v, hv⟩ := SecondOrderMemberDef.nonempty_member_l hℳ hNonempty
      exact False.elim (hEmptyT v hv)
  have hImage : image_l hℳ H I T := by
    intro v
    apply iff_of_false (hEmptyT v)
    rintro ⟨x, hx, _⟩
    exact hEmptyI x hx
  have hPreimage : preimage_l hℳ H I T := by
    intro x
    apply iff_of_false (hEmptyI x)
    rintro ⟨v, hv, _⟩
    exact hEmptyT v hv
  constructor
  · intro Y hY
    have hYI : Y = I := ((hPairI Y).mp hY).elim id id
    subst Y
    exact ⟨T, (hPairT T).mpr (Or.inl rfl), hImage, hPreimage⟩
  · intro Z hZ
    have hZT : Z = T := ((hPairT Z).mp hZ).elim id id
    subst Z
    exact ⟨I, (hPairI I).mpr (Or.inl rfl), hImage, hPreimage⟩

#print axioms slice_exists_l
#print axioms slice_transport_l
#print axioms presentation_l
#print axioms nonempty_l
#print axioms spec_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberCollapseDef
