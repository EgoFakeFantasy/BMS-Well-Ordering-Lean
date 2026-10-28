import BMSConstructibleBridge.SecondOrderMemberDef
import BMSConstructibleBridge.SecondOrderEnumerationCorrespondence

/-!
# 用实际集合函数读取全部内部定义子集

证书只用母集、枚举函数及内部算术关系，不再将正规化图作为定义参数。
任意满足证书的枚举均给出原 MemberDef 的同一商对象。这里先核验语义
对应；纯集合 AST 及对象推导另行封装，不能把本模块称为 BMS 终局。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEnumeratedMemberDef

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)
open PowerlessBMSQuotientCoding SecondOrderFunctionObjects

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
  {hℳ : Theory.Models ℳ theory_m}

local notation "qmem" => SecondOrderQuotient.mem_l hℳ
local notation "qmk" => SecondOrderQuotient.mk_l hℳ

structure presentation_l (C : source_coding_l hℳ) (X Y f : SecondOrderQuotient.type_l hℳ)
    (V E D Q R T F : set_l ℳ) : Prop where
  mapping : map_l hℳ f C.omega X
  onto : ∀ y, qmem y X → ∃ x, qmem x C.omega ∧ value_l hℳ f x y
  formula_codes : SecondOrderInternalFormulaSyntax.spec_l V
  powers : SecondOrderBinaryPowers.spec_l E
  domain : ∀ n, mem_l n D
  equality : ∀ n m x y, value_l hℳ f (numberCode_l C n).val x →
    value_l hℳ f (numberCode_l C m).val y → (relation_l Q n m ↔ x = y)
  membership : ∀ n m x y, value_l hℳ f (numberCode_l C n).val x →
    value_l hℳ f (numberCode_l C m).val y → (relation_l R n m ↔ qmem x y)
  evaluation : SecondOrderEvaluationEquations.spec_l E D Q R T
  family : SecondOrderDefinableFamily.spec_l E D T F
  collection : ∀ B, qmem B Y ↔ ∃ i, SecondOrderLegalFormulaIndex.spec_l V E i ∧
    ∀ x, qmem x B ↔ ∃ n, relation_l F i n ∧ value_l hℳ f (numberCode_l C n).val x

/-- 旧图呈现的精确性提升到任意商对象，不限制其代表图。 -/
theorem original_collection_l (A : SecondOrderGraph.code_l ℳ) (a : num_l ℳ)
    (ha : relation_l A.real a A.root) {V E D Q R T F : set_l ℳ} {H : SecondOrderGraph.code_l ℳ}
    (P : SecondOrderLegalMemberCollection.presentation_l hℳ A a ha V E D Q R T F H)
    (B : SecondOrderQuotient.type_l hℳ) : qmem B (qmk H) ↔
      ∃ i, SecondOrderLegalFormulaIndex.spec_l V E i ∧ ∀ x,
        qmem x B ↔ ∃ n, relation_l F i n ∧ x = (SecondOrderMemberStructure.value_l hℳ A a ha n).val := by
  obtain ⟨B, rfl⟩ := SecondOrderQuotient.surj_l hℳ B
  refine (SecondOrderQuotient.mem_iff_l hℳ B H).trans
    ((SecondOrderLegalMemberExact.collection_l hℳ A a ha P B).trans ?_)
  apply exists_congr
  intro i
  apply and_congr Iff.rfl
  constructor
  · intro h x
    obtain ⟨Z, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
    exact (SecondOrderQuotient.mem_iff_l hℳ Z B).trans (h Z)
  · intro h Z
    exact (SecondOrderQuotient.mem_iff_l hℳ Z B).symm.trans (h (qmk Z))

theorem compare_l (C : source_coding_l hℳ) (A : SecondOrderGraph.code_l ℳ)
    (a : num_l ℳ) (ha : relation_l A.real a A.root)
    {V E D Q R T F : set_l ℳ} {H : SecondOrderGraph.code_l ℳ}
    (P : SecondOrderLegalMemberCollection.presentation_l hℳ A a ha V E D Q R T F H)
    {Y f : SecondOrderQuotient.type_l hℳ} {V' E' D' Q' R' U G : set_l ℳ}
    (P' : presentation_l C (qmk A) Y f V' E' D' Q' R' U G) : Y = qmk H := by
  obtain ⟨W, _, hUnique⟩ := SecondOrderInternalFormulaSyntax.exists_l hℳ
  have hV : V' = V := (hUnique V' P'.formula_codes).trans (hUnique V P.formula_codes).symm
  subst V'
  have hE : E' = E := SecondOrderPowers.unique_l hℳ P'.powers P.powers
  subst E'
  obtain ⟨K, hK⟩ := SecondOrderEnumerationCorrespondence.exists_l C f A a ha
  obtain ⟨hLeft, hRight⟩ := SecondOrderEnumerationCorrespondence.total_l C f A a ha
    P'.mapping P'.onto hK
  let v := fun n => (SecondOrderMemberStructure.value_l hℳ A a ha n).val
  have hCorr : SecondOrderDefinableFamilyTransport.correspondence_l E D' D K Q' Q R' R U T G F := by
    refine ⟨P.powers, P'.domain, P.domain, hLeft, hRight, ?_, ?_,
      P'.evaluation, P.evaluation, P'.family, P.family⟩
    · intro n m x y hnx hmy
      exact (P'.equality n m (v x) (v y) ((hK n x).mp hnx) ((hK m y).mp hmy)).trans
        (Subtype.val_injective.eq_iff.trans (P.equality x y).symm)
    · intro n m x y hnx hmy
      exact (P'.membership n m (v x) (v y) ((hK n x).mp hnx) ((hK m y).mp hmy)).trans
        (P.membership x y).symm
  apply SecondOrderQuotient.ext_l hℳ
  intro B
  rw [P'.collection, original_collection_l A a ha P B]
  have hSlice i j (hRows : ∀ n m, relation_l K n m → (relation_l G i n ↔ relation_l F j m)) (x) :
      (∃ n, relation_l G i n ∧ value_l hℳ f (numberCode_l C n).val x) ↔
        ∃ m, relation_l F j m ∧ x = v m := by
    constructor
    · rintro ⟨n, hn, hnx⟩
      obtain ⟨m, hnm⟩ := hLeft n
      exact ⟨m, (hRows n m hnm).mp hn,
        SecondOrderFunctionLaws.value_unique_l hℳ P'.mapping hnx ((hK n m).mp hnm)⟩
    · rintro ⟨m, hm, rfl⟩
      obtain ⟨n, hnm⟩ := hRight m
      exact ⟨n, (hRows n m hnm).mpr hm, (hK n m).mp hnm⟩
  constructor
  · rintro ⟨i, hi, hB⟩
    obtain ⟨j, hj, hRows⟩ := SecondOrderDefinableFamilyTransport.left_l hℳ hCorr V i hi
    exact ⟨j, hj, fun x => (hB x).trans (hSlice i j hRows x)⟩
  · rintro ⟨j, hj, hB⟩
    obtain ⟨i, hi, hRows⟩ := SecondOrderDefinableFamilyTransport.right_l hℳ hCorr V j hj
    exact ⟨i, hi, fun x => (hB x).trans (hSlice i j hRows x).symm⟩

theorem exists_l (C : source_coding_l hℳ) (A : SecondOrderGraph.code_l ℳ)
    (a : num_l ℳ) (ha : relation_l A.real a A.root) :
    ∃ Y f V E D Q R T F, presentation_l C (qmk A) Y f V E D Q R T F ∧
      SecondOrderMemberDef.nonempty_l hℳ (qmk A) Y := by
  obtain ⟨V, E, D, Q, R, T, F, H, P, _⟩ := SecondOrderLegalMemberCollection.exists_l hℳ A a ha
  obtain ⟨f, hf, hRead, hOnto⟩ := SecondOrderMemberEnumeration.exists_l C A a ha
  refine ⟨qmk H, f, V, E, D, Q, R, T, F, ?_,
    ⟨A, a, ha, V, E, D, Q, R, T, F, H, rfl, P, rfl⟩⟩
  refine ⟨hf, hOnto, P.formula_codes, P.powers, P.domain, ?_, ?_, P.evaluation, P.family, ?_⟩
  · intro n m x y hx hy
    rw [(hRead n x).mp hx, (hRead m y).mp hy]
    exact (P.equality n m).trans Subtype.val_injective.eq_iff.symm
  · intro n m x y hx hy
    rw [(hRead n x).mp hx, (hRead m y).mp hy]
    exact P.membership n m
  · intro B
    refine (original_collection_l A a ha P B).trans (exists_congr (fun i => and_congr Iff.rfl ?_))
    apply forall_congr'
    intro x
    apply iff_congr Iff.rfl
    exact exists_congr (fun n => and_congr Iff.rfl (hRead n x).symm)

/-- 任意实际枚举证书都对应原全域 Def 的非空分支。 -/
theorem represents_l (C : source_coding_l hℳ) {X Y f : SecondOrderQuotient.type_l hℳ}
    {V E D Q R T F : set_l ℳ} (P : presentation_l C X Y f V E D Q R T F) :
    SecondOrderMemberDef.nonempty_l hℳ X Y := by
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ X
  obtain ⟨y, ⟨hy, _⟩, _⟩ := P.mapping.2 (numberCode_l C (zero_l ℳ)).val (numberCode_l C (zero_l ℳ)).property
  obtain ⟨B, rfl⟩ := SecondOrderQuotient.surj_l hℳ y
  obtain ⟨a, ha, _⟩ := hy
  obtain ⟨V', E', D', Q', R', U, G, H, P', _⟩ := SecondOrderLegalMemberCollection.exists_l hℳ A a ha
  have hY := compare_l C A a ha P' P
  exact ⟨A, a, ha, V', E', D', Q', R', U, G, H, rfl, P', hY.symm⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEnumeratedMemberDef
