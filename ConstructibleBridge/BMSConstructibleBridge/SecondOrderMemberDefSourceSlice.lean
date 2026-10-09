import BMSConstructibleBridge.PowerlessRelativeParameters
import BMSConstructibleBridge.PowerlessRelativeLimitDeltaSeparationDerives
import YesMetaZFC.Automation.StructureCongruence

/-! # 任意有限源公式的实际 Def 切片

复用原 Def 的完整公式覆盖，将两种实际成员结构的同一载体对应起来。
不要求矩阵 Δ₀、不要求母集满足完整源理论，也不抽取统一真值谓词。
输出位于 Def(C)，并非 C；因此此结论不能替代截断层的完整分离。
外部模式实例最后回传原 Z₂ 的正式推导核。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberDefSourceSlice

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l mk_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l SecondOrderMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {C D : SecondOrderQuotient.type_l hℳ}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem exists_l (hC : ∃ x, mem_l hℳ x C) (hDef : SecondOrderMemberDef.spec_l hℳ C D)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (η : Env (PowerlessMemberStructure.structure_l (ℳ := 𝒱) C hC) [] Δ) :
    ∃ Y, mem_l hℳ Y D ∧ ∀ x : PowerlessMemberStructure.type_l (ℳ := 𝒱) C,
      mem_l hℳ x.val Y ↔ φ.satisfies (η.pushFree x) := by
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ C
  obtain ⟨c, hc⟩ := hC
  obtain ⟨a, ha, _⟩ := SecondOrderMemberDefProperties.member_root_l hℳ A hc
  have hStructure : PowerlessMemberStructure.structure_l (ℳ := 𝒱) (mk_l hℳ A) ⟨c, hc⟩ =
      SecondOrderMemberStructure.structure_l hℳ A a ha := by
    unfold PowerlessMemberStructure.structure_l SecondOrderMemberStructure.structure_l
    congr 1
    funext r args
    cases r
    cases args with
    | cons x rest => cases rest with
      | cons y tail => cases tail; rfl
  let ξ : Env (SecondOrderMemberStructure.structure_l hℳ A a ha) [] Δ :=
    { boundVal := η.boundVal
      freeVal := η.freeVal }
  obtain ⟨Y, hY, hRead⟩ := SecondOrderMemberDefProperties.coverage_l hℳ A a ha hDef ξ φ.abstractFreeTop
  refine ⟨Y, hY, fun x => ?_⟩
  obtain ⟨n, hn, hx⟩ := SecondOrderMemberDefProperties.member_root_l hℳ A x.property
  have hValue : (SecondOrderMemberStructure.value_l hℳ A a ha n).val =
      mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn) := by
    change mk_l hℳ (SecondOrderMemberNormalizer.code_l hℳ A a ha n) = _
    rw [SecondOrderMemberNormalizer.code_fixed_l hℳ A a ha n hn]
  have hPoint : SecondOrderMemberStructure.value_l hℳ A a ha n = x :=
    Subtype.ext (hValue.trans hx.symm)
  have h := (hRead n hn).trans
    (Formula.satisfies_abstractFreeTop ξ (SecondOrderMemberStructure.value_l hℳ A a ha n) φ)
  rw [hPoint] at h
  have hSame := _root_.YesMetaZFC.Automation.StructureCongruence.satisfies_l hStructure.symm
    (ξ.pushFree x) (η.pushFree x) (fun _ v => nomatch v)
    (fun s v => by cases s; cases v <;> rfl) φ
  simpa only [← hx] using h.trans hSame

private def arguments_m {Δ : SortContext ℒ} :
    Variable (.set :: Δ) SetTheory.SetSort.set → Term ℒ [.set, .set] (.set :: .set :: Δ) .set
  | .here => .bvar .here
  | .there v => .fvar (.there (.there v))

private def body_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    Formula ℒ [.set, .set] (.set :: .set :: Δ) :=
  PowerlessRelativeParameters.instance_m φ (.fvar .here) arguments_m

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) : Formula ℒ [] (.set :: .set :: Δ) :=
  let C : Term ℒ [] (.set :: .set :: Δ) .set := .fvar .here
  let D := .fvar (.there .here)
  .imp (.existsE .set (SecondOrderObjectSyntax.member_m (.bvar .here) (C.weakenBound SetTheory.SetSort.set))) <|
    .imp (PowerlessMemberDefSyntax.global_m C D) <|
      .imp (PowerlessRelativeLimitDeltaSeparationDerives.parameters_m Δ C (fun v => .fvar (.there (.there v)))) <|
        .existsE .set <| .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (D.weakenBound SetTheory.SetSort.set)) <|
          .forallE .set <| .iff (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there .here)))
            (.conj (SecondOrderObjectSyntax.member_m (.bvar .here)
              ((C.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set)) (body_m φ))

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) : (sentence_m φ).TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hC hDef hParams
  change ∃ x, mem_l hℳ x (η.freeVal .here) at hC
  have hDef' := (PowerlessMemberDefDerives.formula_l K η (.fvar .here) (.fvar (.there .here))).mp hDef
  have hParams' := (PowerlessRelativeLimitDeltaSeparationDerives.parameters_formula_l Δ η (.fvar .here)
    (fun v => .fvar (.there (.there v)))).mp hParams
  let ξ : Env (PowerlessMemberStructure.structure_l (ℳ := 𝒱) (η.freeVal .here) hC) [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with | .set => ⟨η.freeVal (.there (.there v)), hParams' _ v⟩ }
  obtain ⟨Y, hY, hRead⟩ := exists_l hC hDef' φ ξ
  refine ⟨Y, hY, fun x => ?_⟩
  have hBody (hx : mem_l hℳ x (η.freeVal .here)) :
      (body_m φ).satisfies ((η.pushBound Y).pushBound x) ↔ φ.satisfies (ξ.pushFree ⟨x, hx⟩) :=
    PowerlessRelativeParameters.instance_l φ ((η.pushBound Y).pushBound x) (.fvar .here) arguments_m
      (ξ.pushFree ⟨x, hx⟩) rfl (fun v => by cases v <;> rfl)
  constructor
  · intro hxY
    have hxC := SecondOrderMemberDefProperties.subset_l hℳ hDef' hY x hxY
    exact ⟨hxC, (hBody hxC).mpr ((hRead ⟨x, hxC⟩).mp hxY)⟩
  · rintro ⟨hxC, hφx⟩
    exact (hRead ⟨x, hxC⟩).mpr ((hBody hxC).mp hφx)

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ φ)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberDefSourceSlice
