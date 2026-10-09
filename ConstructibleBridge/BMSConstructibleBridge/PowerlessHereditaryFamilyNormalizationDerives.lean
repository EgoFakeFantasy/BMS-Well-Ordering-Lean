import BMSConstructibleBridge.PowerlessHereditaryFamilyNormalization
import BMSConstructibleBridge.PowerlessHereditaryRealRequestDerives

/-! # 类内族零根规范化存在性的原 Z₂ 对象推导

目标是原 Derives 核中的纯检查器图翻译。原 Class 实数 U 的全部
内部数行均由一个实际遗传实数 V 规范化；支撑参数消费既有原规格。
没有加入 Class 全可数性或 Collection，也不把实数代表等同于解码对象。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryFamilyNormalizationDerives

open Logic FirstOrder StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def reading_m {Γ Δ : SortContext ℒ} (ω e o S U V : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall ω <| membershipLevyBound.boundedForall (up ω) <| .iff
    (PowerlessRootedRealSyntax.row_m (up (up ω)) (up (up e)) (up (up S)) (up (up V))
      (.bvar (.there .here)) (.bvar .here))
    (PowerlessRootedFamilyNormalizationSyntax.body_m (up (up ω)) (up (up e)) (up (up o))
      (up (up S)) (up (up U)) (.bvar (.there .here)) (.bvar .here))

def schema_m : Formula ℒ [] [.set, .set, .set, .set, .set, .set] :=
  let B : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar .here
  let ω := .fvar (.there .here)
  let e := .fvar (.there (.there .here))
  let o := .fvar (.there (.there (.there .here)))
  let S := .fvar (.there (.there (.there (.there .here))))
  let U := .fvar (.there (.there (.there (.there (.there .here)))))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessHereditaryRealRequestDerives.support_m ω e o S) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B U) <|
        .imp (PowerlessHereditaryRealRequest.real_m ω U) <| .existsE .set <| .conj
          (PowerlessHereditaryClass.formula_m (up B) (.bvar .here)) <| .conj
          (PowerlessHereditaryRealRequest.real_m (up ω) (.bvar .here))
          (reading_m (up ω) (up e) (up o) (up S) (up U) (.bvar .here))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def reading_l (ω e o S U V : SecondOrderQuotient.type_l hℳ) : Prop :=
  ∀ i, mem_l hℳ i ω → ∀ z, mem_l hℳ z ω →
    (PowerlessRootedRealSyntax.row_l (𝒩 := 𝒱) ω e S V i z ↔
      PowerlessRootedFamilyNormalizationSyntax.body_l (𝒩 := 𝒱) ω e o S U i z)

theorem reading_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (ω e o S U V : Term ℒ Γ Δ .set) :
    (reading_m ω e o S U V).satisfies η ↔
      reading_l (ω.eval η) (e.eval η) (o.eval η) (S.eval η) (U.eval η) (V.eval η) := by
  simp only [reading_m, reading_l, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessRootedRealSyntax.row_formula_l,
    PowerlessRootedFamilyNormalizationSyntax.body_formula_l, Arguments.eval,
    up, Term.eval_weakenBound, Term.eval]
  rfl

theorem read_l (K : source_coding_l hℳ) {S U V : SecondOrderQuotient.type_l hℳ}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega S)
    (hU : ∀ c, mem_l hℳ c U → mem_l hℳ c K.omega)
    (hV : ∀ c, mem_l hℳ c V → mem_l hℳ c K.omega) {H J : SecondOrderModel.set_l ℳ}
    (hUTrace : setRel_l K ⟨U, hU⟩ H) (hVTrace : setRel_l K ⟨V, hV⟩ J)
    (hJ : SecondOrderRootedRealFamilyNormalization.spec_l H J) :
    reading_l K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val
      (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).val S U V := by
  intro i hi z hz
  obtain ⟨i₀, hi₀⟩ := numberCode_surjective_l K ⟨i, hi⟩
  obtain ⟨z₀, hz₀⟩ := numberCode_surjective_l K ⟨z, hz⟩
  have hi₀' : (numberCode_l K i₀).val = i := congrArg Subtype.val hi₀
  have hz₀' : (numberCode_l K z₀).val = z := congrArg Subtype.val hz₀
  subst i z
  exact (PowerlessRootedRealSyntax.row_instance_l K hS hV hVTrace i₀ z₀).trans
    ((hJ i₀ z₀).trans (PowerlessRootedFamilyNormalizationReading.body_l K hS hU hUTrace i₀ z₀).symm)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessHereditaryRealRequestDerives.support_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, PowerlessHereditaryRealRequest.real_formula_l,
    PowerlessHereditaryClass.formula_l K, reading_formula_l, up, Term.eval_weakenBound, Term.eval]
  intro hBase ⟨hω, he, ho, hS⟩ hUClass hU
  obtain ⟨hωEq, heEq, hoEq⟩ := PowerlessHereditaryRealRequestDerives.normalize_l K hω he ho
  rw [hωEq] at hS hU
  let U : PowerlessRelativeClassStructure.type_l hℳ (η.freeVal .here) :=
    ⟨η.freeVal (.there (.there (.there (.there (.there .here))))), hUClass⟩
  obtain ⟨H, hTrace⟩ := PowerlessBMSQuotientReals.trace_exists_l K ⟨U.val, hU⟩
  obtain ⟨V, hVHC, hV, J, hVTrace, hJ⟩ :=
    PowerlessHereditaryFamilyNormalization.coded_l (hBase := hBase) K U hU hTrace
  refine ⟨V.val, hVHC, ?_, ?_⟩
  · exact hωEq.symm ▸ hV
  · rw [hωEq, heEq, hoEq]
    exact read_l K hS hU hV hTrace hVTrace hJ

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms read_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryFamilyNormalizationDerives
