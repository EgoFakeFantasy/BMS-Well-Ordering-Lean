import BMSConstructibleBridge.PowerlessRelativeCutoffLimit
import BMSConstructibleBridge.PowerlessRelativeLimitSourceSeparation

/-! # 首个不可数截断层的实际基础源准备

截断层由已有内部层次构造取得；ω<Ω 与序数初段覆盖给出真正
层内的 ω，基集的全部成员也仍在该层。六条原基础公理已经可用，
但本文件不把这一层冒充完整 PowerlessTheory 模型。完整分离与
Collection 仍是必须补齐的缺口。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffSourcePreparation

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem exists_l (K : source_coding_l hℳ) {B ω Ω : SecondOrderQuotient.type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hω : SecondOrderOmega.omega_l hℳ ω) (hΩ : PowerlessRelativeOrdinalCutoff.first_l B ω Ω) :
    ∃ C, ∃ hωC : mem_l hℳ ω C, PowerlessRelativeHierarchySemantics.level_l hℳ B Ω C ∧
      (∀ x, mem_l hℳ x B → mem_l hℳ x C) ∧
        PowerlessRelativeLimitSourceBasics.basic_m.TrueIn
          (PowerlessMemberStructure.structure_l (ℳ := 𝒱) C ⟨ω, hωC⟩) := by
  obtain ⟨C, hC⟩ := PowerlessRelativeOrdinalCoverage.level_exists_l hℳ hBase hΩ.1
  have hωC := PowerlessRelativeOrdinalCoverage.covered_l hℳ K hBase Ω C hC ω
    (PowerlessRelativeCutoffBelow.omega_below_l (hBase := hBase) K hω hΩ)
  exact ⟨C, hωC, hC, PowerlessRelativeLevelClosure.base_l hℳ hBase hC,
    PowerlessRelativeLimitSourceBasics.basic_l hBase
      (PowerlessRelativeCutoffLimit.limit_l K hBase hω hΩ) hC hω hωC⟩

def schema_m : Formula ℒ [] [.set, .set, .set] :=
  let B : Term ℒ [] [.set, .set, .set] .set := .fvar .here
  let ω := .fvar (.there .here)
  let Ω := .fvar (.there (.there .here))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeOrdinalCutoff.first_m B ω Ω) <| .existsE .set <|
        .conj (PowerlessRelativeHierarchySyntax.level_m (B.weakenBound SetTheory.SetSort.set)
          (Ω.weakenBound SetTheory.SetSort.set) (.bvar .here)) <|
          .conj (SecondOrderObjectSyntax.member_m (ω.weakenBound SetTheory.SetSort.set) (.bvar .here))
            (PowerlessRelativeParameters.instance_m PowerlessRelativeLimitSourceBasics.basic_m
              (.bvar .here) (fun v => nomatch v))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) : sentence_m.TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hBase hω hΩ
  have hBase' := (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ η (.fvar .here)).mp hBase
  have hω' := (SecondOrderOmegaSyntax.omega_l hℳ η (.fvar (.there .here))).mp hω
  have hΩ' := (PowerlessRelativeOrdinalCutoff.first_formula_l K η (.fvar .here)
    (.fvar (.there .here)) (.fvar (.there (.there .here)))).mp hΩ
  obtain ⟨C, hωC, hC, _, hBasic⟩ := exists_l K hBase' hω' hΩ'
  refine ⟨C, ?_, hωC, ?_⟩
  · simp only [PowerlessRelativeHierarchySemantics.level_formula_l K, Term.eval_weakenBound, Term.eval]
    exact hC
  · exact (PowerlessRelativeParameters.instance_l PowerlessRelativeLimitSourceBasics.basic_m
      (η.pushBound C) (.bvar .here) (fun v => nomatch v) Env.empty rfl (fun v => nomatch v)).mpr hBasic

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffSourcePreparation
