import BMSConstructibleBridge.PowerlessRelationalCollapseNumericOrderIndex
import BMSConstructibleBridge.PowerlessRelationalCollapseOrderedClass

/-! # 数码前驱优先良序的预算无参数坍缩出口

纯隶属 ℒ，原 Z₂。实际 I⊆ω 上的 J 已是前驱优先环境良序时，
P、序数域、预算 Q 和共同局部覆盖全部在证明内产生。
仍保留 J 的实际存在性守卫；没有把任意根良基码的线序化当作假设已消去。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseNumericOrderedClass

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem class_l (K : PowerlessBMSQuotientCoding.source_coding_l hℳ) {B ω A I J T H : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hSub : ∀ x, mem_l hℳ x I → mem_l hℳ x ω)
    (hA : PowerlessRelativeClassCorrespondence.member_l hℳ B A)
    (hI : PowerlessRelativeClassCorrespondence.member_l hℳ B I)
    (hJClass : PowerlessRelativeClassCorrespondence.member_l hℳ B J)
    (hRelation : SecondOrderRegularRelation.relation_l hℳ J I)
    (hJ : wellOrder_l (ℳ := 𝒱) I J)
    (hExtends : PowerlessRelationalCollapseOrderedCut.extends_l I A J)
    (hH : SecondOrderCollapseFunction.spec_l hℳ A I T H) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B H ∧
      PowerlessRelativeClassCorrespondence.member_l hℳ B T := by
  obtain ⟨_α, _P, hP⟩ := PowerlessRelationalCollapseNumericOrderIndex.exists_l hω hSub hRelation hJ
  exact PowerlessRelationalCollapseOrderedClass.class_l K hBase hA hI hJClass hJ hExtends hH hP

def schema_m {Δ : SortContext ℒ} (B ω A I J T H : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (ThirdOrderTheory.subset_m I ω) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B A) <|
          .imp (PowerlessRelativeHierarchySyntax.class_m B I) <|
            .imp (PowerlessRelativeHierarchySyntax.class_m B J) <|
              .imp (SecondOrderRelationSyntax.relation_m J I) <|
                .imp (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m I J) <|
                  .imp (PowerlessRelationalCollapseOrderedCut.extends_m I A J) <|
                    .imp (SecondOrderCollapseSyntax.formula_m A I T H) <|
                      .conj (PowerlessRelativeHierarchySyntax.class_m B H)
                        (PowerlessRelativeHierarchySyntax.class_m B T)

def sentence_m {Δ : SortContext ℒ} (B ω A I J T H : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B ω A I J T H)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B ω A I J T H : Term ℒ [] Δ .set) : (sentence_m B ω A I J T H).TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l, SecondOrderOmegaSyntax.omega_l,
    ThirdOrderSemantics.subset_formula_l, ThirdOrderSemantics.subset_l, ThirdOrderSemantics.member_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderRelationSyntax.relation_l,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    PowerlessRelationalCollapseOrderedCut.extends_formula_l, SecondOrderCollapseSyntax.formula_l]
  exact fun hBase hω hSub hA hI hJClass hRelation hJ hExtends hH =>
    class_l (hℳ := hℳ) K hBase hω hSub hA hI hJClass hRelation hJ hExtends hH

theorem derives_m {Δ : SortContext ℒ} (B ω A I J T H : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m B ω A I J T H)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B ω A I J T H)

#print axioms class_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseNumericOrderedClass
