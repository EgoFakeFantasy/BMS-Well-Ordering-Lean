import BMSConstructibleBridge.PowerlessRelationalCollapseNumericOrderedClass
import BMSConstructibleBridge.PowerlessRelationalCollapseNumeric

/-! # 原数码坍缩值的实际遗传包络

纯隶属 ℒ，原 Z₂。给定前驱优先类内环境良序 J 后，索引、预算及
H/T 的类资格都由证明构造。源 I 的内部 ω 枚举以实际求值源点为缺省，
复合图的整张类资格及精确满射同时核验；结论针对原 H 的同一值 X。
仍未从任意根良基实数构造 J，不宣称无条件解码或遗传 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseNumericOrderedHereditary

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem hereditary_l (K : PowerlessBMSQuotientCoding.source_coding_l hℳ) {B ω A I J T H x X : Raw}
    (hBase : ∀ a, mem_l hℳ a B → ∀ b, mem_l hℳ b a → mem_l hℳ b B)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hSub : ∀ a, mem_l hℳ a I → mem_l hℳ a ω)
    (hA : PowerlessRelativeClassCorrespondence.member_l hℳ B A)
    (hI : PowerlessRelativeClassCorrespondence.member_l hℳ B I)
    (hJClass : PowerlessRelativeClassCorrespondence.member_l hℳ B J)
    (hRelation : SecondOrderRegularRelation.relation_l hℳ J I)
    (hJ : wellOrder_l (ℳ := 𝒱) I J)
    (hExtends : PowerlessRelationalCollapseOrderedCut.extends_l I A J)
    (hH : SecondOrderCollapseFunction.spec_l hℳ A I T H)
    (hValue : SecondOrderFunctionObjects.value_l hℳ H x X) :
    PowerlessHereditaryClass.member_l hℳ B X := by
  obtain ⟨hHClass, hTClass⟩ := PowerlessRelationalCollapseNumericOrderedClass.class_l
    K hBase hω hSub hA hI hJClass hRelation hJ hExtends hH
  let I₀ : PowerlessRelativeClassStructure.type_l hℳ B := ⟨I, hI⟩
  let O : PowerlessRelativeClassStructure.type_l hℳ B := ⟨ω,
    PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase (SecondOrderOmegaOrdinal.ordinal_l hℳ hω)⟩
  have hx := (SecondOrderFunctionProperties.value_mem_l hℳ hH.2.1 hValue).1
  let x₀ : PowerlessRelativeClassStructure.type_l hℳ B := ⟨x,
    PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hI hx⟩
  obtain ⟨f, hf, hOnto⟩ := PowerlessRelationalCollapseNumeric.enumeration_l
    (hBase := hBase) O I₀ x₀ hSub hx
  exact PowerlessRelationalCollapseHereditary.envelope_l
    K hBase hI hHClass hTClass hH hω f.property hf hOnto hValue

def schema_m {Δ : SortContext ℒ} (B ω A I J T H x X : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
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
                      .imp (SecondOrderObjectSyntax.value_m H x X) (PowerlessHereditaryClass.formula_m B X)

def sentence_m {Δ : SortContext ℒ} (B ω A I J T H x X : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B ω A I J T H x X)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B ω A I J T H x X : Term ℒ [] Δ .set) : (sentence_m B ω A I J T H x X).TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l, SecondOrderOmegaSyntax.omega_l,
    ThirdOrderSemantics.subset_formula_l, ThirdOrderSemantics.subset_l, ThirdOrderSemantics.member_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderRelationSyntax.relation_l,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    PowerlessRelationalCollapseOrderedCut.extends_formula_l, SecondOrderCollapseSyntax.formula_l,
    SecondOrderObjectSyntax.value_l, PowerlessHereditaryClass.formula_l K]
  exact fun hBase hω hSub hA hI hJClass hRelation hJ hExtends hH hValue =>
    hereditary_l (hℳ := hℳ) K hBase hω hSub hA hI hJClass hRelation hJ hExtends hH hValue

theorem derives_m {Δ : SortContext ℒ} (B ω A I J T H x X : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m B ω A I J T H x X)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B ω A I J T H x X)

#print axioms hereditary_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseNumericOrderedHereditary
