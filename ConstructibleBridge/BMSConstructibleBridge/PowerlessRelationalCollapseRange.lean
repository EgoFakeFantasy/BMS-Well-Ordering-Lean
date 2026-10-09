import BMSConstructibleBridge.PowerlessRelationalCollapseBoundedGraph
import BMSConstructibleBridge.PowerlessRelativeClassFunctionRange

/-! # 保持原坍缩图与满射值域的类内资格

纯隶属 ℒ，原 Z₂。已有实际类内函数图给出精确全 raw 值域；
原坍缩的满射规格认同同一个 T，不需要 T 的预先 Class 假设。
有界覆盖版同时输出 H/T 的资格；实际共同局部预算仍待构造。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseRange

open Logic FirstOrder StabilityFrame
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem range_l {B A I T H : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hI : PowerlessRelativeClassCorrespondence.member_l hℳ B I)
    (hHClass : PowerlessRelativeClassCorrespondence.member_l hℳ B H)
    (hH : SecondOrderCollapseFunction.spec_l hℳ A I T H) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B T := by
  obtain ⟨R, hR⟩ := PowerlessRelativeClassFunctionRange.exists_l hBase
    ⟨I, hI⟩ ⟨H, hHClass⟩ (q := T) (by exact hH.2.1)
  have hEq : R.val = T := by
    apply SecondOrderQuotient.ext_l hℳ
    intro y
    rw [hR y]
    constructor
    · rintro ⟨x, hxy⟩
      exact (SecondOrderFunctionProperties.value_mem_l hℳ hH.2.1 hxy).2
    · intro hy
      obtain ⟨x, _, hxy⟩ := hH.2.2.1 y hy
      exact ⟨x, hxy⟩
  exact hEq ▸ R.property

theorem closure_l {B β C A I T H : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hC : PowerlessRelativeHierarchySemantics.level_l hℳ B β C)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hAC : mem_l hℳ A C) (hIC : mem_l hℳ I C)
    (hH : SecondOrderCollapseFunction.spec_l hℳ A I T H)
    (hWitness : PowerlessRelationalCollapseBoundedGraph.witness_l A I C) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B H ∧
      PowerlessRelativeClassCorrespondence.member_l hℳ B T := by
  have hI := PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase
    (PowerlessRelativeLevelClosure.class_l hℳ hBase hC) hIC
  have hHClass := PowerlessRelationalCollapseBoundedGraph.class_l hBase hC hLimit hAC hIC hH hWitness
  exact ⟨hHClass, range_l hBase hI hHClass hH⟩

def schema_m {Δ : SortContext ℒ} (B β C A I T H : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.level_m B β C) <|
      .imp (PowerlessRelativeHierarchySyntax.limit_m β) <|
        .imp (SecondOrderObjectSyntax.member_m A C) <|
          .imp (SecondOrderObjectSyntax.member_m I C) <|
            .imp (SecondOrderCollapseSyntax.formula_m A I T H) <|
              .imp (PowerlessRelationalCollapseBoundedGraph.witness_m A I C) <| .conj
                (PowerlessRelativeHierarchySyntax.class_m B H)
                (PowerlessRelativeHierarchySyntax.class_m B T)

def sentence_m {Δ : SortContext ℒ} (B β C A I T H : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B β C A I T H)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B β C A I T H : Term ℒ [] Δ .set) : (sentence_m B β C A I T H).TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeHierarchySemantics.limit_formula_l,
    SecondOrderCollapseSyntax.formula_l, PowerlessRelationalCollapseBoundedGraph.witness_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderObjectSyntax.member_m, Arguments.eval]
  exact fun hBase hC hLimit hAC hIC hH hWitness => closure_l hBase hC hLimit hAC hIC hH hWitness

theorem derives_m {Δ : SortContext ℒ} (B β C A I T H : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m B β C A I T H)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B β C A I T H)

#print axioms range_l
#print axioms closure_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseRange
