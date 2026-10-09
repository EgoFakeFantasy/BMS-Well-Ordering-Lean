import BMSConstructibleBridge.PowerlessRelationalCollapseRange
import BMSConstructibleBridge.PowerlessRelativeClassFunctionComposition
import BMSConstructibleBridge.PowerlessHereditaryClass

/-! # 有界坍缩的实际遗传对象出口

纯隶属 ℒ，原 Z₂。源 I 由实际类内 f 在内部 ω 上满射枚举，
坍缩后的同一 H/T 由共同局部预算取得类内资格。实际复合图枚举 T，
原 H 的任一值 X 因此有遗传包络；不预供 X 的 Class 或遗传假设。
共同局部预算和源枚举仍是明确守卫，不代表任意良基码解码已完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseHereditary

open Logic FirstOrder StabilityFrame
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 已取得同一图和值域的类资格时，实际复合枚举给原值的遗传包络。 -/
theorem envelope_l (K : PowerlessBMSQuotientCoding.source_coding_l hℳ)
    {B A I T H ω f x X : Raw}
    (hBase : ∀ a, mem_l hℳ a B → ∀ b, mem_l hℳ b a → mem_l hℳ b B)
    (hIClass : PowerlessRelativeClassCorrespondence.member_l hℳ B I)
    (hHClass : PowerlessRelativeClassCorrespondence.member_l hℳ B H)
    (hTClass : PowerlessRelativeClassCorrespondence.member_l hℳ B T)
    (hH : SecondOrderCollapseFunction.spec_l hℳ A I T H)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hf : PowerlessRelativeClassCorrespondence.member_l hℳ B f)
    (hMap : SecondOrderFunctionObjects.map_l hℳ f ω I)
    (hOnto : ∀ a, mem_l hℳ a I → ∃ n, mem_l hℳ n ω ∧ SecondOrderFunctionObjects.value_l hℳ f n a)
    (hValue : SecondOrderFunctionObjects.value_l hℳ H x X) :
    PowerlessHereditaryClass.member_l hℳ B X := by
  let I₀ : PowerlessRelativeClassStructure.type_l hℳ B := ⟨I, hIClass⟩
  let T₀ : PowerlessRelativeClassStructure.type_l hℳ B := ⟨T, hTClass⟩
  let H₀ : PowerlessRelativeClassStructure.type_l hℳ B := ⟨H, hHClass⟩
  let F₀ : PowerlessRelativeClassStructure.type_l hℳ B := ⟨f, hf⟩
  let O : PowerlessRelativeClassStructure.type_l hℳ B := ⟨ω,
    PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase (SecondOrderOmegaOrdinal.ordinal_l hℳ hω)⟩
  have hF := (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) F₀ O I₀).mpr hMap
  have hG := (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) H₀ I₀ T₀).mpr hH.2.1
  obtain ⟨P, hP, hRead⟩ := PowerlessRelativeClassFunctionComposition.exists_l hF hG
  have hPOnto : ∀ y, mem_l hℳ y T → ∃ n, mem_l hℳ n ω ∧
      SecondOrderFunctionObjects.value_l hℳ P.val n y := by
    intro y hy
    obtain ⟨a, ha, hay⟩ := hH.2.2.1 y hy
    obtain ⟨n, hn, hna⟩ := hOnto a ha
    let a₀ : PowerlessRelativeClassStructure.type_l hℳ B :=
      ⟨a, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase I₀.property ha⟩
    let n₀ : PowerlessRelativeClassStructure.type_l hℳ B :=
      ⟨n, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase O.property hn⟩
    let y₀ : PowerlessRelativeClassStructure.type_l hℳ B :=
      ⟨y, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase T₀.property hy⟩
    exact ⟨n, hn, (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) P n₀ y₀).mp
      ((hRead n₀ y₀).mpr ⟨hn, hy, a₀, ha,
        (PowerlessRelativeClassFunctionAbsolute.value_l F₀ n₀ a₀).mpr hna,
        (PowerlessRelativeClassFunctionAbsolute.value_l H₀ a₀ y₀).mpr hay⟩)⟩
  exact ⟨T, P.val, ω, hTClass, P.property,
    (SecondOrderFunctionProperties.value_mem_l hℳ hH.2.1 hValue).2,
    (fun a ha b hb => hH.1 a b ha hb), hω,
    (PowerlessRelativeClassFunctionAbsolute.map_l P O T₀).mp hP, hPOnto⟩

theorem hereditary_l (K : PowerlessBMSQuotientCoding.source_coding_l hℳ)
    {B β C A I T H ω f x X : Raw}
    (hBase : ∀ a, mem_l hℳ a B → ∀ b, mem_l hℳ b a → mem_l hℳ b B)
    (hC : PowerlessRelativeHierarchySemantics.level_l hℳ B β C)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hAC : mem_l hℳ A C) (hIC : mem_l hℳ I C)
    (hH : SecondOrderCollapseFunction.spec_l hℳ A I T H)
    (hWitness : PowerlessRelationalCollapseBoundedGraph.witness_l A I C)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hf : PowerlessRelativeClassCorrespondence.member_l hℳ B f)
    (hMap : SecondOrderFunctionObjects.map_l hℳ f ω I)
    (hOnto : ∀ a, mem_l hℳ a I → ∃ n, mem_l hℳ n ω ∧ SecondOrderFunctionObjects.value_l hℳ f n a)
    (hValue : SecondOrderFunctionObjects.value_l hℳ H x X) :
    PowerlessHereditaryClass.member_l hℳ B X := by
  obtain ⟨hHClass, hTClass⟩ := PowerlessRelationalCollapseRange.closure_l
    hBase hC hLimit hAC hIC hH hWitness
  have hIClass := PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase
    (PowerlessRelativeLevelClosure.class_l hℳ hBase hC) hIC
  exact envelope_l K hBase hIClass hHClass hTClass hH hω hf hMap hOnto hValue

def schema_m {Δ : SortContext ℒ}
    (B β C A I T H ω f x X : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.level_m B β C) <|
      .imp (PowerlessRelativeHierarchySyntax.limit_m β) <|
        .imp (SecondOrderObjectSyntax.member_m A C) <|
          .imp (SecondOrderObjectSyntax.member_m I C) <|
            .imp (SecondOrderCollapseSyntax.formula_m A I T H) <|
              .imp (PowerlessRelationalCollapseBoundedGraph.witness_m A I C) <|
                .imp (SecondOrderOmegaSyntax.omega_m ω) <|
                  .imp (PowerlessRelativeHierarchySyntax.class_m B f) <|
                    .imp (SecondOrderObjectSyntax.map_m f ω I) <|
                      .imp (PowerlessMemberDefSyntax.onto_m ω I f) <|
                        .imp (SecondOrderObjectSyntax.value_m H x X) (PowerlessHereditaryClass.formula_m B X)

def sentence_m {Δ : SortContext ℒ}
    (B β C A I T H ω f x X : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B β C A I T H ω f x X)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B β C A I T H ω f x X : Term ℒ [] Δ .set) : (sentence_m B β C A I T H ω f x X).TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeHierarchySemantics.limit_formula_l,
    SecondOrderCollapseSyntax.formula_l, PowerlessRelationalCollapseBoundedGraph.witness_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeHierarchySemantics.class_formula_l K,
    SecondOrderObjectSyntax.map_l, PowerlessMemberDefFormulaSemantics.onto_formula_l,
    SecondOrderObjectSyntax.value_l, PowerlessHereditaryClass.formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  exact fun hBase hC hLimit hAC hIC hH hWitness hω hf hMap hOnto hValue =>
    hereditary_l K hBase hC hLimit hAC hIC hH hWitness hω hf hMap hOnto hValue

theorem derives_m {Δ : SortContext ℒ} (B β C A I T H ω f x X : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m B β C A I T H ω f x X)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B β C A I T H ω f x X)

#print axioms envelope_l
#print axioms hereditary_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseHereditary
