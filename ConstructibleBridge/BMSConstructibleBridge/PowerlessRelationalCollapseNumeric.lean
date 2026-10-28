import BMSConstructibleBridge.PowerlessRelationalCollapseHereditary
import BMSConstructibleBridge.PowerlessRelativeClassInjectionEnumeration

/-! # 数码源域的坍缩遗传出口，枚举在证明内构造

纯隶属 ℒ，原 Z₂。I⊆ω 的类内恒等单射被逆成满射，默认值直接取
原 H 求值证书中的源点 x，故无额外非空守卫或 Type 选择。共同局部
解预算仍是唯一待构造的核心守卫；本模块不宣称无条件解码闭包。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseNumeric

open Logic FirstOrder StabilityFrame ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B : type_l hℳ}
  {hBase : ∀ a, mem_l hℳ a B → ∀ b, mem_l hℳ b a → mem_l hℳ b B}

local notation "Raw" => type_l hℳ
local notation "Class" => PowerlessRelativeClassStructure.type_l hℳ B
local notation "𝒩" => PowerlessRelativeClassStructure.structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

include hBase in
/-- 任意类内非空数域子集的实际枚举；不假定其传递。 -/
theorem enumeration_l (O I d : Class)
    (hSub : ∀ a, mem_l hℳ a I.val → mem_l hℳ a O.val)
    (hd : mem_l hℳ d.val I.val) :
    ∃ f : Class, SecondOrderFunctionObjects.map_l hℳ f.val O.val I.val ∧
      ∀ a, mem_l hℳ a I.val → ∃ n, mem_l hℳ n O.val ∧
        SecondOrderFunctionObjects.value_l hℳ f.val n a := by
  let φ : Formula ℒ [] [.set, .set] := .equal (.fvar .here) (.fvar (.there .here))
  obtain ⟨R, hR, hRead⟩ := PowerlessRelativeClassFunctionRelation.exists_l
    (hBase := hBase) (φ := φ) (show Formula.IsDelta0 membershipLevyBound φ from .equal _ _)
    (Env.empty (M := 𝒩)) I O (by
      intro a ha
      exact ⟨a, ⟨hSub a.val ha, rfl⟩, fun _ hz => hz.2.symm⟩)
  have hInjective (a b i : Class) (hai : value_l (ℳ := 𝒩) R a i)
      (hbi : value_l (ℳ := 𝒩) R b i) : a = b :=
    ((hRead a i).mp hai).2.2.trans ((hRead b i).mp hbi).2.2.symm
  obtain ⟨f, hf, hOnto, _⟩ := PowerlessRelativeClassInjectionEnumeration.exists_l hR hInjective hd
  exact ⟨f, (PowerlessRelativeClassFunctionAbsolute.map_l f O I).mp hf,
    (PowerlessRelativeClassFunctionAbsolute.onto_l f O I).mp hOnto⟩

include hBase in
theorem hereditary_l (K : PowerlessBMSQuotientCoding.source_coding_l hℳ)
    {β C A I T H ω x X : Raw}
    (hC : PowerlessRelativeHierarchySemantics.level_l hℳ B β C)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hAC : mem_l hℳ A C) (hIC : mem_l hℳ I C)
    (hH : SecondOrderCollapseFunction.spec_l hℳ A I T H)
    (hWitness : PowerlessRelationalCollapseBoundedGraph.witness_l A I C)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hSub : ∀ a, mem_l hℳ a I → mem_l hℳ a ω)
    (hValue : SecondOrderFunctionObjects.value_l hℳ H x X) :
    PowerlessHereditaryClass.member_l hℳ B X := by
  let I₀ : Class := ⟨I, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase
    (PowerlessRelativeLevelClosure.class_l hℳ hBase hC) hIC⟩
  let O : Class := ⟨ω, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ hω)⟩
  have hx := (SecondOrderFunctionProperties.value_mem_l hℳ hH.2.1 hValue).1
  let x₀ : Class := ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase I₀.property hx⟩
  obtain ⟨f, hf, hOnto⟩ := enumeration_l (hBase := hBase) O I₀ x₀ hSub hx
  exact PowerlessRelationalCollapseHereditary.hereditary_l K hBase hC hLimit hAC hIC hH hWitness
    hω f.property hf hOnto hValue

def schema_m {Δ : SortContext ℒ} (B β C A I T H ω x X : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.level_m B β C) <|
      .imp (PowerlessRelativeHierarchySyntax.limit_m β) <|
        .imp (SecondOrderObjectSyntax.member_m A C) <|
          .imp (SecondOrderObjectSyntax.member_m I C) <|
            .imp (SecondOrderCollapseSyntax.formula_m A I T H) <|
              .imp (PowerlessRelationalCollapseBoundedGraph.witness_m A I C) <|
                .imp (SecondOrderOmegaSyntax.omega_m ω) <|
                  .imp (ThirdOrderTheory.subset_m I ω) <|
                    .imp (SecondOrderObjectSyntax.value_m H x X) (PowerlessHereditaryClass.formula_m B X)

def sentence_m {Δ : SortContext ℒ} (B β C A I T H ω x X : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B β C A I T H ω x X)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B β C A I T H ω x X : Term ℒ [] Δ .set) : (sentence_m B β C A I T H ω x X).TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeHierarchySemantics.limit_formula_l,
    SecondOrderCollapseSyntax.formula_l, PowerlessRelationalCollapseBoundedGraph.witness_formula_l,
    SecondOrderOmegaSyntax.omega_l, ThirdOrderSemantics.subset_formula_l, ThirdOrderSemantics.subset_l,
    ThirdOrderSemantics.member_l, SecondOrderObjectSyntax.value_l, PowerlessHereditaryClass.formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  exact fun hBase hC hLimit hAC hIC hH hWitness hω hSub hValue =>
    hereditary_l (hBase := hBase) K hC hLimit hAC hIC hH hWitness hω hSub hValue

theorem derives_m {Δ : SortContext ℒ} (B β C A I T H ω x X : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m B β C A I T H ω x X)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B β C A I T H ω x X)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseNumeric
