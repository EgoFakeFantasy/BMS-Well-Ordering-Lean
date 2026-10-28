import BMSConstructibleBridge.PowerlessRelativeClassFiniteSequencesDerives
import BMSConstructibleBridge.PowerlessRelativeClassFunctionAbsolute

/-! # 任意原商有限函数图提升到相对类

量词首先覆盖原商中的全部函数图，不把图属于类当作前提。ω 与陪域共取
一个极限层界后，内部有限函数共同界定理给出实际类成员关系。正式句子
保留环境全称量词，不能误用类相对化而把需要证明的成员条件藏入量词域。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFiniteMapLift

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem member_l {B ω X n f : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hωClass : PowerlessRelativeClassCorrespondence.member_l hℳ B ω)
    (hXClass : PowerlessRelativeClassCorrespondence.member_l hℳ B X)
    (hω : SecondOrderOmega.omega_l hℳ ω) (hn : mem_l hℳ n ω)
    (hf : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) f n X) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B f := by
  obtain ⟨α, C₀, hC₀, hωC₀, hXC₀⟩ := PowerlessRelativeClassBounds.common_l hℳ hBase hωClass hXClass
  obtain ⟨β, hβ, hαβ, hNoMax⟩ := SecondOrderOrdinalLimitDerives.exists_l hℳ α
    (PowerlessRelativeLevelClosure.ordinal_l hℳ hC₀)
  obtain ⟨C, hC⟩ := PowerlessRelativeOrdinalCoverage.level_exists_l hℳ hBase hβ
  have hωC := PowerlessRelativeLevelClosure.subset_l hℳ hBase hαβ hC₀ hC ω hωC₀
  have hXC := PowerlessRelativeLevelClosure.subset_l hℳ hBase hαβ hC₀ hC X hXC₀
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  have hfC := PowerlessRelativeLimitFiniteMaps.member_l hℳ hBase ⟨⟨α, hαβ⟩, hNoMax⟩
    hC K (hEq ▸ hωC) hXC (hEq ▸ hn) hf
  exact ⟨β, C, hC, hfC⟩

/-- 不改变原函数对象，仅取得其类内载体及同一映射规格。 -/
theorem lift_l {B : type_l hℳ}
    {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}
    {ω X : PowerlessRelativeClassStructure.type_l hℳ B}
    (hω : omega_l (ℳ := PowerlessRelativeClassStructure.structure_l hℳ B hBase) ω)
    {n f : type_l hℳ} (hn : mem_l hℳ n ω.val)
    (hf : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) f n X.val) :
    ∃ n' f' : PowerlessRelativeClassStructure.type_l hℳ B,
      n'.val = n ∧ f'.val = f ∧
      map_l (ℳ := PowerlessRelativeClassStructure.structure_l hℳ B hBase) f' n' X := by
  let n' : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨n, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property hn⟩
  let f' : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨f, member_l hBase ω.property X.property
      ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mp hω) hn hf⟩
  exact ⟨n', f', rfl, rfl,
    (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) f' n' X).mpr hf⟩

def schema_m : Formula ℒ [] [.set, .set, .set, .set, .set] :=
  let B : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar .here
  let ω : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let X : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let n : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let f : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B ω) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B X) <|
        .imp (SecondOrderOmegaSyntax.omega_m ω) <| .imp (member_m n ω) <|
          .imp (map_m f n X) (PowerlessRelativeHierarchySyntax.class_m B f)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ,
    PowerlessRelativeHierarchySemantics.class_formula_l K, omega_formula_l,
    map_formula_l, member_m, Arguments.eval, Term.eval]
  exact fun hBase hωClass hXClass hω hn hf => member_l hBase hωClass hXClass hω hn hf

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFiniteMapLift
