import BMSConstructibleBridge.PowerlessRelativeClassCodedCoverage

/-! # 原 Z₂ 可推导的 Class 局部覆盖存在句

保留原十七见证矩阵的完整 AST，只将其量词相对化到实际 Class。
类参数与原 B 参数通过显式替换认同；不要求编码参数属于待反射子域。
正式出口仅保留 B 传递、实际 ω 和 x 的 Class 守卫，没有首 Ω／W、
历史、Sat、Def 图、Collection 或元素性前提。这仍不是最终 BMS 句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCodedCoverageDerives

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

private abbrev context_m : SortContext ℒ := [.set, .set, .set]

private def formula_m : Formula ℒ [] context_m :=
  PowerlessCodedHistoryCoverageSyntax.result_m (.fvar (.there (.there .here)))
    (.fvar (.there .here)) (.fvar .here)

private def substitution_m : Substitution ℒ [] (.set :: context_m) [] context_m :=
  .map (fun v => nomatch v) (fun {s} v => match s, v with
    | .set, .here => .fvar (.there (.there .here))
    | .set, .there .here => .fvar .here
    | .set, .there (.there .here) => .fvar (.there .here)
    | .set, .there (.there (.there .here)) => .fvar (.there (.there .here)))

def result_m : Formula ℒ [] context_m :=
  (PowerlessRelativeClassRelativization.formula_m formula_m).substitute substitution_m

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

private theorem formula_l (K : source_coding_l hℳ)
    (η : Env (PowerlessRelativeClassStructure.structure_l hℳ B hBase) [] context_m)
    (hB : (η.freeVal (.there (.there .here))).val = B) :
    result_m.satisfies (PowerlessRelativeClassRelativization.env_l η) ↔ formula_m.satisfies η := by
  rw [result_m, Formula.satisfies_substitute]
  have hη : (PowerlessRelativeClassRelativization.env_l η).pullback substitution_m =
      (PowerlessRelativeClassRelativization.env_l η).pushFree (sort := SetTheory.SetSort.set) B := by
    apply Env.ext
    · intro _ v; nomatch v
    · intro s v
      cases s
      cases v with
      | here => exact hB
      | there v =>
        cases v with
        | here => rfl
        | there v =>
          cases v with
          | here => rfl
          | there v => cases v with
            | here => rfl
            | there v => nomatch v
  rw [hη]
  exact PowerlessRelativeClassRelativization.formula_l K formula_m η

def schema_m : Formula ℒ [] context_m :=
  let B : Term ℒ [] context_m .set := .fvar (.there (.there .here))
  let ω := .fvar (.there .here)
  let x := .fvar .here
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B x) result_m

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeHierarchySemantics.class_formula_l K, Term.eval]
  intro hBase hω hx
  let B := η.freeVal (.there (.there .here))
  let B₀ : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  let ω₀ : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨η.freeVal (.there .here), PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
      (hωEq.symm ▸ SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)⟩
  let x₀ : PowerlessRelativeClassStructure.type_l hℳ B := ⟨η.freeVal .here, hx⟩
  let ξ : Env (PowerlessRelativeClassStructure.structure_l hℳ B hBase) [] context_m :=
    Env.empty |>.pushFree B₀ |>.pushFree ω₀ |>.pushFree x₀
  have hφ : formula_m.satisfies ξ :=
    (PowerlessCodedHistoryCoverageSyntax.result_formula_l
      (PowerlessRelativeClassStructure.ext_l hℳ B hBase) ξ
      (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)).mpr
      (PowerlessRelativeClassCodedCoverage.exists_l (hBase := hBase) K ω₀ x₀ hω)
  have hη : PowerlessRelativeClassRelativization.env_l ξ = η := by
    apply Env.ext
    · intro _ v; nomatch v
    · intro s v
      cases s
      cases v with
      | here => rfl
      | there v => cases v with
        | here => rfl
        | there v => cases v with
          | here => rfl
          | there v => nomatch v
  exact hη ▸ (formula_l K ξ rfl).mpr hφ

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCodedCoverageDerives
