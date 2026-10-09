import BMSConstructibleBridge.PowerlessRelativeSourceSkolemFamily

/-! # 原截断层中共同构造有限见证族

排序图 R 由同一实际首不可数截断构造；全部原矩阵的图随后在一个对象
存在块内共同绑定，并保留每张图的原规格和同一标签算子的实际性质。
原有限参数及互异标签明确留在守卫中，不预供任何源见证图或排序图。
此处仍不是源模型 Collection、闭包塌缩或最终 fixed-H 良序推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffSkolemFamily

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev free {Ε : SortContext ℒ} (t : Term ℒ [] Ε .set) :=
  t.weakenFree SetTheory.SetSort.set

def conclusion_m {Ε Δ : SortContext ℒ}
    (F : List (Formula ℒ [] (.set :: .set :: Δ))) (T : List (Variable Δ .set))
    (B W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) : Formula ℒ [] Ε :=
  let R : Term ℒ [] (.set :: Ε) .set := .fvar .here
  (Formula.conj (PowerlessRelativeHierarchySyntax.class_m (free B) R) <|
    .conj (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m (free W) R)
      (PowerlessRelativeSourceSkolemFamily.conclusion_m F T (free B) (free W) R
        (fun v => free (τ v)))).existsFreeTop .set

private abbrev context_m (Δ : SortContext ℒ) := .set :: .set :: .set :: .set :: .set :: Δ

def schema_m {Δ : SortContext ℒ}
    (F : List (Formula ℒ [] (.set :: .set :: Δ))) (T : List (Variable Δ .set)) :
    Formula ℒ [] (context_m Δ) :=
  let W : Term ℒ [] (context_m Δ) .set := .fvar .here
  let Ω := .fvar (.there .here)
  let ω := .fvar (.there (.there .here))
  let P₀ := .fvar (.there (.there (.there .here)))
  let B := .fvar (.there (.there (.there (.there .here))))
  let τ : Variable Δ .set → Term ℒ [] (context_m Δ) .set :=
    fun v => .fvar (.there (.there (.there (.there (.there v)))))
  .imp (SecondOrderCanonicalLevelDerives.guard_m B P₀) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B P₀) <|
      .imp (SecondOrderOmegaSyntax.omega_m ω) <|
        .imp (PowerlessRelativeOrdinalCutoff.first_m B ω Ω) <|
          .imp (PowerlessRelativeHierarchySyntax.level_m B Ω W) <|
            .imp (SecondOrderObjectSyntax.member_m B W) <|
              .imp (parameters_m Δ W τ) <|
                .imp (PowerlessRelativeSourceSkolemFamily.distinct_m T τ) (conclusion_m F T B W τ)

def sentence_m {Δ : SortContext ℒ}
    (F : List (Formula ℒ [] (.set :: .set :: Δ))) (T : List (Variable Δ .set)) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m F T)

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (F : List (Formula ℒ [] (.set :: .set :: Δ))) (T : List (Variable Δ .set))
    (hLength : T.length = F.length) :
    (sentence_m F T).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, SecondOrderCanonicalLevelDerives.guard_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeOrdinalCutoff.first_formula_l K,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval]
  intro ζ hSeed hP₀ hω hΩ hW hBW hParams hDistinct
  let W : Term ℒ [] (context_m Δ) .set := .fvar .here
  let B : Term ℒ [] (context_m Δ) .set := .fvar (.there (.there (.there (.there .here))))
  let τ : Variable Δ .set → Term ℒ [] (context_m Δ) .set :=
    fun v => .fvar (.there (.there (.there (.there (.there v)))))
  have hBase : ∀ x, mem_l hℳ x (B.eval ζ) → ∀ y, mem_l hℳ y x → mem_l hℳ y (B.eval ζ) :=
    fun x hx y hy => hSeed.2.1 x y hx hy
  have hClass := PowerlessRelativeLevelClosure.class_l hℳ hBase hW
  obtain ⟨R, hR⟩ := PowerlessRelativeCutoffClassWellOrder.exists_l K ⟨_, hP₀⟩ hSeed hω hΩ hW
  let ξ : Env (SecondOrderQuotient.structure_l hℳ) [] (.set :: context_m Δ) := ζ.pushFree R.val
  have hParams' := (parameters_formula_l Δ ζ W τ).mp hParams
  have hParameters : (parameters_m Δ (free W) (fun v => free (τ v))).satisfies ξ := by
    apply (parameters_formula_l Δ ξ (free W) (fun v => free (τ v))).mpr
    intro s v; cases s
    exact hParams' _ v
  have hTags : (PowerlessRelativeSourceSkolemFamily.distinct_m T
      (fun v => free (τ v))).satisfies ξ := by
    apply (PowerlessRelativeSourceSkolemFamily.distinct_formula_l T (fun v => free (τ v)) ξ).mpr
    simpa only [free, Term.eval_weakenFree, ξ] using
      (PowerlessRelativeSourceSkolemFamily.distinct_formula_l T τ ζ).mp hDistinct
  have hSource := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
    (PowerlessRelativeSourceSkolemFamily.models_l hℳ F T hLength
      (free B) (free W) (.fvar .here) (fun v => free (τ v))) ξ
  simp only [PowerlessRelativeSourceSkolemFamily.schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval,
    free, Term.eval_weakenFree, Term.eval, ξ] at hSource
  have hSource' := hSource hBase hClass R.property hR hBW hParameters hTags
  rw [conclusion_m, Formula.satisfies_existsFreeTop]
  refine ⟨R.val, ?_⟩
  simp only [Formula.satisfies, PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    free, Term.eval_weakenFree, Term.eval]
  exact ⟨R.property, hR, hSource'⟩

theorem derives_m {Δ : SortContext ℒ}
    (F : List (Formula ℒ [] (.set :: .set :: Δ))) (T : List (Variable Δ .set))
    (hLength : T.length = F.length) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m F T)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ F T hLength)

#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffSkolemFamily
