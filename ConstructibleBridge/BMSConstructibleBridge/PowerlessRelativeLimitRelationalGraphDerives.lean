import BMSConstructibleBridge.PowerlessRelativeLimitRelationalGraph
import BMSConstructibleBridge.PowerlessRelativeLimitDeltaSeparationDerives

/-! # 固定层有界关系构图模式的原 Z₂ 推导

图的成员守卫明确保留指定层 C。模式只要求实际有限自由参数和两个母集
属于 C，不把基集或层序数本身偷偷加入这些成员前提。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitRelationalGraphDerives

open Logic FirstOrder ThirdOrderSemantics StabilityFrame SecondOrderObjectSyntax PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private def insert_m {Δ : SortContext ℒ} :
    VariableSubstitution ℒ (.set :: .set :: Δ) [.set, .set, .set, .set, .set] (.set :: .set :: .set :: Δ)
  | _, .here => .bvar (.there .here)
  | _, .there .here => .bvar .here
  | _, .there (.there v) => .fvar (.there (.there (.there v)))

private def matrix_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [.set, .set, .set, .set, .set] (.set :: .set :: .set :: Δ) :=
  φ.substitute (.map (fun {s} (v : Variable ([] : SortContext ℒ) s) => nomatch v) insert_m)

private theorem matrix_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 [] Δ) (B β C X Y R x y : carrier_l 𝒩) :
    (matrix_m φ).satisfies ((((((((η.pushFree C).pushFree β).pushFree B).pushBound X).pushBound Y).pushBound R).pushBound x).pushBound y) ↔
      φ.satisfies ((η.pushFree y).pushFree x) := by
  refine (Formula.satisfies_substitute _ _ φ).trans ?_
  apply Iff.of_eq
  apply congrArg (fun η => φ.satisfies η)
  apply Env.ext
  · intro _ v; nomatch v
  · intro s v
    cases s
    cases v with
    | here => rfl
    | there v => cases v <;> rfl

def graph_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [] (.set :: .set :: .set :: Δ) :=
  .forallE .set <| .imp (member_m (.bvar .here) (.fvar (.there (.there .here)))) <|
    .forallE .set <| .imp (member_m (.bvar .here) (.fvar (.there (.there .here)))) <|
      .existsE .set <| .conj (member_m (.bvar .here) (.fvar (.there (.there .here)))) <|
        .forallE .set <| .forallE .set <| .iff
          (value_m (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))
          (.conj (member_m (.bvar (.there .here)) (.bvar (.there (.there (.there (.there .here)))))) <|
            .conj (member_m (.bvar .here) (.bvar (.there (.there (.there .here))))) (matrix_m φ))

theorem graph_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 [] Δ) (B β C : carrier_l 𝒩) :
    (graph_m φ).satisfies (((η.pushFree C).pushFree β).pushFree B) ↔
      ∀ X, member_l 𝒩 X C → ∀ Y, member_l 𝒩 Y C → ∃ R, member_l 𝒩 R C ∧
        ∀ x y, value_l R x y ↔ member_l 𝒩 x X ∧ member_l 𝒩 y Y ∧ φ.satisfies ((η.pushFree y).pushFree x) := by
  simp only [graph_m, Formula.satisfies, value_formula_l, matrix_formula_l,
    member_m, member_l, Arguments.eval, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  rfl

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [] (.set :: .set :: .set :: Δ) :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m (.fvar .here)) <|
    .imp (PowerlessRelativeHierarchySyntax.level_m (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))) <|
      .imp (PowerlessRelativeHierarchySyntax.limit_m (.fvar (.there .here))) <|
        .imp (parameters_m Δ (.fvar (.there (.there .here)))
          (fun v => .fvar (.there (.there (.there v))))) (graph_m φ)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ)

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) :
    (sentence_m φ).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro ρ hBase hC hLimit hParams
  have hBase' := (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ ρ (.fvar .here)).mp hBase
  have hC' := (PowerlessRelativeHierarchySemantics.level_formula_l K ρ (.fvar .here)
    (.fvar (.there .here)) (.fvar (.there (.there .here)))).mp hC
  have hLimit' := (PowerlessRelativeHierarchySemantics.limit_formula_l ρ (.fvar (.there .here))).mp hLimit
  have hParams' := (parameters_formula_l Δ ρ (.fvar (.there (.there .here)))
    (fun v => .fvar (.there (.there (.there v))))).mp hParams
  let η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ :=
    ⟨(fun v => nomatch v), fun v => ρ.freeVal (.there (.there (.there v)))⟩
  have hρ : ρ = (((η.pushFree (ρ.freeVal (.there (.there .here)))).pushFree
      (ρ.freeVal (.there .here))).pushFree (ρ.freeVal .here)) := by
    apply Env.ext
    · intro _ v; nomatch v
    · intro s v
      cases s
      cases v with
      | here => rfl
      | there v => cases v with
        | here => rfl
        | there v => cases v <;> rfl
  change (graph_m φ).satisfies ρ
  rw [hρ]
  apply (graph_formula_l φ η _ _ _).mpr
  intro X hX Y hY
  exact PowerlessRelativeLimitRelationalGraph.exists_l hBase' hLimit' hC' hφ η hX hY hParams'

theorem derives_m {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ hφ)

#print axioms graph_formula_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitRelationalGraphDerives
