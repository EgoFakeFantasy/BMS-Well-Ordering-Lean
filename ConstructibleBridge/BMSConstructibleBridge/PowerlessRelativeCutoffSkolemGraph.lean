import BMSConstructibleBridge.PowerlessRelativeSourceSkolemGraph

/-! # 原截断层的实际总 Skolem 图

在同一首不可数截断层上先构造实际 Class 良序 R，再构造任意固定原矩阵
的总最小见证图 J。两个图均在原 Z₂ 证明中产生，不由调用者预供，亦不
要求它们属于截断层。原有限参数仍须属于该层，默认值为层内基底 B。
此处只解除排序图和逐输入见证守卫，不代替闭包、凝聚或完整源模型构造。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffSkolemGraph

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding StabilityFrame
open SecondOrderQuotient (mem_l)
open SecondOrderObjectSyntax (member_m)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Ε : SortContext ℒ} (t : Term ℒ Γ Ε .set) :=
  t.weakenBound SetTheory.SetSort.set

private def binding_m {Γ Ε Δ : SortContext ℒ}
    (B W R : Term ℒ Γ Ε .set) (τ : Variable Δ .set → Term ℒ Γ Ε .set) :
    Substitution ℒ [] (.set :: .set :: .set :: Δ) Γ Ε :=
  .map (fun v => nomatch v) (fun {s} v => match s with
    | .set => match v with
      | .here => W
      | .there .here => R
      | .there (.there .here) => B
      | .there (.there (.there v)) => τ v)

def witness_m {Γ Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B W R : Term ℒ Γ Ε .set) (τ : Variable Δ .set → Term ℒ Γ Ε .set) : Formula ℒ Γ Ε :=
  (PowerlessRelativeSourceSkolemGraph.conclusion_m φ).substitute (binding_m B W R τ)

theorem witness_formula_l {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ζ : Env 𝒱 Γ Ε) (B W R : Term ℒ Γ Ε .set)
    (τ : Variable Δ .set → Term ℒ Γ Ε .set) (η : Env 𝒱 [] Δ)
    (hτ : ∀ v, (τ v).eval ζ = η.freeVal v) :
    (witness_m φ B W R τ).satisfies ζ ↔
      (PowerlessRelativeSourceSkolemGraph.conclusion_m φ).satisfies
        (((η.pushFree (B.eval ζ)).pushFree (R.eval ζ)).pushFree (W.eval ζ)) := by
  rw [witness_m, Formula.satisfies_substitute]
  apply Iff.of_eq
  apply congrArg (fun ξ => (PowerlessRelativeSourceSkolemGraph.conclusion_m φ).satisfies ξ)
  apply Env.ext
  · intro s v; nomatch v
  · intro s v; cases s
    cases v with
    | here => rfl
    | there v => cases v with
      | here => rfl
      | there v => cases v with
        | here => rfl
        | there v => exact hτ v

def conclusion_m {Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) : Formula ℒ [] Ε :=
  .existsE .set <|
    .conj (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here)) <|
      .conj (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m (up W) (.bvar .here))
        (witness_m φ (up B) (up W) (.bvar .here) (fun v => up (τ v)))

private abbrev context_m (Δ : SortContext ℒ) := .set :: .set :: .set :: .set :: .set :: Δ

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
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
            .imp (member_m B W) <| .imp (parameters_m Δ W τ) (conclusion_m φ B W τ)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ)

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    (sentence_m φ).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, SecondOrderCanonicalLevelDerives.guard_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeOrdinalCutoff.first_formula_l K,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    member_m, Arguments.eval, Term.eval]
  intro ζ hSeed hP₀ hω hΩ hW hBW hParams
  let W := ζ.freeVal (.here : Variable (context_m Δ) .set)
  let B := ζ.freeVal (.there (.there (.there (.there (.here : Variable (.set :: Δ) .set)))))
  have hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B :=
    fun x hx y hy => hSeed.2.1 x y hx hy
  have hClass := PowerlessRelativeLevelClosure.class_l hℳ hBase hW
  obtain ⟨R, hR⟩ := PowerlessRelativeCutoffClassWellOrder.exists_l K ⟨_, hP₀⟩ hSeed hω hΩ hW
  have hParams' := (parameters_formula_l Δ ζ (.fvar .here)
    (fun v => .fvar (.there (.there (.there (.there (.there v))))))).mp hParams
  let η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with
        | .set => ζ.freeVal (.there (.there (.there (.there (.there v))))) }
  let ξ : Env (SecondOrderQuotient.structure_l hℳ) [] (.set :: .set :: .set :: Δ) :=
    ((η.pushFree B).pushFree R.val).pushFree W
  have hSource := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
    (PowerlessRelativeSourceSkolemGraph.models_l hℳ φ) ξ
  simp only [PowerlessRelativeSourceSkolemGraph.schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    member_m, Arguments.eval, Term.eval] at hSource
  have hParameters : (parameters_m Δ (.fvar .here)
      (fun v => .fvar (.there (.there (.there v))))).satisfies ξ := by
    apply (parameters_formula_l Δ ξ (.fvar .here)
      (fun v => .fvar (.there (.there (.there v))))).mpr
    intro s v
    cases s
    exact hParams' _ v
  have hSource' := hSource hBase hClass R.property hR hBW hParameters
  simp only [conclusion_m, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  refine ⟨R.val, R.property, hR, ?_⟩
  exact (witness_formula_l φ (ζ.pushBound R.val)
    (.fvar (.there (.there (.there (.there .here))))) (.fvar .here) (.bvar .here)
    (fun v => .fvar (.there (.there (.there (.there (.there v)))))) η (fun _ => rfl)).mpr hSource'

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ φ)

#print axioms witness_formula_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffSkolemGraph
