import BMSConstructibleBridge.PowerlessRelativeCutoffWitnessStageGraph
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramEvaluationGraph

/-! # 实际 Class 最小阶段图的原 Z₂ 对象推导

纯隶属闭句只保留传递基底、实际 ω、首截断、层值、原 Class 参数及
逐输入的真正见证存在性。前史与阶段函数共同在对象存在块中产生，
并保留精确最小阶段读数；不预供图、统一族或共同序数界。
这个对象规则不是完整 Collection，更不是最终固定高度 BMS 良序句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffWitnessStageDerives

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Ε : SortContext ℒ} (t : Term ℒ Γ Ε .set) :=
  t.weakenBound SetTheory.SetSort.set

private def matrix_m {Γ Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (x y : Term ℒ Γ Ε .set) (τ : Variable Δ .set → Term ℒ Γ Ε .set) : Formula ℒ Γ Ε :=
  φ.substitute (show Substitution ℒ [] (.set :: .set :: Δ) Γ Ε from
    .map (fun v => nomatch v) (fun {s} v => match s with
      | .set => match v with | .here => y | .there .here => x | .there (.there v) => τ v))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ

private theorem matrix_formula_l {Γ Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 Γ Ε) (x y : Term ℒ Γ Ε .set) (τ : Variable Δ .set → Term ℒ Γ Ε .set) :
    (matrix_m φ x y τ).satisfies η ↔ φ.satisfies
      (((PowerlessRelativeHistoryWitnessStage.env_l η τ).pushFree (x.eval η)).pushFree (y.eval η)) := by
  rw [matrix_m, Formula.satisfies_substitute]
  apply Iff.of_eq
  apply congrArg (fun ρ => φ.satisfies ρ)
  apply Env.ext
  · intro s v; nomatch v
  · intro s v; cases s; cases v with
    | here => rfl
    | there v => cases v <;> rfl

private theorem env_up_l {Γ Ε Δ : SortContext ℒ} (η : Env 𝒱 Γ Ε)
    (τ : Variable Δ .set → Term ℒ Γ Ε .set) (x : Raw) :
    PowerlessRelativeHistoryWitnessStage.env_l (η.pushBound x) (fun v => up (τ v)) =
      PowerlessRelativeHistoryWitnessStage.env_l η τ := by
  apply Env.ext
  · intro s v; nomatch v
  · intro s v; cases s; exact Term.eval_weakenBound _ _ _

def total_m {Γ Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω W : Term ℒ Γ Ε .set) (τ : Variable Δ .set → Term ℒ Γ Ε .set) : Formula ℒ Γ Ε :=
  .forallE .set <| .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (up ω)) <|
    .existsE .set <| .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up (up W)))
      (matrix_m φ (.bvar (.there .here)) (.bvar .here) (fun v => up (up (τ v))))

theorem total_formula_l {Γ Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 Γ Ε) (ω W : Term ℒ Γ Ε .set) (τ : Variable Δ .set → Term ℒ Γ Ε .set) :
    (total_m φ ω W τ).satisfies η ↔ ∀ x, mem_l hℳ x (ω.eval η) →
      ∃ y, mem_l hℳ y (W.eval η) ∧ φ.satisfies
        (((PowerlessRelativeHistoryWitnessStage.env_l η τ).pushFree x).pushFree y) := by
  simp only [total_m, Formula.satisfies, matrix_formula_l, env_up_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def reading_m {Γ Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω Ω F G W : Term ℒ Γ Ε .set) (τ : Variable Δ .set → Term ℒ Γ Ε .set) : Formula ℒ Γ Ε :=
  .forallE .set <| .forallE .set <|
    let x := .bvar (.there .here)
    let a := .bvar .here
    .iff (SecondOrderObjectSyntax.value_m (up (up G)) x a) <|
      .conj (SecondOrderObjectSyntax.member_m x (up (up ω))) <|
        .conj (SecondOrderObjectSyntax.member_m a (up (up Ω)))
          (PowerlessRelativeCutoffWitnessStageGraph.graph_m φ (up (up F)) (up (up W)) x a
            (fun v => up (up (τ v))))

theorem reading_formula_l {Γ Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 Γ Ε) (ω Ω F G W : Term ℒ Γ Ε .set)
    (τ : Variable Δ .set → Term ℒ Γ Ε .set) :
    (reading_m φ ω Ω F G W τ).satisfies η ↔ ∀ x a,
      value_l (ℳ := 𝒱) (G.eval η) x a ↔ mem_l hℳ x (ω.eval η) ∧ mem_l hℳ a (Ω.eval η) ∧
        PowerlessRelativeHistoryWitnessStage.rank_l φ
          ((PowerlessRelativeHistoryWitnessStage.env_l η τ).pushFree x) (F.eval η) (W.eval η) a := by
  simp only [reading_m, Formula.satisfies, SecondOrderObjectSyntax.value_l hℳ,
    PowerlessRelativeCutoffWitnessStageGraph.graph_formula_l, env_up_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def conclusion_m {Γ Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B ω Ω W : Term ℒ Γ Ε .set) (τ : Variable Δ .set → Term ℒ Γ Ε .set) : Formula ℒ Γ Ε :=
  .existsE .set <| .existsE .set <|
    let F := .bvar (.there .here)
    let G := .bvar .here
    .conj (PowerlessRelativeHierarchySyntax.class_m (up (up B)) F) <|
      .conj (PowerlessRelativeHierarchySyntax.class_m (up (up B)) G) <|
        .conj (PowerlessRelativeHierarchySyntax.history_m (up (up B)) (up (up Ω)) F (up (up W))) <|
          .conj (SecondOrderObjectSyntax.map_m G (up (up ω)) (up (up Ω)))
            (reading_m φ (up (up ω)) (up (up Ω)) F G (up (up W)) (fun v => up (up (τ v))))

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [] (.set :: .set :: .set :: .set :: Δ) :=
  let W : Term ℒ [] (.set :: .set :: .set :: .set :: Δ) .set := .fvar .here
  let Ω := .fvar (.there .here)
  let ω := .fvar (.there (.there .here))
  let B := .fvar (.there (.there (.there .here)))
  let τ : Variable Δ .set → Term ℒ [] (.set :: .set :: .set :: .set :: Δ) .set :=
    fun v => .fvar (.there (.there (.there (.there v))))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeOrdinalCutoff.first_m B ω Ω) <|
        .imp (PowerlessRelativeHierarchySyntax.level_m B Ω W) <|
          .imp (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_m Δ B τ) <|
            .imp (total_m φ ω W τ) (conclusion_m φ B ω Ω W τ)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) :
    (sentence_m φ).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeOrdinalCutoff.first_formula_l K,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeFiniteProgramEvaluationGraph.parameters_formula_l K, total_formula_l]
  intro η hBase hω hΩ hW hParams hSome
  let τ : Variable Δ .set → Term ℒ [] (.set :: .set :: .set :: .set :: Δ) .set :=
    fun v => .fvar (.there (.there (.there (.there v))))
  obtain ⟨F, G, hF, hG, hRead⟩ := PowerlessRelativeCutoffWitnessStageGraph.exists_l K
    hBase hω hΩ hW hφ (PowerlessRelativeHistoryWitnessStage.env_l η τ)
    (fun s v => by cases s; exact hParams .set v) hSome
  simp only [conclusion_m, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeHierarchySemantics.history_formula_l K, SecondOrderObjectSyntax.map_l h𝒩,
    reading_formula_l, env_up_l, up, Term.eval_weakenBound, Term.eval]
  refine ⟨F.val, G.val, F.property, G.property, hF, hG, fun x a => ?_⟩
  constructor
  · intro hValue
    obtain ⟨hx, ha, hRank⟩ := (hRead x a).mp hValue
    exact ⟨hx, ha, (PowerlessRelativeHistoryWitnessStage.rank_iff_l φ _ hΩ.1 hF ha).mpr hRank⟩
  · rintro ⟨hx, ha, hRank⟩
    exact (hRead x a).mpr ⟨hx, ha,
      (PowerlessRelativeHistoryWitnessStage.rank_iff_l φ _ hΩ.1 hF ha).mp hRank⟩

theorem derives_m {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 hφ)

#print axioms total_formula_l
#print axioms reading_formula_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffWitnessStageDerives
