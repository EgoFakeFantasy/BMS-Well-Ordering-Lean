import BMSConstructibleBridge.PowerlessRelativeCutoffWitnessStageDerives
import BMSConstructibleBridge.PowerlessRelativizationDelta

/-! # 任意原收集矩阵的实际阶段图及精确可数值域

纯隶属 ℒ、原 Z₂。任意原矩阵仅对同一 W 限制量词，再代入有界
阶段图规则；不把原矩阵误改成 Δ₀，也不要求 W 属于自身。
实际 F/G/C 同时产生，C 是 G 的精确 Class 可数值域。所给原对象
推导尚不包括 C 的序数并集可数性或 δ<Ω，因而不是完整 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffCollectionStages

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Ε : SortContext ℒ} (t : Term ℒ Γ Ε .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₃ {Γ Ε : SortContext ℒ} (t : Term ℒ Γ Ε .set) := up (up (up t))

/-- 原 y/x 槽保持顺序，第三自由槽为外部域 W。 -/
def matrix_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [] (.set :: .set :: .set :: Δ) :=
  PowerlessRelativeParameters.instance_m φ (.fvar (.there (.there .here)))
    (fun v => match v with
      | .here => .fvar .here
      | .there .here => .fvar (.there .here)
      | .there (.there v) => .fvar (.there (.there (.there v))))

theorem matrix_delta_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula.IsDelta0 membershipLevyBound (matrix_m φ) :=
  PowerlessRelativizationDelta.instance_l φ _ _

theorem matrix_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒩 [] Δ) (W x y : carrier_l 𝒩) :
    (matrix_m φ).satisfies (((η.pushFree W).pushFree x).pushFree y) ↔
      (PowerlessRelativization.formula_m φ).satisfies (((η.pushFree x).pushFree y).pushFree W) := by
  rw [matrix_m, PowerlessRelativeParameters.instance_m, Formula.satisfies_substitute]
  apply Iff.of_eq
  apply congrArg (fun ξ => (PowerlessRelativization.formula_m φ).satisfies ξ)
  apply Env.ext
  · intro s v; nomatch v
  · intro s v; cases s
    cases v with
    | here => rfl
    | there v => cases v with
      | here => rfl
      | there v => cases v with
        | here => rfl
        | there v => rfl

/-- 任意原公式的实际成员域真值，不需要传递性或有界性假设。 -/
theorem member_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {W : carrier_l 𝒩} {hW : ∃ x, member_l 𝒩 x W} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (PowerlessMemberStructure.structure_l W hW) [] Δ)
    (x y : PowerlessMemberStructure.type_l (ℳ := 𝒩) W) :
    (matrix_m φ).satisfies
      ((((PowerlessRelativization.env_l η).pushFree W).pushFree x.val).pushFree y.val) ↔
        φ.satisfies ((η.pushFree x).pushFree y) := by
  refine PowerlessRelativeParameters.instance_l φ _ _ _ ((η.pushFree x).pushFree y) rfl ?_
  intro v
  cases v with
  | here => rfl
  | there v => cases v <;> rfl

def range_m {Γ Ε : SortContext ℒ} (G C : Term ℒ Γ Ε .set) : Formula ℒ Γ Ε :=
  .forallE .set <| .iff (SecondOrderObjectSyntax.member_m (.bvar .here) (up C)) <|
    .existsE .set (SecondOrderObjectSyntax.value_m (up (up G)) (.bvar .here) (.bvar (.there .here)))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ

theorem range_formula_l {Γ Ε : SortContext ℒ} (η : Env 𝒱 Γ Ε) (G C : Term ℒ Γ Ε .set) :
    (range_m G C).satisfies η ↔ ∀ a, mem_l hℳ a (C.eval η) ↔
      ∃ x, value_l (ℳ := 𝒱) (G.eval η) x a := by
  simp only [range_m, Formula.satisfies, SecondOrderObjectSyntax.value_l hℳ,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

private def domain_m {Γ Ε Δ : SortContext ℒ} (W : Term ℒ Γ Ε .set)
    (τ : Variable Δ .set → Term ℒ Γ Ε .set) : Variable (.set :: Δ) .set → Term ℒ Γ Ε .set
  | .here => W
  | .there v => τ v

def conclusion_m {Γ Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B ω Ω W : Term ℒ Γ Ε .set) (τ : Variable Δ .set → Term ℒ Γ Ε .set) : Formula ℒ Γ Ε :=
  .existsE .set <| .existsE .set <| .existsE .set <|
    let F := .bvar (.there (.there .here))
    let G := .bvar (.there .here)
    let C := .bvar .here
    .conj (PowerlessRelativeHierarchySyntax.class_m (up₃ B) F) <|
      .conj (PowerlessRelativeHierarchySyntax.class_m (up₃ B) G) <|
        .conj (PowerlessRelativeHierarchySyntax.class_m (up₃ B) C) <|
          .conj (PowerlessRelativeHierarchySyntax.history_m (up₃ B) (up₃ Ω) F (up₃ W)) <|
            .conj (SecondOrderObjectSyntax.map_m G (up₃ ω) (up₃ Ω)) <|
              .conj (PowerlessRelativeOrdinalCutoff.countable_m (up₃ B) (up₃ ω) C) <|
                .conj (range_m G C)
                  (PowerlessRelativeCutoffWitnessStageDerives.reading_m (matrix_m φ)
                    (up₃ ω) (up₃ Ω) F G (up₃ W) (domain_m (up₃ W) (fun v => up₃ (τ v))))

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
            .imp (PowerlessRelativeCutoffWitnessStageDerives.total_m (matrix_m φ) ω W (domain_m W τ))
              (conclusion_m φ B ω Ω W τ)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    (sentence_m φ).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeOrdinalCutoff.first_formula_l K,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeFiniteProgramEvaluationGraph.parameters_formula_l K,
    PowerlessRelativeCutoffWitnessStageDerives.total_formula_l]
  intro η hBase hω hΩ hW hParams hSome
  let τ : Variable Δ .set → Term ℒ [] (.set :: .set :: .set :: .set :: Δ) .set :=
    fun v => .fvar (.there (.there (.there (.there v))))
  let σ : Variable (.set :: Δ) .set → Term ℒ [] (.set :: .set :: .set :: .set :: Δ) .set :=
    domain_m (.fvar .here) τ
  obtain ⟨F, G, hF, hG, hRead⟩ := PowerlessRelativeCutoffWitnessStageGraph.exists_l K
    hBase hω hΩ hW (matrix_delta_l φ) (PowerlessRelativeHistoryWitnessStage.env_l η σ)
    (fun s v => by
      cases s
      cases v with
      | here => exact PowerlessRelativeLevelClosure.class_l h𝒩 hBase hW
      | there v => exact hParams .set v) hSome
  obtain ⟨C, hCount, hRange⟩ := PowerlessRelativeCutoffWitnessStageGraph.range_l K hBase hω G hG
  simp only [conclusion_m, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeHierarchySemantics.history_formula_l K, SecondOrderObjectSyntax.map_l h𝒩,
    PowerlessRelativeOrdinalCutoff.countable_formula_l K, range_formula_l,
    PowerlessRelativeCutoffWitnessStageDerives.reading_formula_l,
    up₃, up, Term.eval_weakenBound, Term.eval]
  refine ⟨F.val, G.val, C.val, F.property, G.property, C.property, hF, hG, hCount, hRange, ?_⟩
  have hEnv : PowerlessRelativeHistoryWitnessStage.env_l
      (((η.pushBound F.val).pushBound G.val).pushBound C.val)
      (domain_m (up₃ (.fvar .here)) (fun v => up₃ (τ v))) =
        PowerlessRelativeHistoryWitnessStage.env_l η σ := by
    apply Env.ext
    · intro s v; nomatch v
    · intro s v; cases s; cases v <;> rfl
  rw [hEnv]
  intro x a
  constructor
  · intro hValue
    obtain ⟨hx, ha, hRank⟩ := (hRead x a).mp hValue
    exact ⟨hx, ha, (PowerlessRelativeHistoryWitnessStage.rank_iff_l _ _ hΩ.1 hF ha).mpr hRank⟩
  · rintro ⟨hx, ha, hRank⟩
    exact (hRead x a).mpr ⟨hx, ha,
      (PowerlessRelativeHistoryWitnessStage.rank_iff_l _ _ hΩ.1 hF ha).mp hRank⟩

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 φ)

#print axioms matrix_delta_l
#print axioms member_formula_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffCollectionStages
