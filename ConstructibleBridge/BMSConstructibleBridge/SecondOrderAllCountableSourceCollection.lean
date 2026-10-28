import BMSConstructibleBridge.SecondOrderAllCountableClassCollectionDerives

/-! # 全类可数分支中实际类子模型的 Collection

原矩阵先逐量词类相对化，再重排两个输入与类参数。不假定环境
枚举属于类，也不抽取 Type 选择函数。源模式的全部参数只遍历
实际类子模型；最后将带分支条件的整条相对化闭句回传原 Z₂。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAllCountableSourceCollection

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open SecondOrderObjectSyntax (member_m)
open PowerlessBMSQuotientSubsetImageDerives
  (at_m at_formula_l parameters_l parameters_empty_l parameters_pushBound_l)
open SecondOrderCanonicalLevelDerives (guard_m guard_l guard_formula_l)
open SecondOrderClassWitnessCommonLevelDerives (all_countable_m all_countable_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.type_l PowerlessRelativeClassStructure.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private def reorder_m {Δ : SortContext ℒ} :
    VariableSubstitution ℒ (.set :: .set :: .set :: Δ) [] (.set :: .set :: .set :: Δ)
  | _, .here => .fvar (.there (.there .here))
  | _, .there .here => .fvar .here
  | _, .there (.there .here) => .fvar (.there .here)
  | _, .there (.there (.there v)) => .fvar (.there (.there (.there v)))

def relativized_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [] (.set :: .set :: .set :: Δ) :=
  (PowerlessRelativeClassRelativization.formula_m φ).substitute
    (show Substitution ℒ [] (.set :: .set :: .set :: Δ) [] (.set :: .set :: .set :: Δ) from
      .map (fun v => nomatch v) reorder_m)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "ClassModel" => PowerlessRelativeClassStructure.structure_l hℳ B hBase
local notation "CType" => PowerlessRelativeClassStructure.type_l hℳ B

def env_l {Δ : SortContext ℒ} (η : Env ClassModel [] Δ) : Env 𝒱 [] (.set :: Δ) :=
  (PowerlessRelativeClassRelativization.env_l η).pushFree B

theorem relativized_formula_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env ClassModel [] Δ) (x y : CType) :
    (relativized_m φ).satisfies (((env_l η).pushFree x.val).pushFree y.val) ↔
      φ.satisfies ((η.pushFree x).pushFree y) := by
  rw [relativized_m, Formula.satisfies_substitute]
  have hEnv : (((env_l η).pushFree x.val).pushFree y.val).pullback
      (show Substitution ℒ [] (.set :: .set :: .set :: Δ) [] (.set :: .set :: .set :: Δ) from
        .map (fun v => nomatch v) reorder_m) =
      (PowerlessRelativeClassRelativization.env_l ((η.pushFree x).pushFree y)).pushFree B := by
    apply Env.ext
    · intro s v; nomatch v
    · intro s v
      cases s
      rcases v with _ | _ | v
      all_goals first | rfl | cases v <;> rfl
  rw [hEnv]
  exact PowerlessRelativeClassRelativization.formula_l K φ ((η.pushFree x).pushFree y)

theorem collection_l (K : source_coding_l hℳ) {t₁ t₂ t₃ Pair Valid P₀ S : SecondOrderQuotient.type_l hℳ}
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
    (hGuard : guard_l B P₀)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega S)
    (hAll : ∀ a, SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) a →
      PowerlessRelativeOrdinalCutoff.countable_l B K.omega a)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env ClassModel [] Δ) (A : CType)
    (hSome : ∀ x : CType, mem_l hℳ x.val A.val → ∃ y : CType, φ.satisfies ((η.pushFree x).pushFree y)) :
    ∃ C : CType, ∀ x : CType, mem_l hℳ x.val A.val → ∃ y : CType,
      mem_l hℳ y.val C.val ∧ φ.satisfies ((η.pushFree x).pushFree y) := by
  let ξ := env_l η
  let b : Term ℒ [] (.set :: Δ) .set := .fvar .here
  have hSome' (x : SecondOrderQuotient.type_l hℳ) (hx : mem_l hℳ x A.val) : ∃ y,
      PowerlessRelativeClassCorrespondence.member_l hℳ B y ∧
        (relativized_m φ).satisfies ((ξ.pushFree x).pushFree y) := by
    let x' : CType := ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase A.property hx⟩
    obtain ⟨y, hy⟩ := hSome x' hx
    exact ⟨y.val, y.property, (relativized_formula_l K φ η x' y).mpr hy⟩
  obtain ⟨C, hC, hCover⟩ := SecondOrderAllCountableClassCollection.exists_l K hCoding
    (relativized_m φ) ξ b hGuard hS hAll A.val hSome'
  refine ⟨⟨C, hC⟩, fun x hx => ?_⟩
  obtain ⟨y, hyC, hyClass, hφ⟩ := hCover x.val hx
  let y' : CType := ⟨y, hyClass⟩
  exact ⟨y', hyC, (relativized_formula_l K φ η x y').mp hφ⟩

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)

def request_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (A : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (member_m (.bvar .here) (up A)) <|
    .existsE .set (at_m φ (.bvar (.there .here)) (.bvar .here))

def collected_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (A C : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (member_m (.bvar .here) (up A)) <|
    .existsE .set <| .conj (member_m (.bvar .here) (up₂ C))
      (at_m φ (.bvar (.there .here)) (.bvar .here))

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Formula ℒ [] Δ :=
  .forallE .set <| .imp (request_m φ (.bvar .here)) <|
    .existsE .set (collected_m φ (.bvar (.there .here)) (.bvar .here))

def source_sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ)

theorem schema_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 [] Δ) :
    (schema_m φ).satisfies η ↔ ∀ A,
      (∀ x, member_l 𝒩 x A → ∃ y, φ.satisfies ((η.pushFree x).pushFree y)) →
      ∃ C, ∀ x, member_l 𝒩 x A → ∃ y, member_l 𝒩 y C ∧ φ.satisfies ((η.pushFree x).pushFree y) := by
  simp only [schema_m, request_m, collected_m, Formula.satisfies, at_formula_l,
    parameters_pushBound_l, parameters_empty_l, member_m, Arguments.eval, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem source_models_l (K : source_coding_l hℳ) {t₁ t₂ t₃ Pair Valid P₀ S : SecondOrderQuotient.type_l hℳ}
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
    (hGuard : guard_l B P₀)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega S)
    (hAll : ∀ a, SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) a →
      PowerlessRelativeOrdinalCutoff.countable_l B K.omega a)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : (source_sentence_m φ).TrueIn ClassModel := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  exact (schema_formula_l φ η).mpr (fun A hSome => collection_l K hCoding hGuard hS hAll φ η A hSome)

/-- 分支守卫不藏在 Lean 前提中，原源闭句的全部参数仍在类内量化。 -/
def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Sentence ℒ :=
  .forallE .set <| .forallE .set <| .forallE .set <| .forallE .set <|
    let B : Term ℒ [.set, .set, .set, .set] [] .set := .bvar (.there (.there (.there .here)))
    let ω := .bvar (.there (.there .here))
    let P₀ := .bvar (.there .here)
    let S := .bvar .here
    .imp (guard_m B P₀) <| .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessFiniteSequencesSyntax.spec_m ω ω S) <| .imp (all_countable_m B ω)
        (PowerlessWeakSetInduction.at_m (PowerlessRelativeClassRelativization.formula_m (source_sentence_m φ)) B)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) : (sentence_m φ).TrueIn 𝒱 := by
  obtain ⟨K₀⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  simp only [sentence_m, Formula.TrueIn, Formula.satisfies, guard_formula_l, omega_formula_l,
    PowerlessFiniteSequencesSyntax.spec_formula_l, all_countable_formula_l K₀,
    PowerlessWeakSetInduction.at_formula_l, parameters_pushBound_l, parameters_empty_l, Term.eval]
  intro B ω P₀ S hGuard hω hS hAll
  obtain ⟨K, _, _, _, _, _, _, hωEq, _, hCoding⟩ := SecondOrderComparisonCoding.exists_l hω
  rw [hωEq] at hS hAll
  have hBase x hx y hy := hGuard.2.1 x y hx hy
  exact (PowerlessRelativeClassRelativization.sentence_l (hBase := hBase) K (source_sentence_m φ)).mpr
    (source_models_l K hCoding hGuard hS hAll φ)

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ φ)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAllCountableSourceCollection
