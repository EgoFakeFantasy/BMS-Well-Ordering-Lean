import BMSConstructibleBridge.PowerlessRelativeClassParameterSeed

/-! # 原参数种子在扩大的证明上下文中的实际构造

原参数 Δ 与装配上下文 Ε 分开。仅用指定项 τ 解释原 Δ，复用实际
Class 种子构造；新环境中的排序图、见证图不自动进入种子。
同一 C、实际枚举 G、原参数成员性及共同母界规格同时保留。
背景为原 Z₂，公开终点为对象存在句的原 Derives，不抽取 Type 选择。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassParameterSeedLift

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev up {Γ Ε : SortContext ℒ} (t : Term ℒ Γ Ε .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Ε : SortContext ℒ} (t : Term ℒ Γ Ε .set) := up (up t)

def bound_m {Γ Ε : SortContext ℒ} (Δ : SortContext ℒ)
    (B ω C : Term ℒ Γ Ε .set) (τ : VariableSubstitution ℒ Δ Γ Ε) : Formula ℒ Γ Ε :=
  .forallE .set <| .imp (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here)) <|
    .imp (ThirdOrderTheory.subset_m (up ω) (.bvar .here)) <|
      .imp (SecondOrderObjectSyntax.member_m (up B) (.bvar .here)) <|
        .imp (PowerlessRelativeClassParameterSeed.members_m Δ (.bvar .here) (fun v => up (τ v)))
          (ThirdOrderTheory.subset_m (up C) (.bvar .here))

def packet_m {Γ Ε : SortContext ℒ} (Δ : SortContext ℒ)
    (B ω C G : Term ℒ Γ Ε .set) (τ : VariableSubstitution ℒ Δ Γ Ε) : Formula ℒ Γ Ε :=
  .conj (PowerlessRelativeHierarchySyntax.class_m B C) <|
    .conj (PowerlessRelativeHierarchySyntax.class_m B G) <|
      .conj (SecondOrderObjectSyntax.map_m G ω C) <|
        .conj (PowerlessRelativeClassEnumerationSectionDerives.onto_m G ω C) <|
          .conj (ThirdOrderTheory.subset_m ω C) <|
            .conj (SecondOrderObjectSyntax.member_m B C) <|
              .conj (PowerlessRelativeClassParameterSeed.members_m Δ C τ) (bound_m Δ B ω C τ)

def conclusion_m {Ε : SortContext ℒ} (Δ : SortContext ℒ)
    (B ω : Term ℒ [] Ε .set) (τ : VariableSubstitution ℒ Δ [] Ε) : Formula ℒ [] Ε :=
  .existsE .set <| .existsE .set <| packet_m Δ (up₂ B) (up₂ ω)
    (.bvar (.there .here)) (.bvar .here) (fun v => up₂ (τ v))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem bound_formula_l (K : source_coding_l hℳ) {Γ Ε : SortContext ℒ}
    (Δ : SortContext ℒ) (η : Env 𝒱 Γ Ε) (B ω C : Term ℒ Γ Ε .set)
    (τ : VariableSubstitution ℒ Δ Γ Ε) : (bound_m Δ B ω C τ).satisfies η ↔
      ∀ W, PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) W →
        (∀ x, mem_l hℳ x (ω.eval η) → mem_l hℳ x W) → mem_l hℳ (B.eval η) W →
        (∀ s (v : Variable Δ s), mem_l hℳ ((τ v).eval η) W) →
        ∀ x, mem_l hℳ x (C.eval η) → mem_l hℳ x W := by
  simp only [bound_m, Formula.satisfies, PowerlessRelativeHierarchySemantics.class_formula_l K,
    subset_formula_l, PowerlessRelativeClassParameterSeed.members_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem packet_formula_l (K : source_coding_l hℳ) {Γ Ε : SortContext ℒ}
    (Δ : SortContext ℒ) (η : Env 𝒱 Γ Ε) (B ω C G : Term ℒ Γ Ε .set)
    (τ : VariableSubstitution ℒ Δ Γ Ε) : (packet_m Δ B ω C G τ).satisfies η ↔
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η) ∧
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (G.eval η) ∧
      map_l (ℳ := 𝒱) (G.eval η) (ω.eval η) (C.eval η) ∧
      (∀ x, mem_l hℳ x (C.eval η) →
        ∃ i, mem_l hℳ i (ω.eval η) ∧ value_l (ℳ := 𝒱) (G.eval η) i x) ∧
      (∀ x, mem_l hℳ x (ω.eval η) → mem_l hℳ x (C.eval η)) ∧
      mem_l hℳ (B.eval η) (C.eval η) ∧
      (∀ s (v : Variable Δ s), mem_l hℳ ((τ v).eval η) (C.eval η)) ∧
      ∀ W, PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) W →
        (∀ x, mem_l hℳ x (ω.eval η) → mem_l hℳ x W) → mem_l hℳ (B.eval η) W →
        (∀ s (v : Variable Δ s), mem_l hℳ ((τ v).eval η) W) →
        ∀ x, mem_l hℳ x (C.eval η) → mem_l hℳ x W := by
  simp only [packet_m, Formula.satisfies, PowerlessRelativeHierarchySemantics.class_formula_l K,
    map_formula_l, PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l,
    subset_formula_l, PowerlessRelativeClassParameterSeed.members_formula_l, bound_formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  rfl

theorem exists_l (K : source_coding_l hℳ) {Ε : SortContext ℒ}
    (Δ : SortContext ℒ) (η : Env 𝒱 [] Ε) (B ω : Term ℒ [] Ε .set)
    (τ : VariableSubstitution ℒ Δ [] Ε)
    (hB : ∀ x, mem_l hℳ x (B.eval η) → ∀ y, mem_l hℳ y x → mem_l hℳ y (B.eval η))
    (hω : SecondOrderOmega.omega_l hℳ (ω.eval η))
    (hωC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (ω.eval η))
    (hParams : ∀ s (v : Variable Δ s),
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) ((τ v).eval η)) :
    (conclusion_m Δ B ω τ).satisfies η := by
  let ξ : Env (structure_l hℳ (B.eval η) hB) [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with
        | .set => ⟨(τ v).eval η, hParams _ v⟩ }
  let O : type_l hℳ (B.eval η) := ⟨ω.eval η, hωC⟩
  let b : type_l hℳ (B.eval η) :=
    ⟨B.eval η, PowerlessRelativeClassCorrespondence.base_object_l hℳ hB⟩
  obtain ⟨C, G, hG, hOnto, hωC', hb, hMembers, hBound⟩ :=
    PowerlessRelativeClassParameterSeed.exists_l
      ((PowerlessRelativeClassOmegaAbsolute.omega_l O).mpr hω) b ξ
  simp only [conclusion_m, Formula.satisfies, packet_formula_l K,
    up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  refine ⟨C.val, G.val, C.property, G.property,
    (PowerlessRelativeClassFunctionAbsolute.map_l G O C).mp hG,
    (PowerlessRelativeClassFunctionAbsolute.onto_l G O C).mp hOnto, ?_, hb, ?_, ?_⟩
  · intro x hx
    exact hωC' ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hB O.property hx⟩ hx
  · intro s v
    cases s
    exact hMembers _ v
  · intro W hW hωW hbW hParamsW x hx
    let D : type_l hℳ (B.eval η) := ⟨W, hW⟩
    exact hBound D (fun y hy => hωW y.val hy) hbW (fun s v => by
      cases s
      exact hParamsW _ v)
      ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hB C.property hx⟩ hx

def schema_m {Ε : SortContext ℒ} (Δ : SortContext ℒ)
    (B ω : Term ℒ [] Ε .set) (τ : VariableSubstitution ℒ Δ [] Ε) : Formula ℒ [] Ε :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B ω) <|
        .imp (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_m Δ B τ)
          (conclusion_m Δ B ω τ)

def sentence_m {Ε : SortContext ℒ} (Δ : SortContext ℒ)
    (B ω : Term ℒ [] Ε .set) (τ : VariableSubstitution ℒ Δ [] Ε) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m Δ B ω τ)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Ε : SortContext ℒ}
    (Δ : SortContext ℒ) (B ω : Term ℒ [] Ε .set) (τ : VariableSubstitution ℒ Δ [] Ε) :
    (sentence_m Δ B ω τ).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeFiniteProgramEvaluationGraph.parameters_formula_l K]
  intro η hB hω hωC hParams
  exact exists_l K Δ η B ω τ hB hω hωC hParams

theorem derives_m {Ε : SortContext ℒ} (Δ : SortContext ℒ)
    (B ω : Term ℒ [] Ε .set) (τ : VariableSubstitution ℒ Δ [] Ε) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m Δ B ω τ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 Δ B ω τ)

#print axioms bound_formula_l
#print axioms packet_formula_l
#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassParameterSeedLift
