import BMSConstructibleBridge.PowerlessRelativeClassEnumerationClosure
import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionIndexEnumeration
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramEvaluationGraph

/-! # 原有限参数族的实际可数 Class 常量种子

从内部 ω 的恒等图起，添入基底及外部有限原公式参数，得到实际 ω 满射。
同一个种子包含于任何已覆盖原参数及 ω 的实际 Class 母界。
上下文归纳只遍历原公式的外部有限参数，不假设模型内部 ω 外部标准。
调用时应先取原参数族、后取层界 W 和见证选择图；不可把 W 自身添入
要求包含于 W 的种子，也不要求选择图充当可数常量。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassParameterSeed

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩" => structure_l hℳ B hBase

theorem exists_l {ω : type_l hℳ B} (hω : omega_l (ℳ := 𝒩) ω)
    (b : type_l hℳ B) {Δ : SortContext ℒ} (η : Env 𝒩 [] Δ) :
    ∃ C G : type_l hℳ B, map_l (ℳ := 𝒩) G ω C ∧
      (∀ x : type_l hℳ B, mem_l hℳ x.val C.val →
        ∃ i : type_l hℳ B, mem_l hℳ i.val ω.val ∧ value_l (ℳ := 𝒩) G i x) ∧
      (∀ x : type_l hℳ B, mem_l hℳ x.val ω.val → mem_l hℳ x.val C.val) ∧
      mem_l hℳ b.val C.val ∧
      (∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v).val C.val) ∧
      ∀ W : type_l hℳ B,
        (∀ x : type_l hℳ B, mem_l hℳ x.val ω.val → mem_l hℳ x.val W.val) →
        mem_l hℳ b.val W.val →
        (∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v).val W.val) →
        ∀ x : type_l hℳ B, mem_l hℳ x.val C.val → mem_l hℳ x.val W.val := by
  induction Δ with
  | nil =>
      obtain ⟨J, hJ, hRead⟩ :=
        PowerlessRelativeClassSatisfactionIndexEnumeration.identity_l (hBase := hBase) ω
      have hOnto : ∀ x : type_l hℳ B, mem_l hℳ x.val ω.val →
          ∃ i : type_l hℳ B, mem_l hℳ i.val ω.val ∧ value_l (ℳ := 𝒩) J i x :=
        fun x hx => ⟨x, hx, (hRead x x).mpr ⟨hx, rfl⟩⟩
      obtain ⟨C, G, hC, hG, hGOnto⟩ :=
        PowerlessRelativeClassEnumerationClosure.adjoin_l hω hJ hOnto b
      refine ⟨C, G, hG, hGOnto, fun x hx => (hC x).mpr (Or.inl hx),
        (hC b).mpr (Or.inr rfl), (fun _ v => nomatch v), ?_⟩
      intro W hωW hb _ x hx
      rcases (hC x).mp hx with hx | rfl
      · exact hωW x hx
      · exact hb
  | cons s Δ ih =>
      cases s
      let ξ : Env 𝒩 [] Δ :=
        { boundVal := η.boundVal, freeVal := fun v => η.freeVal (.there v) }
      obtain ⟨C, G, hG, hOnto, hωC, hb, hParams, hBound⟩ := ih ξ
      obtain ⟨D, F, hD, hF, hFOnto⟩ := PowerlessRelativeClassEnumerationClosure.adjoin_l
        hω hG hOnto (η.freeVal .here)
      refine ⟨D, F, hF, hFOnto, fun x hx => (hD x).mpr (Or.inl (hωC x hx)),
        (hD b).mpr (Or.inl hb), ?_, ?_⟩
      · intro s v
        cases s
        cases v with
        | here => exact (hD (η.freeVal .here)).mpr (Or.inr rfl)
        | there v => exact (hD (η.freeVal (.there v))).mpr (Or.inl (hParams _ v))
      · intro W hωW hbW hParamsW x hx
        rcases (hD x).mp hx with hx | hx
        · exact hBound W hωW hbW (fun s v => hParamsW s (.there v)) x hx
        · exact hx.symm ▸ hParamsW _ .here

def members_m {Γ Ε : SortContext ℒ} (Δ : SortContext ℒ)
    (C : Term ℒ Γ Ε .set) (τ : VariableSubstitution ℒ Δ Γ Ε) : Formula ℒ Γ Ε :=
  match Δ with
  | [] => .truth
  | .set :: Δ => .conj (SecondOrderObjectSyntax.member_m (τ .here) C)
      (members_m Δ C (fun v => τ (.there v)))

theorem members_formula_l {Γ Ε : SortContext ℒ} (Δ : SortContext ℒ) (η : Env 𝒱 Γ Ε)
    (C : Term ℒ Γ Ε .set) (τ : VariableSubstitution ℒ Δ Γ Ε) :
    (members_m Δ C τ).satisfies η ↔ ∀ s (v : Variable Δ s), mem_l hℳ ((τ v).eval η) (C.eval η) := by
  induction Δ with
  | nil =>
      constructor
      · intro _ _ v; nomatch v
      · intro _; trivial
  | cons s Δ ih =>
      cases s
      change (_ ∧ (members_m Δ C (fun v => τ (.there v))).satisfies η) ↔ _
      rw [ih]
      constructor
      · rintro ⟨h₀, h₁⟩ s v
        cases s
        cases v with
        | here => exact h₀
        | there v => exact h₁ _ v
      · intro h
        exact ⟨h _ .here, fun _ v => h _ (.there v)⟩

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)

def bound_m {Γ Δ : SortContext ℒ} (B ω C : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here)) <|
    .imp (ThirdOrderTheory.subset_m (up ω) (.bvar .here)) <|
      .imp (SecondOrderObjectSyntax.member_m (up B) (.bvar .here)) <|
        .imp (members_m Δ (.bvar .here) (fun v => .fvar v))
          (ThirdOrderTheory.subset_m (up C) (.bvar .here))

theorem bound_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (B ω C : Term ℒ Γ Δ .set) : (bound_m B ω C).satisfies η ↔
      ∀ W, PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) W →
        (∀ x, mem_l hℳ x (ω.eval η) → mem_l hℳ x W) → mem_l hℳ (B.eval η) W →
        (∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v) W) →
        ∀ x, mem_l hℳ x (C.eval η) → mem_l hℳ x W := by
  simp only [bound_m, Formula.satisfies, PowerlessRelativeHierarchySemantics.class_formula_l K,
    subset_formula_l, members_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval,
    up, Term.eval_weakenBound, Term.eval]
  rfl

def conclusion_m {Δ : SortContext ℒ} (B ω : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .existsE .set <| .existsE .set <|
    let C := .bvar (.there .here)
    let G := .bvar .here
    .conj (PowerlessRelativeHierarchySyntax.class_m (up₂ B) C) <|
      .conj (PowerlessRelativeHierarchySyntax.class_m (up₂ B) G) <|
        .conj (SecondOrderObjectSyntax.map_m G (up₂ ω) C) <|
          .conj (PowerlessRelativeClassEnumerationSectionDerives.onto_m G (up₂ ω) C) <|
            .conj (ThirdOrderTheory.subset_m (up₂ ω) C) <|
              .conj (SecondOrderObjectSyntax.member_m (up₂ B) C)
                (.conj (members_m Δ C (fun v => .fvar v)) (bound_m (up₂ B) (up₂ ω) C))

theorem conclusion_l (K : source_coding_l hℳ) {Δ : SortContext ℒ} (η : Env 𝒱 [] Δ)
    (B ω : Term ℒ [] Δ .set) : (conclusion_m B ω).satisfies η ↔
      ∃ C G, PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) C ∧
        PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) G ∧
        map_l (ℳ := 𝒱) G (ω.eval η) C ∧
        (∀ x, mem_l hℳ x C → ∃ i, mem_l hℳ i (ω.eval η) ∧ value_l (ℳ := 𝒱) G i x) ∧
        (∀ x, mem_l hℳ x (ω.eval η) → mem_l hℳ x C) ∧ mem_l hℳ (B.eval η) C ∧
        (∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v) C) ∧
        ∀ W, PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) W →
          (∀ x, mem_l hℳ x (ω.eval η) → mem_l hℳ x W) → mem_l hℳ (B.eval η) W →
          (∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v) W) →
          ∀ x, mem_l hℳ x C → mem_l hℳ x W := by
  simp only [conclusion_m, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.class_formula_l K, map_formula_l,
    PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l, subset_formula_l,
    members_formula_l, bound_formula_l K, SecondOrderObjectSyntax.member_m, Arguments.eval,
    up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  rfl

def schema_m {Δ : SortContext ℒ} (B ω : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B ω) <|
        .imp (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_m Δ B (fun v => .fvar v))
          (conclusion_m B ω)

def sentence_m {Δ : SortContext ℒ} (B ω : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B ω)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B ω : Term ℒ [] Δ .set) : (sentence_m B ω).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hBase hω hωC hParams
  have hBase' := (PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩 η B).mp hBase
  have hω' := (SecondOrderOmegaSyntax.omega_l h𝒩 η ω).mp hω
  have hωC' := (PowerlessRelativeHierarchySemantics.class_formula_l K η B ω).mp hωC
  have hParams' := (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_formula_l
    K Δ η B (fun v => .fvar v)).mp hParams
  let ξ : Env (structure_l h𝒩 (B.eval η) hBase') [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with
        | .set => ⟨η.freeVal v, hParams' _ v⟩ }
  let O : type_l h𝒩 (B.eval η) := ⟨ω.eval η, hωC'⟩
  let b : type_l h𝒩 (B.eval η) :=
    ⟨B.eval η, PowerlessRelativeClassCorrespondence.base_object_l h𝒩 hBase'⟩
  obtain ⟨C, G, hG, hOnto, hωC, hb, hMembers, hBound⟩ := exists_l
    ((PowerlessRelativeClassOmegaAbsolute.omega_l O).mpr hω') b ξ
  apply (conclusion_l K η B ω).mpr
  refine ⟨C.val, G.val, C.property, G.property,
    (PowerlessRelativeClassFunctionAbsolute.map_l G O C).mp hG,
    (PowerlessRelativeClassFunctionAbsolute.onto_l G O C).mp hOnto, ?_, hb, ?_, ?_⟩
  · intro x hx
    exact hωC ⟨x, PowerlessRelativeClassCorrespondence.transitive_l h𝒩 hBase' O.property hx⟩ hx
  · intro s v
    cases s
    exact hMembers _ v
  · intro W hW hωW hbW hParamsW x hx
    let D : type_l h𝒩 (B.eval η) := ⟨W, hW⟩
    exact hBound D (fun y hy => hωW y.val hy) hbW (fun s v => by
      cases s
      exact hParamsW _ v)
      ⟨x, PowerlessRelativeClassCorrespondence.transitive_l h𝒩 hBase' C.property hx⟩ hx

theorem derives_m {Δ : SortContext ℒ} (B ω : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m B ω)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 B ω)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassParameterSeed
