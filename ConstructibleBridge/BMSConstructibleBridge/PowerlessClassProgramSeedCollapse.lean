import BMSConstructibleBridge.PowerlessClassProgramElementarity
import BMSConstructibleBridge.PowerlessClassProgramIsomorphism
import BMSConstructibleBridge.PowerlessWholeCollapseSeed

/-! # 同一编码包上的有限元素性、实际坍缩与种子固定

原 Z₂、纯隶属 ℒ。原有限公式族决定同一算子及全程序域；Class 程序
枚举 U 和原数码图 A 的同一坍缩 T/H，与该域的有限元素性共同装配。
传递种子 D 及其全部成员均由原常量种子 C 覆盖，故坍缩固定 D。
不存在预供的元素性、同构、函数性、请求闭包或 T/H 的 Class 守卫。
原构造规格仍显式保留；凝聚、T 的 Class 性及最终 BMS 良序尚未完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassProgramSeedCollapse

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderCanonicalLevelDerives (guard_m guard_l guard_formula_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_pushBound_l parameters_empty_l)
open PowerlessRelativeFiniteProgramNumberEvaluation (number_m)
open PowerlessRelativeFiniteProgramEnumeratedCollapse (reading_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (v : Term ℒ Γ Δ .set) :=
  v.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (v : Term ℒ Γ Δ .set) := up (up v)
private abbrev up₃ {Γ Δ : SortContext ℒ} (v : Term ℒ Γ Δ .set) := up (up₂ v)
private abbrev up₅ {Γ Δ : SortContext ℒ} (v : Term ℒ Γ Δ .set) := up₂ (up₃ v)

private def number_body_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a D : Term ℒ [] Δ .set) : Formula ℒ [] (.set :: Δ) :=
  let ψ := number_m φ (up B) (up C) (up ω) (up Q) (up e) (up t₀) (up t₁) (up t₂)
    (up a) (.bvar .here)
  let O := Term.weakenFree (σ := ℒ) SetTheory.SetSort.set ω
  let d := Term.weakenFree (σ := ℒ) SetTheory.SetSort.set D
  .existsE .set <| .existsE .set <| .existsE .set <|
    let A : Term ℒ (.set :: .set :: .set :: []) (.set :: Δ) .set := .bvar (.there (.there .here))
    let T := .bvar (.there .here)
    let H := .bvar .here
    .conj (PowerlessDefinableMembershipDiagram.spec_m ψ (up₃ O) A) <|
      .conj (PowerlessDefinableMembershipCollapse.domain_m A (up₃ O)) <|
        .conj (SecondOrderCollapseSyntax.formula_m A (up₃ O) T H) <|
          .conj (PowerlessDefinableWholeCollapse.isomorphism_m ψ (up₃ O) T H)
            (PowerlessWholeCollapseSeed.conclusion_m ψ (up₃ O) (up₃ d) T H)

/-- 有限元素性与实际坍缩使用同一原请求族和同一编码包。 -/
def conclusion_m {Γ Δ : SortContext ℒ} (Φ : PowerlessClassFiniteElementarity.family_m Γ)
    (ν : VariableSubstitution ℒ Γ [] Δ)
    (ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a P s t D : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  let Ψ := PowerlessClassProgramFiniteRequests.family_m (PowerlessClassFiniteElementarity.requests_m Φ) B ν
  let φ := PowerlessClassProgramHull.operator_m Ψ ω e r₁ r₂ r₃ Pair Valid B P₀ s t
  .conj (PowerlessClassProgramElementarity.conclusion_m Φ ν
    ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a P s t) <|
      .existsE .set <| .conj (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here)) <|
        .conj (SecondOrderObjectSyntax.map_m (.bvar .here) (up ω) (up P)) <|
          .conj (PowerlessRelativeClassEnumerationSectionDerives.onto_m (.bvar .here) (up ω) (up P))
            (PowerlessSourceRebinding.formula_m (number_body_m φ B C ω Q e t₀ t₁ t₂ a D))

private def mode_m {Γ Δ : SortContext ℒ} (Φ : PowerlessClassFiniteElementarity.family_m Γ)
    (ν : VariableSubstitution ℒ Γ [] Δ)
    (ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a G S P s t D : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (guard_m B P₀) <| .imp (PowerlessRelativeHierarchySyntax.class_m B C) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B ω) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B Q) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B G) <|
          .imp (PowerlessRelativeHierarchySyntax.class_m B t₀) <|
            .imp (PowerlessRelativeHierarchySyntax.class_m B t₁) <|
              .imp (PowerlessRelativeHierarchySyntax.class_m B t₂) <|
                .imp (SecondOrderObjectSyntax.map_m G ω C) <|
                  .imp (PowerlessRelativeClassEnumerationSectionDerives.onto_m G ω C) <|
                    .imp (PowerlessDefinableFiniteTraceDerives.zero_m e) <|
                      .imp (PowerlessRelativeFiniteProgramStep.record_m e e e a) <|
                        .imp (PowerlessRelativeFiniteProgramInstruction.tags_m t₀ t₁ t₂) <|
                          .imp (PowerlessRelativeFiniteProgramAlphabet.alphabet_m C ω t₀ t₁ t₂ Q) <|
                            .imp (PowerlessRelativeFiniteProgramDomain.domain_m B ω Q S P) <|
                              .imp (SecondOrderObjectSyntax.member_m B C) <|
                                .imp (SecondOrderObjectSyntax.member_m s C) <|
                                  .imp (SecondOrderObjectSyntax.member_m t C) <| .imp (.neg (.equal s t)) <|
                                    .imp (PowerlessRelativeHierarchyDerives.transitive_m D) <|
                                      .imp (ThirdOrderTheory.subset_m D C) <|
                                        .imp (SecondOrderObjectSyntax.member_m D C)
                                          (conclusion_m Φ ν ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a P s t D)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "ε" => SecondOrderQuotient.mem_l hℳ

private theorem opening_l {Δ : SortContext ℒ} (η : Env 𝒱 [] Δ) :
    PowerlessSourceOpening.env_l η = η := by
  apply Env.ext
  · intro _ v; nomatch v
  · intro _ _; rfl

private theorem env_id_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ) :
    PowerlessDefinableMembershipDiagram.env_l η (fun v => .fvar v) =
      PowerlessBMSQuotientSubsetImageDerives.parameters_l η := by
  apply Env.ext
  · intro _ v; nomatch v
  · intro s v; cases s; rfl

private theorem number_body_formula_l {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B C ω Q e t₀ t₁ t₂ a D : Term ℒ [] Δ .set) (U : Raw) :
    let ψ := number_m φ (up B) (up C) (up ω) (up Q) (up e) (up t₀) (up t₁) (up t₂)
      (up a) (.bvar .here)
    (number_body_m φ B C ω Q e t₀ t₁ t₂ a D).satisfies (η.pushFree U) ↔
      ∃ A T H : Raw, PowerlessDefinableMembershipDiagram.spec_l ψ (η.pushFree U) (ω.eval η) A ∧
        PowerlessDefinableMembershipCollapse.domain_l (𝒩 := 𝒱) A (ω.eval η) ∧
          SecondOrderCollapseFunction.spec_l hℳ A (ω.eval η) T H ∧
            PowerlessDefinableWholeCollapse.isomorphism_l ψ (η.pushFree U) (ω.eval η) T H ∧
              (∀ x, ε x (D.eval η) → ε x T ∧
                PowerlessDefinableMembershipIsomorphism.project_l ψ (η.pushFree U) (ω.eval η) H x x) ∧
              ε (D.eval η) T ∧ PowerlessDefinableMembershipIsomorphism.project_l ψ
                (η.pushFree U) (ω.eval η) H (D.eval η) (D.eval η) := by
  simp only [number_body_m, Formula.satisfies,
    PowerlessDefinableMembershipDiagram.spec_formula_l,
    PowerlessDefinableMembershipCollapse.domain_formula_l, SecondOrderCollapseSyntax.formula_l,
    PowerlessDefinableWholeCollapse.isomorphism_formula_l, PowerlessWholeCollapseSeed.conclusion_m,
    PowerlessWholeCollapseSeed.fixed_formula_l, PowerlessDefinableMembershipIsomorphism.project_formula_l,
    env_id_l, parameters_pushBound_l, parameters_empty_l,
    up₃, up₂, up, Term.eval_weakenBound, Term.eval_weakenFree, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  rfl

private theorem mode_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (Φ : PowerlessClassFiniteElementarity.family_m Γ) (ν : VariableSubstitution ℒ Γ [] Δ)
    (η : Env 𝒱 [] Δ)
    (ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a G S P s t D : Term ℒ [] Δ .set)
    (hCoding : SecondOrderComparisonStageTotal.coding_l K (r₁.eval η) (r₂.eval η)
      (r₃.eval η) (Pair.eval η) (Valid.eval η))
    (hω : SecondOrderOmega.omega_l hℳ (ω.eval η)) :
    (mode_m Φ ν ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a G S P s t D).satisfies η := by
  simp only [mode_m, Formula.satisfies, guard_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, map_formula_l,
    PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l,
    PowerlessDefinableFiniteTraceDerives.zero_formula_l,
    PowerlessRelativeFiniteProgramStep.record_formula_l,
    PowerlessRelativeFiniteProgramInstruction.tags_m,
    PowerlessRelativeFiniteProgramAlphabet.alphabet_formula_l,
    PowerlessRelativeFiniteProgramDomain.domain_formula_l K,
    PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ, subset_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  intro hGuard hC hωC hQ hG h₀ h₁ h₂ hMap hOnto he ha ht hAlphabet hDomain hBC hs htC hst hD hDC hDC₀
  let Ψ := PowerlessClassProgramFiniteRequests.family_m (PowerlessClassFiniteElementarity.requests_m Φ) B ν
  let φ := PowerlessClassProgramHull.operator_m Ψ ω e r₁ r₂ r₃ Pair Valid B P₀ s t
  obtain ⟨_, _, hSeed, _, _, _⟩ := PowerlessClassProgramHull.closure_l K Ψ η
    ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a S P s t
      hCoding hω hGuard hC hωC hQ he ha ht hAlphabet hDomain hBC
  obtain ⟨U, A, T, H, hUC, hU, hUOnto, _, hA, hField, hH, hIso⟩ :=
    PowerlessClassProgramIsomorphism.exists_l K Ψ η
      ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a G S P s t
        hCoding hω hGuard hC hωC hQ hG h₀ h₁ h₂ hMap hOnto he ha ht hAlphabet hDomain hBC hs htC hst
  let ψ := number_m φ (up B) (up C) (up ω) (up Q) (up e) (up t₀) (up t₁) (up t₂)
    (up a) (.bvar .here)
  have hImage (x : Raw) : PowerlessDefinableMembershipIsomorphism.image_l ψ
      (η.pushFree U) (ω.eval η) x ↔
        PowerlessRelativeFiniteProgramVirtualClosure.image_l false φ η (B.eval η) (C.eval η)
          (ω.eval η) (Q.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (P.eval η) x := by
    simpa only [PowerlessDefinableMembershipIsomorphism.image_l, ψ, reading_l K,
      member_l, SecondOrderQuotient.structure_l, PowerlessRelativeFiniteProgramVirtualClosure.image_l] using
        PowerlessRelativeFiniteProgramNumberEvaluation.range_l φ η hU hUOnto x
  have hCover x (hx : ε x (D.eval η)) := (hImage x).mpr (hSeed x (hDC x hx))
  have hDI := (hImage (D.eval η)).mpr (hSeed _ hDC₀)
  have hFixed := PowerlessWholeCollapseSeed.fixed_l ψ (η.pushFree U) (ω.eval η) (D.eval η) T H
    hIso hD (fun x hx z hz => hH.1 x z hx hz) hCover
  have hFixed₀ := PowerlessWholeCollapseSeed.seed_l ψ (η.pushFree U) (ω.eval η) (D.eval η) T H
    hIso hD (fun x hx z hz => hH.1 x z hx hz) hCover hDI
  change (_ ∧ _)
  refine ⟨PowerlessClassProgramElementarity.elementarity_l K Φ ν η
    ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a S P s t
      hCoding hω hGuard hC hωC hQ he ha ht hAlphabet hDomain hBC hs htC hst, ?_⟩
  simp only [Formula.satisfies,
    PowerlessRelativeHierarchySemantics.class_formula_l K, map_formula_l,
    PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l,
    up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here]
  refine ⟨U, hUC, hU, hUOnto, ?_⟩
  apply (PowerlessSourceRebinding.formula_l _ (η.pushBound U)).mpr
  rw [PowerlessSourceOpening.push_l, opening_l]
  exact (number_body_formula_l φ η B C ω Q e t₀ t₁ t₂ a D U).mpr
    ⟨A, T, H, hA, hField, hH, hIso, hFixed, hFixed₀⟩

private def body_m {Γ Δ Θ : SortContext ℒ} (Φ : PowerlessClassFiniteElementarity.family_m Γ)
    (ν : VariableSubstitution ℒ Γ [] Θ)
    (ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a G S P s t D : Term ℒ Δ Θ .set) : Formula ℒ Δ Θ :=
  let τ := @PowerlessSourceRebinding.term_m Δ Θ
  let ν₀ : VariableSubstitution ℒ Γ [] (List.replicate Δ.length .set ++ Θ) :=
    fun {s} v => match s with | .set => τ ((ν v).embedBoundClosed Δ)
  PowerlessSourceRebinding.formula_m <|
    mode_m Φ ν₀ (τ ω) (τ e) (τ r₁) (τ r₂) (τ r₃) (τ Pair) (τ Valid) (τ B) (τ P₀)
      (τ C) (τ Q) (τ t₀) (τ t₁) (τ t₂) (τ a) (τ G) (τ S) (τ P) (τ s) (τ t) (τ D)

def schema_m {Γ Δ : SortContext ℒ} (Φ : PowerlessClassFiniteElementarity.family_m Γ)
    (ν : VariableSubstitution ℒ Γ [] Δ)
    (ω e B P₀ C Q t₀ t₁ t₂ a G S P s t D : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <|
      body_m Φ ν (up₅ ω) (up₅ e) (.bvar (.there (.there (.there (.there .here)))))
        (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here)))
        (.bvar (.there .here)) (.bvar .here) (up₅ B) (up₅ P₀) (up₅ C) (up₅ Q)
        (up₅ t₀) (up₅ t₁) (up₅ t₂) (up₅ a) (up₅ G) (up₅ S) (up₅ P) (up₅ s) (up₅ t) (up₅ D)

def sentence_m {Γ Δ : SortContext ℒ} (Φ : PowerlessClassFiniteElementarity.family_m Γ)
    (ν : VariableSubstitution ℒ Γ [] Δ)
    (ω e B P₀ C Q t₀ t₁ t₂ a G S P s t D : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m Φ ν ω e B P₀ C Q t₀ t₁ t₂ a G S P s t D)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Γ Δ : SortContext ℒ}
    (Φ : PowerlessClassFiniteElementarity.family_m Γ) (ν : VariableSubstitution ℒ Γ [] Δ)
    (ω e B P₀ C Q t₀ t₁ t₂ a G S P s t D : Term ℒ [] Δ .set) :
    (sentence_m Φ ν ω e B P₀ C Q t₀ t₁ t₂ a G S P s t D).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, omega_formula_l]
  intro hω
  have hω' := (SecondOrderOmegaSyntax.omega_l h𝒩 η ω).mp ((omega_formula_l η ω).mpr hω)
  obtain ⟨K, _, r₁, r₂, r₃, Pair, Valid, _, _, hCoding⟩ := SecondOrderComparisonCoding.exists_l hω
  refine ⟨r₁, r₂, r₃, Pair, Valid, ?_⟩
  simp only [body_m, PowerlessSourceRebinding.formula_l]
  apply mode_l K
  · simpa only [PowerlessSourceRebinding.term_l, Term.eval,
      Env.pushBound_bound_here, Env.pushBound_bound_there] using hCoding
  · simpa only [PowerlessSourceRebinding.term_l, up₅, up₃, up₂, up,
      Term.eval_weakenBound] using hω'

theorem derives_m {Γ Δ : SortContext ℒ} (Φ : PowerlessClassFiniteElementarity.family_m Γ)
    (ν : VariableSubstitution ℒ Γ [] Δ)
    (ω e B P₀ C Q t₀ t₁ t₂ a G S P s t D : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m Φ ν ω e B P₀ C Q t₀ t₁ t₂ a G S P s t D)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ h𝒩 => models_l h𝒩 Φ ν ω e B P₀ C Q t₀ t₁ t₂ a G S P s t D)

#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassProgramSeedCollapse
