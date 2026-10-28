import BMSConstructibleBridge.PowerlessClassFiniteElementarity
import BMSConstructibleBridge.PowerlessClassProgramFiniteRequests

/-! # 同一实际程序的类有限元素性原 Z₂ 推导

对象语言为纯隶属 ℒ，背景为原 Z₂。原有限族的存在矩阵及全称否定矩阵
决定同一打包请求族；其原全码域的虚拟像定义子域。元素性正文只守卫
原绑定值与原参数，不要求其余编码元数据在子域中。实际构造规格消去
请求闭包前提，编码包在对象句中存在量化。该模式仍不是最终 BMS 良序句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassProgramElementarity

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderCanonicalLevelDerives (guard_m guard_l guard_formula_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessSourceClass.structure_l PowerlessSourceClass.type_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (v : Term ℒ Γ Δ .set) :=
  v.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (v : Term ℒ Γ Δ .set) := up (up v)
private abbrev up₃ {Γ Δ : SortContext ℒ} (v : Term ℒ Γ Δ .set) := up (up₂ v)
private abbrev up₅ {Γ Δ : SortContext ℒ} (v : Term ℒ Γ Δ .set) := up₂ (up₃ v)

/-- 域公式使用同一完整求值图；原公式族及原参数替换均保持。 -/
def image_m {Γ Δ : SortContext ℒ} (Φ : PowerlessClassFiniteElementarity.family_m Γ)
    (ν : VariableSubstitution ℒ Γ [] Δ)
    (ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a P s t : Term ℒ [] Δ .set) :
    Formula ℒ [] (.set :: Δ) :=
  let Ψ := PowerlessClassProgramFiniteRequests.family_m
    (PowerlessClassFiniteElementarity.requests_m Φ) B ν
  let φ := PowerlessClassProgramHull.operator_m Ψ ω e r₁ r₂ r₃ Pair Valid B P₀ s t
  let θ := PowerlessClassProgramRequests.evaluation_m φ B C ω Q e t₀ t₁ t₂ a
  PowerlessDefinableMembershipIsomorphism.image_m θ
    (Term.weakenFree (σ := ℒ) SetTheory.SetSort.set P) (.fvar .here)
      (fun v => .fvar (.there v))

def conclusion_m {Γ Δ : SortContext ℒ} (Φ : PowerlessClassFiniteElementarity.family_m Γ)
    (ν : VariableSubstitution ℒ Γ [] Δ)
    (ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a P s t : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  let E := image_m Φ ν ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a P s t
  .imp (PowerlessClassFiniteElementarity.parameters_m E ν)
    (PowerlessClassFiniteElementarity.form_m (PowerlessClassProgramFiniteRequests.domain_m B) E Φ ν)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "ε" => SecondOrderQuotient.mem_l hℳ

theorem image_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (Φ : PowerlessClassFiniteElementarity.family_m Γ) (ν : VariableSubstitution ℒ Γ [] Δ)
    (ξ : Env 𝒱 [] Δ)
    (ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a P s t : Term ℒ [] Δ .set) (x : Raw) :
    (image_m Φ ν ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a P s t).satisfies (ξ.pushFree x) ↔
      PowerlessClassProgramFiniteRequests.image_l (PowerlessClassFiniteElementarity.requests_m Φ)
        ν ξ ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a P s t x := by
  let Ψ := PowerlessClassProgramFiniteRequests.family_m
    (PowerlessClassFiniteElementarity.requests_m Φ) B ν
  let φ := PowerlessClassProgramHull.operator_m Ψ ω e r₁ r₂ r₃ Pair Valid B P₀ s t
  let θ := PowerlessClassProgramRequests.evaluation_m φ B C ω Q e t₀ t₁ t₂ a
  have hEnv : PowerlessDefinableMembershipDiagram.env_l
      (ξ.pushFree (sort := SetTheory.SetSort.set) x)
      (fun v : Variable Δ .set => .fvar (.there v)) = ξ := by
    apply Env.ext
    · intro _ v; nomatch v
    · intro s v; cases s; rfl
  change (PowerlessDefinableMembershipIsomorphism.image_m θ
    (Term.weakenFree (σ := ℒ) SetTheory.SetSort.set P) (.fvar .here)
      (fun v => .fvar (.there v))).satisfies (ξ.pushFree x) ↔ _
  rw [PowerlessDefinableMembershipIsomorphism.image_formula_l, hEnv,
    Term.eval_weakenFree]
  exact PowerlessClassProgramRequests.image_formula_l K φ ξ B C ω Q e t₀ t₁ t₂ a P x

/-- 请求闭包从原构造取得，不作为元素性模式的新前提。 -/
theorem elementarity_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (Φ : PowerlessClassFiniteElementarity.family_m Γ) (ν : VariableSubstitution ℒ Γ [] Δ)
    (ξ : Env 𝒱 [] Δ)
    (ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a S P s t : Term ℒ [] Δ .set)
    (hCoding : SecondOrderComparisonStageTotal.coding_l K (r₁.eval ξ) (r₂.eval ξ)
      (r₃.eval ξ) (Pair.eval ξ) (Valid.eval ξ))
    (hω : SecondOrderOmega.omega_l hℳ (ω.eval ξ))
    (hGuard : guard_l (B.eval ξ) (P₀.eval ξ))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval ξ) (C.eval ξ))
    (hωC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval ξ) (ω.eval ξ))
    (hQ : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval ξ) (Q.eval ξ))
    (he : ∀ x, ¬ε x (e.eval ξ))
    (ha : PowerlessRelativeFiniteProgramStep.record_l (e.eval ξ) (e.eval ξ) (e.eval ξ) (a.eval ξ))
    (ht : t₀.eval ξ ≠ t₁.eval ξ ∧ t₀.eval ξ ≠ t₂.eval ξ ∧ t₁.eval ξ ≠ t₂.eval ξ)
    (hAlphabet : ∀ q, ε q (Q.eval ξ) ↔
      PowerlessRelativeFiniteProgramAlphabet.instruction_l (C.eval ξ) (ω.eval ξ)
        (t₀.eval ξ) (t₁.eval ξ) (t₂.eval ξ) q)
    (hDomain : PowerlessRelativeFiniteProgramDomain.domain_l (B.eval ξ) (ω.eval ξ)
      (Q.eval ξ) (S.eval ξ) (P.eval ξ))
    (hBC : ε (B.eval ξ) (C.eval ξ)) (hs : ε (s.eval ξ) (C.eval ξ))
    (htC : ε (t.eval ξ) (C.eval ξ)) (hst : s.eval ξ ≠ t.eval ξ) :
    (conclusion_m Φ ν ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a P s t).satisfies ξ := by
  let Λ := PowerlessClassFiniteElementarity.requests_m Φ
  let Ψ := PowerlessClassProgramFiniteRequests.family_m Λ B ν
  let A : Raw → Prop := fun x => PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval ξ) x
  let I := PowerlessClassProgramFiniteRequests.image_l Λ ν ξ
    ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a P s t
  let D := PowerlessClassProgramFiniteRequests.domain_m B
  let E := image_m Φ ν ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a P s t
  have hE : ∀ x, E.satisfies (ξ.pushFree x) ↔ I x :=
    image_formula_l K Φ ν ξ ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a P s t
  obtain ⟨_, hClass, hSeed, _, _, _⟩ := PowerlessClassProgramHull.closure_l K Ψ ξ
    ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a S P s t
      hCoding hω hGuard hC hωC hQ he ha ht hAlphabet hDomain hBC
  have hI : ∃ x, I x := ⟨B.eval ξ, hSeed _ hBC⟩
  have hBase : ∀ x, ε x (B.eval ξ) → ∀ z, ε z x → ε z (B.eval ξ) :=
    fun x hx z hz => hGuard.2.1 x z hx hz
  have hA : ∃ x, A x := ⟨B.eval ξ, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩
  change (PowerlessClassFiniteElementarity.parameters_m E ν).satisfies ξ →
    (PowerlessClassFiniteElementarity.form_m D E Φ ν).satisfies ξ
  intro hParams
  have hν := (PowerlessClassFiniteElementarity.parameters_formula_l E ν ξ hE).mp hParams
  let η : Env (PowerlessSourceClass.structure_l (ℳ := 𝒱) I hI) [] Γ :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with | .set => ⟨(ν v).eval ξ, hν v⟩ }
  let η₀ := PowerlessSourceClassInclusion.env_l (hP := hA) hClass η
  have hClosed := PowerlessClassProgramFiniteRequests.requests_l K Λ ν ξ
    ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a S P s t
      hCoding hω hGuard hC hωC hQ he ha ht hAlphabet hDomain hBC hs htC hst η₀
        (fun _ => rfl)
  have hFree : PowerlessSourceClass.free_l η₀ = η₀ := by
    apply Env.ext
    · intro _ v; nomatch v
    · intro _ _; rfl
  apply PowerlessClassFiniteElementarity.formula_l D E Φ ν ξ η hClass (fun _ => rfl)
    (PowerlessClassProgramFiniteRequests.domain_formula_l K ξ B) hE
  intro p hp
  rw [hFree]
  apply PowerlessSourcePredicateRequests.subset_l (hΦ := hClosed)
  intro q hq
  exact List.mem_flatMap.mpr ⟨p, hp, hq⟩

private def mode_m {Γ Δ : SortContext ℒ} (Φ : PowerlessClassFiniteElementarity.family_m Γ)
    (ν : VariableSubstitution ℒ Γ [] Δ)
    (ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a S P s t : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (guard_m B P₀) <| .imp (PowerlessRelativeHierarchySyntax.class_m B C) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B ω) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B Q) <|
        .imp (PowerlessDefinableFiniteTraceDerives.zero_m e) <|
          .imp (PowerlessRelativeFiniteProgramStep.record_m e e e a) <|
            .imp (PowerlessRelativeFiniteProgramInstruction.tags_m t₀ t₁ t₂) <|
              .imp (PowerlessRelativeFiniteProgramAlphabet.alphabet_m C ω t₀ t₁ t₂ Q) <|
                .imp (PowerlessRelativeFiniteProgramDomain.domain_m B ω Q S P) <|
                  .imp (SecondOrderObjectSyntax.member_m B C) <|
                    .imp (SecondOrderObjectSyntax.member_m s C) <|
                      .imp (SecondOrderObjectSyntax.member_m t C) <| .imp (.neg (.equal s t))
                        (conclusion_m Φ ν ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a P s t)

private theorem mode_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (Φ : PowerlessClassFiniteElementarity.family_m Γ) (ν : VariableSubstitution ℒ Γ [] Δ)
    (ξ : Env 𝒱 [] Δ)
    (ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a S P s t : Term ℒ [] Δ .set)
    (hCoding : SecondOrderComparisonStageTotal.coding_l K (r₁.eval ξ) (r₂.eval ξ)
      (r₃.eval ξ) (Pair.eval ξ) (Valid.eval ξ))
    (hω : SecondOrderOmega.omega_l hℳ (ω.eval ξ)) :
    (mode_m Φ ν ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a S P s t).satisfies ξ := by
  simp only [mode_m, Formula.satisfies, guard_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessDefinableFiniteTraceDerives.zero_formula_l,
    PowerlessRelativeFiniteProgramStep.record_formula_l,
    PowerlessRelativeFiniteProgramInstruction.tags_m,
    PowerlessRelativeFiniteProgramAlphabet.alphabet_formula_l,
    PowerlessRelativeFiniteProgramDomain.domain_formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  intro hGuard hC hωC hQ he ha ht hAlphabet hDomain hBC hs htC hst
  exact elementarity_l K Φ ν ξ ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a S P s t
    hCoding hω hGuard hC hωC hQ he ha ht hAlphabet hDomain hBC hs htC hst

private def body_m {Γ Δ Θ : SortContext ℒ} (Φ : PowerlessClassFiniteElementarity.family_m Γ)
    (ν : VariableSubstitution ℒ Γ [] Θ)
    (ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a S P s t : Term ℒ Δ Θ .set) : Formula ℒ Δ Θ :=
  let τ := @PowerlessSourceRebinding.term_m Δ Θ
  let ν₀ : VariableSubstitution ℒ Γ [] (List.replicate Δ.length .set ++ Θ) :=
    fun {s} v => match s with | .set => τ ((ν v).embedBoundClosed Δ)
  PowerlessSourceRebinding.formula_m <|
    mode_m Φ ν₀ (τ ω) (τ e) (τ r₁) (τ r₂) (τ r₃) (τ Pair) (τ Valid) (τ B) (τ P₀)
      (τ C) (τ Q) (τ t₀) (τ t₁) (τ t₂) (τ a) (τ S) (τ P) (τ s) (τ t)

def schema_m {Γ Δ : SortContext ℒ} (Φ : PowerlessClassFiniteElementarity.family_m Γ)
    (ν : VariableSubstitution ℒ Γ [] Δ)
    (ω e B P₀ C Q t₀ t₁ t₂ a S P s t : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <|
      body_m Φ ν (up₅ ω) (up₅ e) (.bvar (.there (.there (.there (.there .here)))))
        (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here)))
        (.bvar (.there .here)) (.bvar .here) (up₅ B) (up₅ P₀) (up₅ C) (up₅ Q)
        (up₅ t₀) (up₅ t₁) (up₅ t₂) (up₅ a) (up₅ S) (up₅ P) (up₅ s) (up₅ t)

def sentence_m {Γ Δ : SortContext ℒ} (Φ : PowerlessClassFiniteElementarity.family_m Γ)
    (ν : VariableSubstitution ℒ Γ [] Δ)
    (ω e B P₀ C Q t₀ t₁ t₂ a S P s t : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m Φ ν ω e B P₀ C Q t₀ t₁ t₂ a S P s t)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Γ Δ : SortContext ℒ}
    (Φ : PowerlessClassFiniteElementarity.family_m Γ) (ν : VariableSubstitution ℒ Γ [] Δ)
    (ω e B P₀ C Q t₀ t₁ t₂ a S P s t : Term ℒ [] Δ .set) :
    (sentence_m Φ ν ω e B P₀ C Q t₀ t₁ t₂ a S P s t).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro ξ
  simp only [schema_m, Formula.satisfies, omega_formula_l]
  intro hω
  have hω' := (SecondOrderOmegaSyntax.omega_l h𝒩 ξ ω).mp ((omega_formula_l ξ ω).mpr hω)
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
    (ω e B P₀ C Q t₀ t₁ t₂ a S P s t : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m Φ ν ω e B P₀ C Q t₀ t₁ t₂ a S P s t)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ h𝒩 => models_l h𝒩 Φ ν ω e B P₀ C Q t₀ t₁ t₂ a S P s t)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassProgramElementarity
