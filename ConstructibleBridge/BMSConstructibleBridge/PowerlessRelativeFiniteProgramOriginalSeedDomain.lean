import BMSConstructibleBridge.PowerlessRelativeClassParameterSeedLift
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramLevelDomain
import BMSConstructibleBridge.PowerlessRelativeLimitDeltaSeparationDerives

/-! # 从原有限源参数同时构造种子、实际枚举与全程序域

原 Δ 经 τ 放入装配上下文 Ε。先取得同一 C/G 及共同母界规格，再由
实际层守卫回收 C⊆W，并真正构造 Q、Seq(Q)、Seq(Q)×ω。
对象句同时绑定全部五个见证；新环境中的其他变量不自动成为种子成员。
不预供种子或程序域，不把单射可数性误作实际满射，也不要求 Q∈W。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramOriginalSeedDomain

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Ε : SortContext ℒ} (t : Term ℒ Γ Ε .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Ε : SortContext ℒ} (t : Term ℒ Γ Ε .set) := up (up t)
private abbrev up₄ {Γ Ε : SortContext ℒ} (t : Term ℒ Γ Ε .set) := up₂ (up₂ t)
private abbrev up₅ {Γ Ε : SortContext ℒ} (t : Term ℒ Γ Ε .set) := up (up₄ t)

def conclusion_m {Ε : SortContext ℒ} (Δ : SortContext ℒ)
    (B W ω t₀ t₁ t₂ : Term ℒ [] Ε .set) (τ : VariableSubstitution ℒ Δ [] Ε) : Formula ℒ [] Ε :=
  .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <|
    let C : Term ℒ [.set, .set, .set, .set, .set] Ε .set :=
      .bvar (.there (.there (.there (.there .here))))
    let G := .bvar (.there (.there (.there .here)))
    let Q := .bvar (.there (.there .here))
    let S := .bvar (.there .here)
    let P := .bvar .here
    .conj (PowerlessRelativeClassParameterSeedLift.packet_m Δ
      (up₅ B) (up₅ ω) C G (fun v => up₅ (τ v))) <|
      .conj (ThirdOrderTheory.subset_m C (up₅ W)) <|
        .conj (PowerlessRelativeHierarchySyntax.class_m (up₅ B) Q) <|
          .conj (PowerlessRelativeFiniteProgramAlphabet.alphabet_m
            C (up₅ ω) (up₅ t₀) (up₅ t₁) (up₅ t₂) Q) <|
            .conj (ThirdOrderTheory.subset_m Q (up₅ W))
              (PowerlessRelativeFiniteProgramDomain.domain_m (up₅ B) (up₅ ω) Q S P)

def schema_m {Ε : SortContext ℒ} (Δ : SortContext ℒ)
    (B β W ω t₀ t₁ t₂ : Term ℒ [] Ε .set) (τ : VariableSubstitution ℒ Δ [] Ε) : Formula ℒ [] Ε :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.limit_m β) <|
      .imp (PowerlessRelativeHierarchySyntax.level_m B β W) <|
        .imp (SecondOrderObjectSyntax.member_m B W) <|
          .imp (SecondOrderOmegaSyntax.omega_m ω) <|
            .imp (PowerlessRelativeHierarchySyntax.class_m B ω) <|
              .imp (ThirdOrderTheory.subset_m ω W) <|
                .imp (parameters_m Δ W τ) <|
                  .imp (SecondOrderObjectSyntax.member_m t₀ W) <|
                    .imp (SecondOrderObjectSyntax.member_m t₁ W) <|
                      .imp (SecondOrderObjectSyntax.member_m t₂ W)
                        (conclusion_m Δ B W ω t₀ t₁ t₂ τ)

def sentence_m {Ε : SortContext ℒ} (Δ : SortContext ℒ)
    (B β W ω t₀ t₁ t₂ : Term ℒ [] Ε .set) (τ : VariableSubstitution ℒ Δ [] Ε) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m Δ B β W ω t₀ t₁ t₂ τ)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Ε : SortContext ℒ}
    (Δ : SortContext ℒ) (B β W ω t₀ t₁ t₂ : Term ℒ [] Ε .set)
    (τ : VariableSubstitution ℒ Δ [] Ε) :
    (sentence_m Δ B β W ω t₀ t₁ t₂ τ).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.limit_formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderOmegaSyntax.omega_l,
    subset_formula_l, parameters_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  intro η hB hβ hW hBW hω hωC hωW hParams h₀ h₁ h₂
  have hWC := PowerlessRelativeLevelClosure.class_l hℳ hB hW
  have hParamsC : ∀ s (v : Variable Δ s),
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) ((τ v).eval η) := by
    intro s v
    cases s
    exact PowerlessRelativeClassCorrespondence.transitive_l hℳ hB hWC (hParams _ v)
  have hSeed := PowerlessRelativeClassParameterSeedLift.exists_l K Δ η B ω τ hB hω hωC hParamsC
  simp only [PowerlessRelativeClassParameterSeedLift.conclusion_m, Formula.satisfies,
    PowerlessRelativeClassParameterSeedLift.packet_formula_l K,
    Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there] at hSeed
  obtain ⟨C, G, hC, hG, hMap, hOnto, hωSeed, hb, hMembers, hBound⟩ := hSeed
  have hCW := hBound (W.eval η) hWC hωW hBW hParams
  obtain ⟨Q, S, P, hQ, hAlphabet, hQW, hDomain⟩ :=
    PowerlessRelativeFiniteProgramLevelDomain.exists_l hB hβ hW hC hω hωC hCW hωW h₀ h₁ h₂
  simp only [conclusion_m, Formula.satisfies,
    PowerlessRelativeClassParameterSeedLift.packet_formula_l K,
    PowerlessRelativeHierarchySemantics.class_formula_l K, subset_formula_l,
    PowerlessRelativeFiniteProgramAlphabet.alphabet_formula_l,
    PowerlessRelativeFiniteProgramDomain.domain_formula_l K,
    up₅, up₄, up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  exact ⟨C, G, Q, S, P, ⟨hC, hG, hMap, hOnto, hωSeed, hb, hMembers, hBound⟩,
    hCW, hQ, hAlphabet, hQW, hDomain⟩

theorem derives_m {Ε : SortContext ℒ} (Δ : SortContext ℒ)
    (B β W ω t₀ t₁ t₂ : Term ℒ [] Ε .set) (τ : VariableSubstitution ℒ Δ [] Ε) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m Δ B β W ω t₀ t₁ t₂ τ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ Δ B β W ω t₀ t₁ t₂ τ)

#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramOriginalSeedDomain
