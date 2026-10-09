import BMSConstructibleBridge.PowerlessRelativeFiniteProgramOriginalSeedDomain
import BMSConstructibleBridge.PowerlessRelativeSourceFamilyElementaryImage

/-! # 原种子、程序域与同一个有限元素性像

对象语言为纯隶属 ℒ，背景为原 Z₂，正式出口为原 Derives 的图翻译句。
先实际构造 C/G/Q/S/P，再在同一组见证上构造原图族和有限元素性像 I。
标签槽与原 Δ 参数一同作为指定种子参数；装配 Θ、排序图及新图不加入种子。
有限 numeral 标签的存在绑定仍由下游解除，本模块不预供种子或闭包像。
本结果是源模型构造的中间对象定理，不是最终 fixed-height BMS 良序定理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSeedFamilyElementaryImage

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev context_m (Θ : SortContext ℒ) := .set :: .set :: .set :: .set :: .set :: Θ
private abbrev free {Θ : SortContext ℒ} (t : Term ℒ [] Θ .set) :=
  t.weakenFree SetTheory.SetSort.set
private abbrev free₂ {Θ : SortContext ℒ} (t : Term ℒ [] Θ .set) := free (free t)
private abbrev free₄ {Θ : SortContext ℒ} (t : Term ℒ [] Θ .set) := free₂ (free₂ t)
private abbrev free₅ {Θ : SortContext ℒ} (t : Term ℒ [] Θ .set) := free (free₄ t)

def payload_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B W ω e t₀ t₁ t₂ a R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] (context_m Θ) :=
  let C : Term ℒ [] (context_m Θ) .set := .fvar (.there (.there (.there (.there .here))))
  let G := .fvar (.there (.there (.there .here)))
  let Q := .fvar (.there (.there .here))
  let S := .fvar (.there .here)
  let P := .fvar .here
  .conj (PowerlessRelativeClassParameterSeedLift.packet_m
      (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) (free₅ B) (free₅ ω) C G
      (fun v => free₅ (τ v))) <|
    .conj (ThirdOrderTheory.subset_m C (free₅ W)) <|
      .conj (PowerlessRelativeHierarchySyntax.class_m (free₅ B) Q) <|
        .conj (PowerlessRelativeFiniteProgramAlphabet.alphabet_m C (free₅ ω)
          (free₅ t₀) (free₅ t₁) (free₅ t₂) Q) <|
          .conj (ThirdOrderTheory.subset_m Q (free₅ W)) <|
            .conj (PowerlessRelativeFiniteProgramDomain.domain_m (free₅ B) (free₅ ω) Q S P)
              (PowerlessRelativeSourceFamilyElementaryImage.conclusion_m Φ (free₅ B) C (free₅ W)
                (free₅ ω) Q (free₅ e) (free₅ t₀) (free₅ t₁) (free₅ t₂) (free₅ a) P
                (free₅ R) (fun v => free₅ (τ v)))

def conclusion_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B W ω e t₀ t₁ t₂ a R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  let φ₀ := payload_m Φ B W ω e t₀ t₁ t₂ a R τ
  let φ₁ := φ₀.existsFreeTop SetTheory.SetSort.set
  let φ₂ := φ₁.existsFreeTop SetTheory.SetSort.set
  let φ₃ := φ₂.existsFreeTop SetTheory.SetSort.set
  let φ₄ := φ₃.existsFreeTop SetTheory.SetSort.set
  φ₄.existsFreeTop SetTheory.SetSort.set

def schema_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B β W ω e t₀ t₁ t₂ a R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  let Δ₁ := PowerlessRelativeSourceFamilyElementaryImage.context_m Φ
  let m := (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length
  .imp (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_m Θ B (fun v => .fvar v)) <|
    .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
      .imp (PowerlessRelativeHierarchySyntax.limit_m β) <|
        .imp (PowerlessRelativeHierarchySyntax.level_m B β W) <|
          .imp (SecondOrderObjectSyntax.member_m B W) <|
            .imp (SecondOrderOmegaSyntax.omega_m ω) <|
              .imp (SecondOrderObjectSyntax.member_m ω W) <|
                .imp (parameters_m Δ₁ W τ) <|
                  .imp (PowerlessRelativeSourceSkolemFamily.distinct_m
                    (PowerlessSourceRequestParameters.tags_m Δ m) τ) <|
                    .imp (SecondOrderObjectSyntax.member_m t₀ W) <|
                      .imp (SecondOrderObjectSyntax.member_m t₁ W) <|
                        .imp (SecondOrderObjectSyntax.member_m t₂ W) <|
                          .imp (PowerlessDefinableFiniteTraceDerives.zero_m e) <|
                            .imp (PowerlessRelativeFiniteProgramStep.record_m e e e a) <|
                              .imp (PowerlessRelativeFiniteProgramInstruction.tags_m t₀ t₁ t₂) <|
                                .imp (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m W R)
                                  (conclusion_m Φ B W ω e t₀ t₁ t₂ a R τ)

def sentence_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B β W ω e t₀ t₁ t₂ a R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m Φ B β W ω e t₀ t₁ t₂ a R τ)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Θ Δ : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B β W ω e t₀ t₁ t₂ a R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) :
    (sentence_m Φ B β W ω e t₀ t₁ t₂ a R τ).TrueIn
      (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeFiniteProgramEvaluationGraph.parameters_formula_l K,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.limit_formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K, SecondOrderOmegaSyntax.omega_l,
    parameters_formula_l, PowerlessRelativeSourceSkolemFamily.distinct_formula_l,
    PowerlessDefinableFiniteTraceDerives.zero_formula_l,
    PowerlessRelativeFiniteProgramStep.record_formula_l,
    PowerlessRelativeFiniteProgramInstruction.tags_m,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  intro η hClass hB hβ hW hBW hω hωW hParams hDistinct h₀ h₁ h₂ he ha ht hR
  have hTerm (t : Term ℒ [] Θ .set) :
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (t.eval η) := by
    match t with
    | .bvar v => nomatch v
    | .fvar v => exact hClass _ v
    | .app f _ => nomatch f
  have hωSub := PowerlessRelativeLevelClosure.transitive_l hℳ hB hW (ω.eval η) hωW
  have hSeed := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
    (PowerlessRelativeFiniteProgramOriginalSeedDomain.models_l hℳ
      (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) B β W ω t₀ t₁ t₂ τ) η
  simp only [PowerlessRelativeFiniteProgramOriginalSeedDomain.schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.limit_formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderOmegaSyntax.omega_l,
    subset_formula_l, parameters_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval] at hSeed
  have hSeed' := hSeed hB hβ hW hBW hω (hTerm ω) hωSub hParams h₀ h₁ h₂
  simp only [PowerlessRelativeFiniteProgramOriginalSeedDomain.conclusion_m, Formula.satisfies,
    PowerlessRelativeClassParameterSeedLift.packet_formula_l K,
    PowerlessRelativeHierarchySemantics.class_formula_l K, subset_formula_l,
    PowerlessRelativeFiniteProgramAlphabet.alphabet_formula_l,
    PowerlessRelativeFiniteProgramDomain.domain_formula_l K,
    Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there] at hSeed'
  obtain ⟨C, G, Q, S, P, hPacket, hCW, hQ, hAlphabet, hQW, hDomain⟩ := hSeed'
  obtain ⟨hC, hG, hMap, hOnto, hωSeed, hBC, hMembers, hBound⟩ := hPacket
  let ξ : Env (SecondOrderQuotient.structure_l hℳ) [] (context_m Θ) :=
    ((((η.pushFree C).pushFree G).pushFree Q).pushFree S).pushFree P
  let C' : Term ℒ [] (context_m Θ) .set := .fvar (.there (.there (.there (.there .here))))
  let G' : Term ℒ [] (context_m Θ) .set := .fvar (.there (.there (.there .here)))
  let Q' : Term ℒ [] (context_m Θ) .set := .fvar (.there (.there .here))
  let S' : Term ℒ [] (context_m Θ) .set := .fvar (.there .here)
  let P' : Term ℒ [] (context_m Θ) .set := .fvar .here
  have hv (t : Term ℒ [] Θ .set) : (free₅ t).eval ξ = t.eval η := by
    simp only [free₅, free₄, free₂, free, ξ, Term.eval_weakenFree]
  have hClass' : ∀ s (v : Variable (context_m Θ) s),
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (ξ.freeVal v) := by
    intro s v
    cases s
    cases v with
    | here => exact hDomain.2.2.1
    | there v =>
      cases v with
      | here => exact hDomain.1
      | there v =>
        cases v with
        | here => exact hQ
        | there v =>
          cases v with
          | here => exact hG
          | there v =>
            cases v with
            | here => exact hC
            | there v => exact hClass _ v
  have hParams' := (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_formula_l K
    (context_m Θ) ξ (free₅ B) (fun v => .fvar v)).mpr (by
      simpa only [hv, Term.eval] using hClass')
  have hFrame := (PowerlessRelativeSourceFamilyClosedImage.frame_formula_l K ξ
    (free₅ B) (free₅ β) C' (free₅ W) (free₅ ω) Q' (free₅ e)
    (free₅ t₀) (free₅ t₁) (free₅ t₂) (free₅ a)).mpr (by
      simp only [hv, C', Q', Term.eval, ξ, Env.pushFree_here, Env.pushFree_there]
      exact ⟨hB, hβ, hW, hBW, hC, hCW, hω, hωW, hQW, he, ha, ht⟩)
  have hParamsW := (parameters_formula_l
    (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) ξ (free₅ W)
    (fun v => free₅ (τ v))).mpr (by simpa only [hv] using hParams)
  have hParamsC := (parameters_formula_l
    (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) ξ C'
    (fun v => free₅ (τ v))).mpr (by
      change ∀ s (v : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) s),
        mem_l hℳ ((free₅ (τ v)).eval ξ) C
      simpa only [hv] using hMembers)
  have hDistinct' := (PowerlessRelativeSourceSkolemFamily.distinct_formula_l
    (PowerlessSourceRequestParameters.tags_m Δ
      (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length)
    (fun v => free₅ (τ v)) ξ).mpr (by simpa only [hv] using hDistinct)
  have hSource := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
    (PowerlessRelativeSourceFamilyElementaryImage.models_l hℳ Φ
      (free₅ B) (free₅ β) C' (free₅ W) (free₅ ω) Q' G' (free₅ e)
      (free₅ t₀) (free₅ t₁) (free₅ t₂) (free₅ a) S' P' (free₅ R)
      (fun v => free₅ (τ v))) ξ
  simp only [PowerlessRelativeSourceFamilyElementaryImage.schema_m, Formula.satisfies,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    PowerlessRelativeFiniteProgramDomain.domain_formula_l K, map_formula_l,
    PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l,
    PowerlessRelativeFiniteProgramAlphabet.alphabet_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, hv,
    C', G', Q', S', P', Term.eval, ξ, Env.pushFree_here, Env.pushFree_there] at hSource
  have hSource' := hSource hParams' hFrame hR hParamsW hParamsC hDistinct'
    hDomain hMap hOnto hAlphabet hBC
  simp only [conclusion_m, Formula.satisfies_existsFreeTop]
  refine ⟨C, G, Q, S, P, ?_⟩
  change (payload_m Φ B W ω e t₀ t₁ t₂ a R τ).satisfies ξ
  simp only [payload_m, Formula.satisfies,
    PowerlessRelativeClassParameterSeedLift.packet_formula_l K, subset_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeFiniteProgramAlphabet.alphabet_formula_l,
    PowerlessRelativeFiniteProgramDomain.domain_formula_l K, hv,
    Term.eval, ξ, Env.pushFree_here, Env.pushFree_there]
  exact ⟨⟨hC, hG, hMap, hOnto, hωSeed, hBC, hMembers, hBound⟩,
    hCW, hQ, hAlphabet, hQW, hDomain, hSource'⟩

theorem derives_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B β W ω e t₀ t₁ t₂ a R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m Φ B β W ω e t₀ t₁ t₂ a R τ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ =>
    models_l hℳ Φ B β W ω e t₀ t₁ t₂ a R τ)

#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSeedFamilyElementaryImage
