import BMSConstructibleBridge.PowerlessRelativeSourceFamilyElementaryImage
import BMSConstructibleBridge.PowerlessCodedHistoryCaptureSyntax
import BMSConstructibleBridge.PowerlessRelativeMemberCodedCoverage

/-! # 抽象共同族上的完整局部前史捕获

先对抽象原公式族 Φ 核验同一实际存在树的运输；Φ 包含两个完整覆盖
模板的前提只是外部有限 AST 列表的包含性证明，不是新的模型公理或
元素性假设。原实际请求闭包构造提供元素性、全部参数成员性与同一 I。
首 Ω 来源守卫下，全部 x∈I 的十七见证同属此 I，完整资格在同一 W
中成立。正式出口为原 Z₂ Derives，完整 Collection 及终局仍待闭合。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceFamilyCodedCapture

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open SecondOrderObjectSyntax (member_m)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)
open PowerlessRelativeSourceFamilyClosedImage (term_m frame_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l PowerlessMemberStructure.type_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev Entry (Ε : SortContext ℒ) := Term ℒ [] Ε .set × Term ℒ [] Ε .set
private abbrev up {Γ Ε : SortContext ℒ} (t : Term ℒ Γ Ε .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev free {Ε : SortContext ℒ} (t : Term ℒ [] Ε .set) :=
  t.weakenFree SetTheory.SetSort.set

def source_m {Γ Ε : SortContext ℒ} (B ω W : Term ℒ Γ Ε .set) : Formula ℒ Γ Ε :=
  .conj (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .conj (SecondOrderOmegaSyntax.omega_m ω) <| .existsE .set <|
      .conj (PowerlessRelativeOrdinalCutoff.first_m (up B) (up ω) (.bvar .here))
        (PowerlessRelativeHierarchySyntax.level_m (up B) (.bvar .here) (up W))

private def binding_m {Ε : SortContext ℒ} : Substitution ℒ [] (.set :: Ε) [.set] Ε :=
  .map (fun v => nomatch v) (fun {s} v => match s with
    | .set => match v with | .here => .bvar .here | .there v => .fvar v)

private def elementary_m {Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) :
    Formula ℒ [.set] Ε :=
  (PowerlessRelativeFiniteElementarity.form_m Φ (.fvar .here) (free W)
    (fun v => free (τ v))).substitute binding_m

private theorem elementary_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ) (W : Term ℒ [] Ε .set)
    (τ : Variable Δ .set → Term ℒ [] Ε .set) (ζ : Env 𝒩 [] Ε) (I : carrier_l 𝒩) :
    (elementary_m Φ W τ).satisfies (ζ.pushBound (sort := SetTheory.SetSort.set) I) ↔
      (PowerlessRelativeFiniteElementarity.form_m Φ (.fvar .here) (free W)
        (fun v => free (τ v))).satisfies (ζ.pushFree I) := by
  rw [elementary_m, Formula.satisfies_substitute]
  have h : (ζ.pushBound (sort := SetTheory.SetSort.set) I).pullback binding_m = ζ.pushFree I := by
    apply Env.ext
    · intro s v; nomatch v
    · intro s v; cases s; cases v <;> rfl
  rw [h]

private def original_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) (v : Variable Δ .set) : Term ℒ [] Θ .set :=
  τ (PowerlessSourceOpening.skip_m
    (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length v)

private def uniform_m {Γ Ε : SortContext ℒ} (I W B ω : Term ℒ Γ Ε .set) : Formula ℒ Γ Ε :=
  .forallE .set <| .imp (member_m (.bvar .here) (up I))
    (PowerlessCodedHistoryCaptureSyntax.formula_m (up I) (up W) (up B) (up ω) (.bvar .here))

/-- 追加全部 x 的捕获字段，I 仍只由原实际存在块绑定一次。 -/
def terminal_m {Θ Δ Ε : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ) (vB vω : Variable Δ .set)
    (B C W ω Q e t₀ t₁ t₂ a P : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set)
    (σ : Variable Θ .set → Term ℒ [] Ε .set) (J : List (Entry Ε)) : Formula ℒ [] Ε :=
  let ρ := fun v => term_m (original_m Φ τ v) σ
  let B₀ := ρ vB
  let ω₀ := ρ vω
  .existsE .set <| .conj
    (PowerlessRelativeSourceFamilyElementaryImage.body_m J (term_m B σ) (term_m C σ)
      (term_m W σ) (term_m ω σ) (term_m Q σ) (term_m e σ)
      (term_m t₀ σ) (term_m t₁ σ) (term_m t₂ σ) (term_m a σ) (term_m P σ)) <|
    .conj (elementary_m Φ (term_m W σ) ρ) <|
      .conj (parameters_m Δ (.bvar .here) (fun v => up (ρ v)))
        (.imp (source_m (up B₀) (up ω₀) (up (term_m W σ)))
          (uniform_m (.bvar .here) (up (term_m W σ)) (up B₀) (up ω₀)))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem source_formula_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (K : source_coding_l hℳ) {Γ Ε : SortContext ℒ}
    (ζ : Env (SecondOrderQuotient.structure_l hℳ) Γ Ε) (B ω W : Term ℒ Γ Ε .set) :
    (source_m B ω W).satisfies ζ ↔
      (∀ x, mem_l hℳ x (B.eval ζ) → ∀ y, mem_l hℳ y x → mem_l hℳ y (B.eval ζ)) ∧
      SecondOrderOmega.omega_l hℳ (ω.eval ζ) ∧
      ∃ Ω, PowerlessRelativeOrdinalCutoff.first_l (B.eval ζ) (ω.eval ζ) Ω ∧
        PowerlessRelativeHierarchySemantics.level_l hℳ (B.eval ζ) Ω (W.eval ζ) := by
  simp only [source_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeOrdinalCutoff.first_formula_l K,
    PowerlessRelativeHierarchySemantics.level_formula_l K, up, Term.eval_weakenBound,
    Term.eval, Env.pushBound_bound_here]
  rfl

/-- 从原实际共同族末端构造全部捕获，绝不预供另一 I 或完整源模型。 -/
theorem terminal_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (K : source_coding_l hℳ) {Θ Δ Ε : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (vB vω : Variable Δ .set)
    (B C W ω Q e t₀ t₁ t₂ a P : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set)
    (σ : Variable Θ .set → Term ℒ [] Ε .set) (J : List (Entry Ε))
    (ζ : Env (SecondOrderQuotient.structure_l hℳ) [] Ε)
    (h : (PowerlessRelativeSourceFamilyElementaryImage.terminal_m Φ
      B C W ω Q e t₀ t₁ t₂ a P τ σ J).satisfies ζ) :
    (terminal_m Φ vB vω B C W ω Q e t₀ t₁ t₂ a P τ σ J).satisfies ζ := by
  let ρ := fun v => term_m (original_m Φ τ v) σ
  obtain ⟨I, hBody, hElem, hParams⟩ :=
    (PowerlessRelativeSourceFamilyElementaryImage.terminal_formula_l Φ
      B C W ω Q e t₀ t₁ t₂ a P τ σ J ζ).mp h
  change ∃ I, (PowerlessRelativeSourceFamilyElementaryImage.body_m J (term_m B σ)
    (term_m C σ) (term_m W σ) (term_m ω σ) (term_m Q σ) (term_m e σ)
    (term_m t₀ σ) (term_m t₁ σ) (term_m t₂ σ) (term_m a σ) (term_m P σ)).satisfies (ζ.pushBound (sort := SetTheory.SetSort.set) I) ∧
    (elementary_m Φ (term_m W σ) ρ).satisfies (ζ.pushBound (sort := SetTheory.SetSort.set) I) ∧
    (parameters_m Δ (.bvar .here) (fun v => up (ρ v))).satisfies (ζ.pushBound (sort := SetTheory.SetSort.set) I) ∧
    ((source_m (up (ρ vB)) (up (ρ vω))
      (up (term_m W σ))).satisfies (ζ.pushBound (sort := SetTheory.SetSort.set) I) →
      (uniform_m (.bvar .here) (up (term_m W σ)) (up (ρ vB))
        (up (ρ vω))).satisfies (ζ.pushBound (sort := SetTheory.SetSort.set) I))
  refine ⟨I, hBody, (elementary_formula_l Φ (term_m W σ) ρ ζ I).mpr hElem, ?_, ?_⟩
  · apply (parameters_formula_l (Δ) (ζ.pushBound (sort := SetTheory.SetSort.set) I) (.bvar .here)
      (fun v => up (ρ v))).mpr
    intro s v; cases s
    simpa only [up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here,
      ThirdOrderSemantics.member_l, ρ, original_m] using hParams v
  · intro hSource
    obtain ⟨hBase, hω, Ω, hΩ, hW⟩ := (source_formula_l hℳ K (ζ.pushBound (sort := SetTheory.SetSort.set) I)
      (up (ρ vB)) (up (ρ vω))
      (up (term_m W σ))).mp hSource
    simp only [up, Term.eval_weakenBound] at hBase hω hΩ hW
    have hIW : subset_l (ℳ := SecondOrderQuotient.structure_l hℳ) I ((term_m W σ).eval ζ) := by
      simpa only [ThirdOrderSemantics.subset_formula_l, up, Term.eval_weakenBound,
        Term.eval, Env.pushBound_bound_here] using hBody.2.2.1
    have hρ : ∀ v : Variable Δ .set,
        member_l (SecondOrderQuotient.structure_l hℳ) ((ρ v).eval ζ) I := hParams
    have hI : ∃ z, member_l (SecondOrderQuotient.structure_l hℳ) z I :=
      ⟨(ρ vB).eval ζ, hρ vB⟩
    have hW₀ : ∃ z, member_l (SecondOrderQuotient.structure_l hℳ) z ((term_m W σ).eval ζ) :=
      ⟨(ρ vB).eval ζ, hIW _ (hρ vB)⟩
    let ν : Env (PowerlessMemberStructure.structure_l
        (ℳ := SecondOrderQuotient.structure_l hℳ) I hI) [] Δ :=
      { boundVal := fun v => nomatch v
        freeVal := fun {s} v => match s with | .set => ⟨(ρ v).eval ζ, hρ v⟩ }
    have hTrans : PowerlessNaturalOrder.transitive_l
        (ℳ := SecondOrderQuotient.structure_l hℳ) ((term_m W σ).eval ζ) :=
      fun z t hz ht => PowerlessRelativeLevelClosure.transitive_l hℳ hBase hW z hz t ht
    have hExt : SetTheory.Extensional (SetTheory.Definitional.Project.FirstOrderSemantics.reduct
        (PowerlessMemberStructure.structure_l
          (ℳ := SecondOrderQuotient.structure_l hℳ) ((term_m W σ).eval ζ) hW₀)) := by
      refine ⟨?_⟩
      intro a b h
      apply Subtype.ext
      apply SecondOrderQuotient.ext_l hℳ
      intro z
      constructor
      · intro hz
        exact (h ⟨z, hTrans a.val z a.property hz⟩).mp hz
      · intro hz
        exact (h ⟨z, hTrans b.val z b.property hz⟩).mpr hz
    have hCoverElem := PowerlessRelativeFiniteElementarity.subfamily_formula_l
      (PowerlessRelativeFiniteHullCodedCoverage.family_m Δ) Φ hΦ
      (ζ.pushFree I) (.fvar .here) (free (term_m W σ)) (fun v => free (ρ v)) hElem
    change ∀ x, member_l (SecondOrderQuotient.structure_l hℳ) x I →
      (PowerlessCodedHistoryCaptureSyntax.formula_m (.bvar (.there .here))
        (up (up (term_m W σ))) (up (up (ρ vB)))
        (up (up (ρ vω))) (.bvar .here)).satisfies
        ((ζ.pushBound (sort := SetTheory.SetSort.set) I).pushBound (sort := SetTheory.SetSort.set) x)
    intro x hx
    let B₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I :=
      ⟨(ρ vB).eval ζ, hρ vB⟩
    let ω₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I :=
      ⟨(ρ vω).eval ζ,
        hρ vω⟩
    let x₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I := ⟨x, hx⟩
    have hCover := PowerlessRelativeMemberCodedCoverage.exists_l (hW₀ := hW₀) K
      (PowerlessSourceInclusion.inclusion_l hIW B₀)
      (PowerlessSourceInclusion.inclusion_l hIW ω₀)
      (PowerlessSourceInclusion.inclusion_l hIW x₀) hBase hω hΩ hW
    have hCapture := PowerlessRelativeFiniteHullCodedCoverage.capture_l
      (hI := hI) (hW := hW₀) (ζ.pushFree I) (.fvar .here) (free (term_m W σ))
      (fun v => free (ρ v)) ν (fun v => by simp only [free, Term.eval_weakenFree, ν])
      hIW rfl (by simp only [free, Term.eval_weakenFree]) hExt B₀ ω₀ x₀ hCoverElem hCover
    exact (PowerlessCodedHistoryCaptureSyntax.formula_l ((ζ.pushBound (sort := SetTheory.SetSort.set) I).pushBound (sort := SetTheory.SetSort.set) x)
      (.bvar (.there .here)) (up (up (term_m W σ))) (up (up (ρ vB)))
      (up (up (ρ vω))) (.bvar .here)
      hIW rfl (by simp only [up, Term.eval_weakenBound]) hExt B₀ ω₀ x₀
      (by simp only [up, Term.eval_weakenBound]; rfl)
      (by simp only [up, Term.eval_weakenBound]; rfl) rfl).mpr hCapture

def conclusion_m {Θ Δ : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ) (vB vω : Variable Δ .set)
    (B C W ω Q e t₀ t₁ t₂ a P R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  PowerlessRelativeSourceFamilyExtension.extension_m
    (terminal_m Φ vB vω B C W ω Q e t₀ t₁ t₂ a P τ)
    (PowerlessRelativeFiniteRequestFamilyClosure.family_m
      (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length
      (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ))
    (PowerlessSourceRequestParameters.tags_m Δ
      (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length)
    B W R τ [] (fun v => .fvar v)

def schema_m {Θ Δ : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ) (vB vω : Variable Δ .set)
    (B β C W ω Q G e t₀ t₁ t₂ a S P R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  let m := (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length
  .imp (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_m Θ B (fun v => .fvar v)) <|
    .imp (frame_m B β C W ω Q e t₀ t₁ t₂ a) <|
      .imp (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m W R) <|
        .imp (parameters_m (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) W τ) <|
          .imp (parameters_m (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) C τ) <|
            .imp (PowerlessRelativeSourceSkolemFamily.distinct_m
              (PowerlessSourceRequestParameters.tags_m Δ m) τ) <|
              .imp (PowerlessRelativeFiniteProgramDomain.domain_m B ω Q S P) <|
                .imp (SecondOrderObjectSyntax.map_m G ω C) <|
                  .imp (PowerlessRelativeClassEnumerationSectionDerives.onto_m G ω C) <|
                    .imp (PowerlessRelativeFiniteProgramAlphabet.alphabet_m C ω t₀ t₁ t₂ Q) <|
                      .imp (member_m B C) (conclusion_m Φ vB vω B C W ω Q e t₀ t₁ t₂ a P R τ)

def sentence_m {Θ Δ : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ) (vB vω : Variable Δ .set)
    (B β C W ω Q G e t₀ t₁ t₂ a S P R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m Φ vB vω B β C W ω Q G e t₀ t₁ t₂ a S P R τ)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Θ Δ : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (vB vω : Variable Δ .set)
    (B β C W ω Q G e t₀ t₁ t₂ a S P R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) :
    (sentence_m Φ vB vω B β C W ω Q G e t₀ t₁ t₂ a S P R τ).TrueIn
      (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hClass hFrame hOrder hParamsW hParamsC hDistinct hDomain hMap hOnto hAlphabet hBC
  have hOriginal := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
    (PowerlessRelativeSourceFamilyElementaryImage.models_l hℳ Φ
      B β C W ω Q G e t₀ t₁ t₂ a S P R τ) η
      hClass hFrame hOrder hParamsW hParamsC hDistinct hDomain hMap hOnto hAlphabet hBC
  exact PowerlessRelativeSourceFamilyElementaryImage.transport_l Φ
    B C W ω Q e t₀ t₁ t₂ a P R τ
    (terminal_m Φ vB vω B C W ω Q e t₀ t₁ t₂ a P τ)
    (fun ζ σ J h => terminal_l hℳ K Φ hΦ vB vω B C W ω Q e t₀ t₁ t₂ a P τ σ J ζ h) η hOriginal

theorem derives_m {Θ Δ : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (vB vω : Variable Δ .set)
    (B β C W ω Q G e t₀ t₁ t₂ a S P R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m Φ vB vω B β C W ω Q G e t₀ t₁ t₂ a S P R τ)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ hℳ => models_l hℳ Φ hΦ vB vω B β C W ω Q G e t₀ t₁ t₂ a S P R τ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceFamilyCodedCapture
