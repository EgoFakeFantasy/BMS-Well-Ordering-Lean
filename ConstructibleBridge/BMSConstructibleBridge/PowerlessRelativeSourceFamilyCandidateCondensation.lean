import BMSConstructibleBridge.PowerlessRelativeBoundedCondensation
import BMSConstructibleBridge.PowerlessRelativeSourceFamilyElementaryImage

/-! # 原实际请求族上的候选基底凝聚

原逐候选准备的精确基底为 B=ω∪{A}。原参数槽包含 B、ω、A，故
同一实际 I 包含三对象；完整包和操作公式给出 ω⊆I，再取得 B⊆I。
沿原请求族的存在树构造同一 I/T/H/J，不预供 I 或坍缩后目标。
八项原正文、元素性和参数成员性全部保留。首 Ω 与精确候选基底
仍在对象条件中；槽对齐只要求实际项的语法相等，不增加模型公理。
出口为原 Z₂ 的图翻译 Derives。严格高度、Collection 与 hSources
消去尚未完成，不能将本存在模式当作最终固定行数良序闭句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceFamilyCandidateCondensation

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)
open PowerlessRelativeSourceFamilyClosedImage (term_m frame_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev Entry (Ε : SortContext ℒ) := Term ℒ [] Ε .set × Term ℒ [] Ε .set
private abbrev up {Γ Ε : SortContext ℒ} (t : Term ℒ Γ Ε .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev free {Ε : SortContext ℒ} (t : Term ℒ [] Ε .set) :=
  t.weakenFree SetTheory.SetSort.set

/-- 精确基底沿用原单点添加 AST，不另造近似基集规格。 -/
theorem base_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Ε : SortContext ℒ} (ζ : Env 𝒩 Γ Ε) (ω A B : Term ℒ Γ Ε .set) :
    (SecondOrderFunctionAppendDerives.adjoin_m ω A B).satisfies ζ ↔
      ∀ x, member_l 𝒩 x (B.eval ζ) ↔ member_l 𝒩 x (ω.eval ζ) ∨ x = A.eval ζ := by
  simp only [SecondOrderFunctionAppendDerives.adjoin_m, Formula.satisfies,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound, Term.eval]
  rfl

/-- 请求标签前缀之后的原参数项；公开供实际候选装配核对槽对齐。 -/
def original_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) (v : Variable Δ .set) : Term ℒ [] Θ .set :=
  τ (PowerlessSourceOpening.skip_m (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length v)

/-- 同一 I 的原八项正文与元素性保留，凝聚也使用这个绑定槽。 -/
def terminal_m {Θ Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B C W ω A Q e t₀ t₁ t₂ a P : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set)
    (σ : Variable Θ .set → Term ℒ [] Ε .set) (J : List (Entry Ε)) : Formula ℒ [] Ε :=
  let ρ := fun v => term_m (original_m Φ τ v) σ
  .existsE .set <| .conj
    (PowerlessRelativeSourceFamilyElementaryImage.body_m J (term_m B σ) (term_m C σ)
      (term_m W σ) (term_m ω σ) (term_m Q σ) (term_m e σ) (term_m t₀ σ)
      (term_m t₁ σ) (term_m t₂ σ) (term_m a σ) (term_m P σ)) <|
    .conj (PowerlessRelativeSourceFamilyElementaryImage.elementary_m Φ (term_m W σ) ρ) <|
      .conj (parameters_m Δ (.bvar .here) (fun v => up (ρ v))) <|
        .imp (PowerlessRelativeSourceFamilyCodedCapture.source_m
          (up (term_m B σ)) (up (term_m ω σ)) (up (term_m W σ))) <|
          .imp (SecondOrderFunctionAppendDerives.adjoin_m
            (up (term_m ω σ)) (up (term_m A σ)) (up (term_m B σ)))
            (PowerlessRelativeBoundedCondensation.conclusion_m (.bvar .here)
              (up (term_m B σ)) (up (term_m W σ)) (up (term_m ω σ)))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

/-- 从旧实际终端读取同一个 I；不重选源域或目标层。 -/
theorem terminal_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (K : source_coding_l hℳ) {Θ Δ Ε : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (hΦ₀ : ∀ p ∈ PowerlessRelativeFiniteHullExtensionality.family_m Δ, p ∈ Φ)
    (hΦ₁ : ∀ p ∈ PowerlessRelativeFiniteHullClosure.family_m Δ, p ∈ Φ)
    (vB vω vA : Variable Δ .set)
    (B C W ω A Q e t₀ t₁ t₂ a P : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set)
    (hB : original_m Φ τ vB = B) (hω : original_m Φ τ vω = ω) (hA : original_m Φ τ vA = A)
    (σ : Variable Θ .set → Term ℒ [] Ε .set) (J : List (Entry Ε))
    (ζ : Env (SecondOrderQuotient.structure_l hℳ) [] Ε)
    (h : (PowerlessRelativeSourceFamilyElementaryImage.terminal_m Φ
      B C W ω Q e t₀ t₁ t₂ a P τ σ J).satisfies ζ) :
    (terminal_m Φ B C W ω A Q e t₀ t₁ t₂ a P τ σ J).satisfies ζ := by
  let ρ := fun v => term_m (original_m Φ τ v) σ
  let b := term_m B σ
  let w := term_m W σ
  let o := term_m ω σ
  let d := term_m A σ
  obtain ⟨I, hBody, hElem, hParams⟩ :=
    (PowerlessRelativeSourceFamilyElementaryImage.terminal_formula_l Φ
      B C W ω Q e t₀ t₁ t₂ a P τ σ J ζ).mp h
  have hb : mem_l hℳ (b.eval ζ) I := by
    have h := hParams vB
    change mem_l hℳ ((term_m (original_m Φ τ vB) σ).eval ζ) I at h
    simpa only [hB] using h
  have ho : mem_l hℳ (o.eval ζ) I := by
    have h := hParams vω
    change mem_l hℳ ((term_m (original_m Φ τ vω) σ).eval ζ) I at h
    simpa only [hω] using h
  have hd : mem_l hℳ (d.eval ζ) I := by
    have h := hParams vA
    change mem_l hℳ ((term_m (original_m Φ τ vA) σ).eval ζ) I at h
    simpa only [hA] using h
  have hParameters : (parameters_m Δ (.bvar .here) (fun v => up (ρ v))).satisfies
      (ζ.pushBound (sort := SetTheory.SetSort.set) I) := by
    apply (parameters_formula_l Δ _ _ _).mpr
    intro s v
    cases s
    simpa only [up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here,
      ρ, original_m, member_l] using hParams v
  refine ⟨I, hBody,
    (PowerlessRelativeSourceFamilyElementaryImage.elementary_formula_l Φ w ρ ζ I).mpr hElem,
    hParameters, ?_⟩
  intro hSource hBase
  let ξ := ζ.pushFree I
  let i : Term ℒ [] (.set :: Ε) .set := .fvar .here
  have hv (t : Term ℒ [] Ε .set) : (free t).eval ξ = t.eval ζ := by
    simp only [free, ξ, Term.eval_weakenFree]
  have hSource' : (PowerlessRelativeSourceFamilyCodedCapture.source_m
      (free b) (free o) (free w)).satisfies ξ := by
    apply (PowerlessRelativeSourceFamilyCodedCapture.source_formula_l hℳ K ξ _ _ _).mpr
    simpa only [hv, up, Term.eval_weakenBound] using
      (PowerlessRelativeSourceFamilyCodedCapture.source_formula_l hℳ K
        (ζ.pushBound (sort := SetTheory.SetSort.set) I) (up b) (up o) (up w)).mp hSource
  have hBase' : (SecondOrderFunctionAppendDerives.adjoin_m (free o) (free d) (free b)).satisfies ξ := by
    apply (base_formula_l ξ _ _ _).mpr
    simpa only [hv, up, Term.eval_weakenBound] using
      (base_formula_l (ζ.pushBound (sort := SetTheory.SetSort.set) I) (up o) (up d) (up b)).mp hBase
  have hIW : subset_l (ℳ := SecondOrderQuotient.structure_l hℳ) (i.eval ξ) ((free w).eval ξ) := by
    simpa only [i, ξ, hv, up, Term.eval_weakenBound, Term.eval,
      Env.pushFree_here, Env.pushBound_bound_here] using
      (subset_formula_l (ζ.pushBound (sort := SetTheory.SetSort.set) I)
        (.bvar .here) (up w)).mp hBody.2.2.1
  have hParameters' : (parameters_m Δ i (fun v => free (ρ v))).satisfies ξ := by
    apply (parameters_formula_l Δ ξ i _).mpr
    intro s v
    cases s
    simpa only [hv, i, ξ, Term.eval, Env.pushFree_here, ρ, original_m, member_l] using hParams v
  have hb' : mem_l hℳ ((free b).eval ξ) (i.eval ξ) := by
    simpa only [hv, i, ξ, Term.eval, Env.pushFree_here] using hb
  have ho' : mem_l hℳ ((free o).eval ξ) (i.eval ξ) := by
    simpa only [hv, i, ξ, Term.eval, Env.pushFree_here] using ho
  have hd' : mem_l hℳ ((free d).eval ξ) (i.eval ξ) := by
    simpa only [hv, i, ξ, Term.eval, Env.pushFree_here] using hd
  obtain ⟨_, hωSub⟩ := PowerlessRelativeFiniteHullOmegaCoverage.target_l K Φ hΦ hΦ₁
    ξ i (free w) (free b) (free o) (fun v => free (ρ v)) hSource' hIW hParameters' hb' ho' hElem
  have hBI : subset_l (ℳ := SecondOrderQuotient.structure_l hℳ) ((free b).eval ξ) (i.eval ξ) := by
    intro x hx
    rcases ((base_formula_l ξ (free o) (free d) (free b)).mp hBase' x).mp hx with hx | hx
    · exact hωSub x hx
    · exact hx.symm ▸ hd'
  have hClass' : (PowerlessRelativeHierarchySyntax.class_m (free b) i).satisfies ξ := by
    apply (PowerlessRelativeHierarchySemantics.class_formula_l K ξ _ _).mpr
    simpa only [hv, i, ξ, up, Term.eval_weakenBound, Term.eval,
      Env.pushFree_here, Env.pushBound_bound_here] using
      (PowerlessRelativeHierarchySemantics.class_formula_l K
        (ζ.pushBound (sort := SetTheory.SetSort.set) I) (up b) (.bvar .here)).mp hBody.1
  have hCount' : (PowerlessRelativeOrdinalCutoff.countable_m (free b) (free o) i).satisfies ξ := by
    apply (PowerlessRelativeOrdinalCutoff.countable_formula_l K ξ _ _ _).mpr
    simpa only [hv, i, ξ, up, Term.eval_weakenBound, Term.eval,
      Env.pushFree_here, Env.pushBound_bound_here] using
      (PowerlessRelativeOrdinalCutoff.countable_formula_l K
        (ζ.pushBound (sort := SetTheory.SetSort.set) I) (up b) (up o) (.bvar .here)).mp hBody.2.1
  have hResult := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
    (PowerlessRelativeBoundedCondensation.models_l hℳ Φ hΦ hΦ₀ hΦ₁
      i (free w) (free b) (free o) (fun v => free (ρ v))) ξ hSource'
      ((subset_formula_l ξ i (free w)).mpr hIW) hParameters' hb' ho'
      ((subset_formula_l ξ (free b) i).mpr hBI) hClass' hCount' hElem
  apply (PowerlessRelativeBoundedCondensation.conclusion_formula_l K
    (ζ.pushBound (sort := SetTheory.SetSort.set) I) (.bvar .here) (up b) (up w) (up o)).mpr
  simpa only [hv, i, ξ, up, Term.eval_weakenBound, Term.eval,
    Env.pushFree_here, Env.pushBound_bound_here] using
    (PowerlessRelativeBoundedCondensation.conclusion_formula_l K ξ i (free b) (free w) (free o)).mp hResult

def conclusion_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B C W ω A Q e t₀ t₁ t₂ a P R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  PowerlessRelativeSourceFamilyExtension.extension_m
    (terminal_m Φ B C W ω A Q e t₀ t₁ t₂ a P τ)
    (PowerlessRelativeFiniteRequestFamilyClosure.family_m
      (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length
      (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ))
    (PowerlessSourceRequestParameters.tags_m Δ
      (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length)
    B W R τ [] (fun v => .fvar v)

def schema_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B β C W ω A Q G e t₀ t₁ t₂ a S P R : Term ℒ [] Θ .set)
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
                      .imp (SecondOrderObjectSyntax.member_m B C)
                        (conclusion_m Φ B C W ω A Q e t₀ t₁ t₂ a P R τ)

def sentence_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B β C W ω A Q G e t₀ t₁ t₂ a S P R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m Φ B β C W ω A Q G e t₀ t₁ t₂ a S P R τ)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Θ Δ : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (hΦ₀ : ∀ p ∈ PowerlessRelativeFiniteHullExtensionality.family_m Δ, p ∈ Φ)
    (hΦ₁ : ∀ p ∈ PowerlessRelativeFiniteHullClosure.family_m Δ, p ∈ Φ)
    (vB vω vA : Variable Δ .set)
    (B β C W ω A Q G e t₀ t₁ t₂ a S P R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set)
    (hB : original_m Φ τ vB = B) (hω : original_m Φ τ vω = ω) (hA : original_m Φ τ vA = A) :
    (sentence_m Φ B β C W ω A Q G e t₀ t₁ t₂ a S P R τ).TrueIn
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
    (terminal_m Φ B C W ω A Q e t₀ t₁ t₂ a P τ)
    (fun ζ σ J h => terminal_l hℳ K Φ hΦ hΦ₀ hΦ₁ vB vω vA
      B C W ω A Q e t₀ t₁ t₂ a P τ hB hω hA σ J ζ h) η hOriginal

theorem derives_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (hΦ₀ : ∀ p ∈ PowerlessRelativeFiniteHullExtensionality.family_m Δ, p ∈ Φ)
    (hΦ₁ : ∀ p ∈ PowerlessRelativeFiniteHullClosure.family_m Δ, p ∈ Φ)
    (vB vω vA : Variable Δ .set)
    (B β C W ω A Q G e t₀ t₁ t₂ a S P R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set)
    (hB : original_m Φ τ vB = B) (hω : original_m Φ τ vω = ω) (hA : original_m Φ τ vA = A) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m Φ B β C W ω A Q G e t₀ t₁ t₂ a S P R τ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ Φ hΦ hΦ₀ hΦ₁ vB vω vA
    B β C W ω A Q G e t₀ t₁ t₂ a S P R τ hB hω hA)

#print axioms base_formula_l
#print axioms terminal_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceFamilyCandidateCondensation
