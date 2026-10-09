import BMSConstructibleBridge.PowerlessRelativeCutoffCoveredElementaryImage
import BMSConstructibleBridge.PowerlessRelativeStrictCondensation

/-! # 完整参数覆盖与同一实际严格坍缩的联合构造

原 Z₂、纯隶属 ℒ。先消费本轮真正构造的 γ/D/I，再在同一 I 上应用
原严格凝聚；完整低层覆盖、原有限元素性和全部严格坍缩字段一起返回。
来源守卫与实际壳构造完全相同，不预供 I、T、H 或凝聚高度。

原 Φ 的三个基础子族按实际包含关系核验，不能换成较小样本族。
J 严格低于返回的实际首截断；后续与指定 Ω 对接使用原首截断唯一性。
本模块不声称 Collection 已完成，也不将联合存在句当作最终良序闭句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffCoveredCondensation

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev free {Θ : SortContext ℒ} (t : Term ℒ [] Θ .set) :=
  t.weakenFree SetTheory.SetSort.set
private abbrev free₃ {Θ : SortContext ℒ} (t : Term ℒ [] Θ .set) := free (free (free t))

def payload_m {Δ Θ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B ω Ω W X : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] (.set :: .set :: .set :: Θ) :=
  .conj (PowerlessRelativeCutoffCoveredElementaryImage.payload_m Φ B ω Ω W X τ)
    (PowerlessRelativeStrictCondensation.conclusion_m (.fvar .here) (free₃ B) (free₃ W) (free₃ ω))

def conclusion_m {Δ Θ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B ω Ω W X : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  (((payload_m Φ B ω Ω W X τ).existsFreeTop SetTheory.SetSort.set).existsFreeTop
    SetTheory.SetSort.set).existsFreeTop SetTheory.SetSort.set

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

/-- 消去原实际壳的存在块，保留它而不重选另一个 I。 -/
theorem read_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (K : source_coding_l hℳ) {Δ Θ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (hΦ₀ : ∀ p ∈ PowerlessRelativeFiniteHullExtensionality.family_m Δ, p ∈ Φ)
    (hΦ₁ : ∀ p ∈ PowerlessRelativeFiniteHullClosure.family_m Δ, p ∈ Φ)
    (B ω Ω W X : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) (η : Env (SecondOrderQuotient.structure_l hℳ) [] Θ)
    (hSource : (PowerlessRelativeSourceFamilyCodedCapture.source_m B ω W).satisfies η)
    (h : (PowerlessRelativeCutoffCoveredElementaryImage.conclusion_m Φ B ω Ω W X τ).satisfies η) :
    (conclusion_m Φ B ω Ω W X τ).satisfies η := by
  simp only [PowerlessRelativeCutoffCoveredElementaryImage.conclusion_m,
    Formula.satisfies_existsFreeTop] at h
  obtain ⟨γ, D, I, h⟩ := h
  let ξ : Env (SecondOrderQuotient.structure_l hℳ) [] (.set :: .set :: .set :: Θ) :=
    ((η.pushFree γ).pushFree D).pushFree I
  let i : Term ℒ [] (.set :: .set :: .set :: Θ) .set := .fvar .here
  let d : Term ℒ [] (.set :: .set :: .set :: Θ) .set := .fvar (.there .here)
  let ν := PowerlessRelativeSourceFamilyCandidateCondensation.original_m Φ τ
  change (PowerlessRelativeCutoffCoveredElementaryImage.payload_m Φ B ω Ω W X τ).satisfies ξ at h
  have hPayload := h
  simp only [PowerlessRelativeCutoffCoveredElementaryImage.payload_m, Formula.satisfies] at h
  obtain ⟨_hγ, _hD, _hDW, _hXD, hParamsD, hI, hCount, hIW, hDI, _hD, hBI, hB, _hωSub, hωI, hElem⟩ := h
  have hv (t : Term ℒ [] Θ .set) : (free₃ t).eval ξ = t.eval η := by
    simp only [free₃, free, ξ, Term.eval_weakenFree]
  have hSource₀ := (PowerlessRelativeSourceFamilyCodedCapture.source_formula_l hℳ K ξ
    (free₃ B) (free₃ ω) (free₃ W)).mpr (by
      simpa only [hv] using
        (PowerlessRelativeSourceFamilyCodedCapture.source_formula_l hℳ K η B ω W).mp hSource)
  have hParamsI := (parameters_formula_l Δ ξ i
    (fun {s} v => match s with | .set => free₃ (ν v))).mpr (by
      have hD := (parameters_formula_l Δ ξ d
        (fun {s} v => match s with | .set => free₃ (ν v))).mp hParamsD
      have hDI₀ := (subset_formula_l ξ d i).mp hDI
      intro s v
      cases s
      exact hDI₀ _ (hD .set v))
  have hStrict := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
    (PowerlessRelativeStrictCondensation.models_l hℳ Φ hΦ hΦ₀ hΦ₁
      i (free₃ W) (free₃ B) (free₃ ω) (fun v => free₃ (ν v))) ξ
    hSource₀ hIW hParamsI hB hωI hBI hI hCount hElem
  simp only [conclusion_m, Formula.satisfies_existsFreeTop]
  refine ⟨γ, D, I, ?_⟩
  change (payload_m Φ B ω Ω W X τ).satisfies ξ
  exact ⟨hPayload, hStrict⟩

def schema_m {Δ Θ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B ω Ω W G X e t₀ t₁ t₂ a R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  PowerlessRelativeCutoffCoveredElementaryImage.guarded_m Φ B ω Ω W G X e t₀ t₁ t₂ a R τ
    (conclusion_m Φ B ω Ω W X τ)

def sentence_m {Δ Θ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B ω Ω W G X e t₀ t₁ t₂ a R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m Φ B ω Ω W G X e t₀ t₁ t₂ a R τ)

/-- 原实际壳与原严格坍缩都在同一来源守卫下构造，没有新增壳存在前提。 -/
theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ Θ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (hΦ₀ : ∀ p ∈ PowerlessRelativeFiniteHullExtensionality.family_m Δ, p ∈ Φ)
    (hΦ₁ : ∀ p ∈ PowerlessRelativeFiniteHullClosure.family_m Δ, p ∈ Φ)
    (B ω Ω W G X e t₀ t₁ t₂ a R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) :
    (sentence_m Φ B ω Ω W G X e t₀ t₁ t₂ a R τ).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hHull := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
    (PowerlessRelativeCutoffCoveredElementaryImage.models_l hℳ Φ B ω Ω W G X e t₀ t₁ t₂ a R τ)
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hClass hBase hω hΩ hW hBW hωB hG hOnto hX hParams hDistinct h₀ h₁ h₂ he ha ht hR
  have hSource := (PowerlessRelativeSourceFamilyCodedCapture.source_formula_l hℳ K η B ω W).mpr
    ⟨(PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ η B).mp hBase,
      (SecondOrderOmegaSyntax.omega_l hℳ η ω).mp hω, Ω.eval η,
      (PowerlessRelativeOrdinalCutoff.first_formula_l K η B ω Ω).mp hΩ,
      (PowerlessRelativeHierarchySemantics.level_formula_l K η B Ω W).mp hW⟩
  exact read_l hℳ K Φ hΦ hΦ₀ hΦ₁ B ω Ω W X τ η hSource
    (hHull η hClass hBase hω hΩ hW hBW hωB hG hOnto hX hParams hDistinct h₀ h₁ h₂ he ha ht hR)

theorem derives_m {Δ Θ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (hΦ₀ : ∀ p ∈ PowerlessRelativeFiniteHullExtensionality.family_m Δ, p ∈ Φ)
    (hΦ₁ : ∀ p ∈ PowerlessRelativeFiniteHullClosure.family_m Δ, p ∈ Φ)
    (B ω Ω W G X e t₀ t₁ t₂ a R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) : Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m Φ B ω Ω W G X e t₀ t₁ t₂ a R τ)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ hℳ => models_l hℳ Φ hΦ hΦ₀ hΦ₁ B ω Ω W G X e t₀ t₁ t₂ a R τ)

#print axioms read_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffCoveredCondensation
