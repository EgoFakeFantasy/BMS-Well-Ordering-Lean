import BMSConstructibleBridge.PowerlessRelativeSourceFamilyHistory
import BMSConstructibleBridge.PowerlessRelativeCutoffFiniteElementaryImage

/-! # 实际截断构造中的同见证历史捕获

对象语言为纯隶属 ℒ，背景为原 Z₂，正式出口为原 Derives 的图翻译句。
原 B/D/A/U 和 Δ 参数先作为指定种子参数；历史 f 仅是装配项，不入种子。
沿有限标签、R/e/a、C/G/Q/S/P 和原图族的全部存在量词保留同一见证，
只加强最内层同一个 I 的正文。标签、排序图、种子和 I 均由旧截断
构造实际提供，不是额外前提。原接口保留历史条件蕴含；capture 接口
消费已成立的守卫后，在同一完整末端直接保留 f∈I。

本模块不假定首 Class 不可数截断必然存在，也不声称已经证明 Def
截迹、弱凝聚、完整源公理或最终固定高度 BMS 良序句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffHistoryImage

open Logic FirstOrder
open PowerlessRelativeSourceFamilyHistory (family_m)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
-- 本层只调用已证历史族接口，不在参数统一时重新计算整棵请求树。
attribute [local irreducible] PowerlessRelativeSourceFamilyHistory.family_m

universe u

private abbrev free {Θ : SortContext ℒ} (t : Term ℒ [] Θ .set) :=
  t.weakenFree SetTheory.SetSort.set
private abbrev free₃ {Θ : SortContext ℒ} (t : Term ℒ [] Θ .set) := free (free (free t))
private abbrev free₅ {Θ : SortContext ℒ} (t : Term ℒ [] Θ .set) := free (free (free₃ t))
private abbrev seedContext_m (Θ : SortContext ℒ) := .set :: .set :: .set :: .set :: .set :: Θ
private abbrev cutoffContext_m (Θ : SortContext ℒ) := .set :: .set :: .set :: Θ

private theorem free_eval_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Θ : SortContext ℒ} (η : Env 𝒩 [] Θ) (t : Term ℒ [] Θ .set)
    (C G Q S P : ThirdOrderSemantics.carrier_l 𝒩) :
    (free₅ t).eval (((((η.pushFree C).pushFree G).pushFree Q).pushFree S).pushFree P) =
      t.eval η := by
  simp only [free₅, free₃, free, Term.eval_weakenFree]

private def seedPayload_m {Θ Δ : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B W ω t₀ t₁ t₂ : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) (χ : Formula ℒ [] (seedContext_m Θ)) : Formula ℒ [] (seedContext_m Θ) :=
  let C : Term ℒ [] (seedContext_m Θ) .set := .fvar (.there (.there (.there (.there .here))))
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
            .conj (PowerlessRelativeFiniteProgramDomain.domain_m (free₅ B) (free₅ ω) Q S P) χ

private def seed_m {Θ Δ : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B W ω t₀ t₁ t₂ : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) (χ : Formula ℒ [] (seedContext_m Θ)) : Formula ℒ [] Θ :=
  let φ₀ := seedPayload_m Φ B W ω t₀ t₁ t₂ τ χ
  let φ₁ := φ₀.existsFreeTop SetTheory.SetSort.set
  let φ₂ := φ₁.existsFreeTop SetTheory.SetSort.set
  let φ₃ := φ₂.existsFreeTop SetTheory.SetSort.set
  let φ₄ := φ₃.existsFreeTop SetTheory.SetSort.set
  φ₄.existsFreeTop SetTheory.SetSort.set

private def historySeed_m (b : Bool) {Θ Δ : SortContext ℒ}
    (B W ω e t₀ t₁ t₂ a R f : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m (family_m Δ)) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  let C : Term ℒ [] (seedContext_m Θ) .set := .fvar (.there (.there (.there (.there .here))))
  let Q := .fvar (.there (.there .here))
  let P := .fvar .here
  if b then seed_m (family_m Δ) B W ω t₀ t₁ t₂ τ
    (PowerlessRelativeSourceFamilyHistory.captured_conclusion_m (Δ := Δ)
      (free₅ B) C (free₅ W) (free₅ ω) Q (free₅ e) (free₅ t₀) (free₅ t₁)
      (free₅ t₂) (free₅ a) P (free₅ R) (free₅ f) (fun v => free₅ (τ v)))
  else seed_m (family_m Δ) B W ω t₀ t₁ t₂ τ
    (PowerlessRelativeSourceFamilyHistory.conclusion_m (Δ := Δ)
      (free₅ B) C (free₅ W) (free₅ ω) Q (free₅ e) (free₅ t₀) (free₅ t₁)
      (free₅ t₂) (free₅ a) P (free₅ R) (free₅ f) (fun v => free₅ (τ v)))

private def cutoffPayload_m (b : Bool) {Θ Δ : SortContext ℒ}
    (B W ω t₀ t₁ t₂ f : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m (family_m Δ)) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] (cutoffContext_m Θ) :=
  let R : Term ℒ [] (cutoffContext_m Θ) .set := .fvar (.there (.there .here))
  let e := .fvar (.there .here)
  let a := .fvar .here
  .conj (PowerlessRelativeHierarchySyntax.class_m (free₃ B) R) <|
    .conj (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m (free₃ W) R) <|
      .conj (PowerlessRelativeFiniteProgramInitialFrame.initial_m (free₃ B) (free₃ W) e a)
        (historySeed_m b (Δ := Δ) (free₃ B) (free₃ W) (free₃ ω) e
          (free₃ t₀) (free₃ t₁) (free₃ t₂) a R (free₃ f) (fun v => free₃ (τ v)))

private def cutoff_m (b : Bool) {Θ Δ : SortContext ℒ}
    (B W ω t₀ t₁ t₂ f : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m (family_m Δ)) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  let φ₀ := cutoffPayload_m b (Δ := Δ) B W ω t₀ t₁ t₂ f τ
  let φ₁ := φ₀.existsFreeTop SetTheory.SetSort.set
  let φ₂ := φ₁.existsFreeTop SetTheory.SetSort.set
  φ₂.existsFreeTop SetTheory.SetSort.set

private def payload_m (b : Bool) {Θ Δ : SortContext ℒ} (B W ω t₀ t₁ t₂ f : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyHistory.context_m Δ) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] (PowerlessRelativeCutoffFiniteElementaryImage.context_m
        (family_m Δ) Θ) :=
  let m := (PowerlessRelativeFiniteRequestFamilyClosure.requests_m (family_m Δ)).length
  cutoff_m b (Δ := Δ) (PowerlessRelativeCutoffFiniteElementaryImage.term_m m B)
    (PowerlessRelativeCutoffFiniteElementaryImage.term_m m W)
    (PowerlessRelativeCutoffFiniteElementaryImage.term_m m ω)
    (PowerlessRelativeCutoffFiniteElementaryImage.term_m m t₀)
    (PowerlessRelativeCutoffFiniteElementaryImage.term_m m t₁)
    (PowerlessRelativeCutoffFiniteElementaryImage.term_m m t₂)
    (PowerlessRelativeCutoffFiniteElementaryImage.term_m m f)
    (PowerlessRelativeCutoffFiniteElementaryImage.binding_m m τ)

/-- 保留原全部量词块与图规格，只增加同一闭包像的历史捕获字段。 -/
def conclusion_m {Θ Δ : SortContext ℒ} (B W ω t₀ t₁ t₂ f : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyHistory.context_m Δ) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  PowerlessRelativeFiniteNumeralTags.exists_m
    (PowerlessRelativeFiniteRequestFamilyClosure.requests_m (family_m Δ)).length
    (payload_m false (Δ := Δ) B W ω t₀ t₁ t₂ f τ)

/-- 同一完整截断构造，其最内层正文明确含 f∈I。 -/
def captured_conclusion_m {Θ Δ : SortContext ℒ} (B W ω t₀ t₁ t₂ f : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyHistory.context_m Δ) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  PowerlessRelativeFiniteNumeralTags.exists_m
    (PowerlessRelativeFiniteRequestFamilyClosure.requests_m (family_m Δ)).length
    (payload_m true (Δ := Δ) B W ω t₀ t₁ t₂ f τ)

def input_m {Θ Δ : SortContext ℒ} (W f : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyHistory.context_m Δ) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  PowerlessRelativeSourceFamilyHistory.guard_m (τ .here) (τ (.there .here))
    (τ (.there (.there .here))) (τ (.there (.there (.there .here)))) W f

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

private theorem seed_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B W ω e t₀ t₁ t₂ a R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) (χ : Formula ℒ [] (seedContext_m Θ))
    (hχ : ∀ ζ : Env 𝒩 [] (seedContext_m Θ),
      (PowerlessRelativeSourceFamilyElementaryImage.conclusion_m Φ
        (free₅ B) (.fvar (.there (.there (.there (.there .here))))) (free₅ W) (free₅ ω)
        (.fvar (.there (.there .here))) (free₅ e) (free₅ t₀) (free₅ t₁) (free₅ t₂)
        (free₅ a) (.fvar .here) (free₅ R) (fun v => free₅ (τ v))).satisfies ζ → χ.satisfies ζ)
    (η : Env 𝒩 [] Θ)
    (h : (PowerlessRelativeSeedFamilyElementaryImage.conclusion_m Φ
      B W ω e t₀ t₁ t₂ a R τ).satisfies η) :
    (seed_m Φ B W ω t₀ t₁ t₂ τ χ).satisfies η := by
  simp only [PowerlessRelativeSeedFamilyElementaryImage.conclusion_m,
    seed_m, Formula.satisfies_existsFreeTop] at h ⊢
  obtain ⟨C, G, Q, S, P, h⟩ := h
  refine ⟨C, G, Q, S, P, ?_⟩
  let ζ := ((((η.pushFree C).pushFree G).pushFree Q).pushFree S).pushFree P
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at h ⊢
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, ?_⟩
  exact hχ ζ h.2.2.2.2.2.2

/-- 抽象正文上的同见证运输，避免内核在五层存在块重复归约具体请求树。 -/
private theorem seed_imp_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B W ω t₀ t₁ t₂ : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) (φ ψ : Formula ℒ [] (seedContext_m Θ))
    (η : Env 𝒩 [] Θ)
    (hφψ : ∀ C G Q S P,
      φ.satisfies (((((η.pushFree C).pushFree G).pushFree Q).pushFree S).pushFree P) →
        ψ.satisfies (((((η.pushFree C).pushFree G).pushFree Q).pushFree S).pushFree P))
    (h : (seed_m Φ B W ω t₀ t₁ t₂ τ φ).satisfies η) :
    (seed_m Φ B W ω t₀ t₁ t₂ τ ψ).satisfies η := by
  simp only [seed_m, Formula.satisfies_existsFreeTop] at h ⊢
  obtain ⟨C, G, Q, S, P, h⟩ := h
  refine ⟨C, G, Q, S, P, ?_⟩
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at h ⊢
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2.1, hφψ C G Q S P h.2.2.2.2.2.2⟩

private theorem historySeed_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Θ Δ : SortContext ℒ} (B W ω e t₀ t₁ t₂ a R f : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m (family_m Δ)) .set →
      Term ℒ [] Θ .set) (η : Env (SecondOrderQuotient.structure_l hℳ) [] Θ)
    (h : (PowerlessRelativeSeedFamilyElementaryImage.conclusion_m (family_m Δ)
      B W ω e t₀ t₁ t₂ a R τ).satisfies η) :
    (historySeed_m false (Δ := Δ) B W ω e t₀ t₁ t₂ a R f τ).satisfies η := by
  apply seed_l (family_m Δ) B W ω e t₀ t₁ t₂ a R τ _ (fun ζ => ?_) η h
  let C' : Term ℒ [] (seedContext_m Θ) .set := .fvar (.there (.there (.there (.there .here))))
  let Q' : Term ℒ [] (seedContext_m Θ) .set := .fvar (.there (.there .here))
  let P' : Term ℒ [] (seedContext_m Θ) .set := .fvar .here
  have h' := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
    (PowerlessRelativeSourceFamilyHistory.models_l hℳ (Δ := Δ)
      (free₅ B) C' (free₅ W) (free₅ ω) Q' (free₅ e) (free₅ t₀) (free₅ t₁)
      (free₅ t₂) (free₅ a) P' (free₅ R) (free₅ f) (fun v => free₅ (τ v))) ζ
  exact h'

private theorem cutoff_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Θ Δ : SortContext ℒ} (B W ω t₀ t₁ t₂ f : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m (family_m Δ)) .set →
      Term ℒ [] Θ .set) (η : Env (SecondOrderQuotient.structure_l hℳ) [] Θ)
    (h : (PowerlessRelativeCutoffSeedFamilyElementaryImage.conclusion_m (family_m Δ)
      B W ω t₀ t₁ t₂ τ).satisfies η) :
    (cutoff_m false (Δ := Δ) B W ω t₀ t₁ t₂ f τ).satisfies η := by
  simp only [PowerlessRelativeCutoffSeedFamilyElementaryImage.conclusion_m,
    cutoff_m, Formula.satisfies_existsFreeTop] at h ⊢
  obtain ⟨R, e, a, h⟩ := h
  refine ⟨R, e, a, ?_⟩
  let ζ := ((η.pushFree R).pushFree e).pushFree a
  let R' : Term ℒ [] (cutoffContext_m Θ) .set := .fvar (.there (.there .here))
  let e' : Term ℒ [] (cutoffContext_m Θ) .set := .fvar (.there .here)
  let a' : Term ℒ [] (cutoffContext_m Θ) .set := .fvar .here
  change _ ∧ _ ∧ _ ∧ _ at h ⊢
  exact ⟨h.1, h.2.1, h.2.2.1, historySeed_l hℳ (Δ := Δ) (free₃ B) (free₃ W) (free₃ ω)
    e' (free₃ t₀) (free₃ t₁) (free₃ t₂) a' R' (free₃ f) (fun v => free₃ (τ v)) ζ h.2.2.2⟩

private theorem exists_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Θ : SortContext ℒ}
    (m : Nat) (φ ψ : Formula ℒ [] (List.replicate m .set ++ Θ))
    (h : ∀ ζ : Env 𝒩 [] (List.replicate m .set ++ Θ), φ.satisfies ζ → ψ.satisfies ζ)
    (η : Env 𝒩 [] Θ) (hφ : (PowerlessRelativeFiniteNumeralTags.exists_m m φ).satisfies η) :
    (PowerlessRelativeFiniteNumeralTags.exists_m m ψ).satisfies η := by
  obtain ⟨v, hv⟩ := (PowerlessRelativeFiniteNumeralTags.exists_formula_l m φ η).mp hφ
  exact (PowerlessRelativeFiniteNumeralTags.exists_formula_l m ψ η).mpr
    ⟨v, h (PowerlessSourceTuple.env_l η m v) hv⟩

theorem imp_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Θ Δ : SortContext ℒ} (B W ω t₀ t₁ t₂ f : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyHistory.context_m Δ) .set →
      Term ℒ [] Θ .set) (η : Env (SecondOrderQuotient.structure_l hℳ) [] Θ)
    (h : (PowerlessRelativeCutoffFiniteElementaryImage.conclusion_m (family_m Δ)
      B W ω t₀ t₁ t₂ τ).satisfies η) :
    (conclusion_m (Δ := Δ) B W ω t₀ t₁ t₂ f τ).satisfies η := by
  let m := (PowerlessRelativeFiniteRequestFamilyClosure.requests_m (family_m Δ)).length
  exact exists_l (𝒩 := SecondOrderQuotient.structure_l hℳ) (Θ := Θ) m
    (PowerlessRelativeCutoffFiniteElementaryImage.payload_m (family_m Δ) B W ω t₀ t₁ t₂ τ)
    (payload_m false (Δ := Δ) B W ω t₀ t₁ t₂ f τ)
    (fun ζ h => cutoff_l hℳ (Δ := Δ)
      (PowerlessRelativeCutoffFiniteElementaryImage.term_m m B)
      (PowerlessRelativeCutoffFiniteElementaryImage.term_m m W)
      (PowerlessRelativeCutoffFiniteElementaryImage.term_m m ω)
      (PowerlessRelativeCutoffFiniteElementaryImage.term_m m t₀)
      (PowerlessRelativeCutoffFiniteElementaryImage.term_m m t₁)
      (PowerlessRelativeCutoffFiniteElementaryImage.term_m m t₂)
      (PowerlessRelativeCutoffFiniteElementaryImage.term_m m f)
      (PowerlessRelativeCutoffFiniteElementaryImage.binding_m m τ) ζ h) η h

private theorem capture_body_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (K : PowerlessBMSQuotientCoding.source_coding_l hℳ) {Θ Δ : SortContext ℒ}
    (B W ω e t₀ t₁ t₂ a R f : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m (family_m Δ)) .set →
      Term ℒ [] Θ .set) (η : Env (SecondOrderQuotient.structure_l hℳ) [] Θ)
    (C G Q S P : ThirdOrderSemantics.carrier_l (SecondOrderQuotient.structure_l hℳ))
    (hGuard : (PowerlessRelativeSourceFamilyHistory.input_m (Δ := Δ) W f τ).satisfies η)
    (h : (PowerlessRelativeSourceFamilyHistory.conclusion_m (Δ := Δ)
      (free₅ B) (.fvar (.there (.there (.there (.there .here))))) (free₅ W) (free₅ ω)
      (.fvar (.there (.there .here))) (free₅ e) (free₅ t₀) (free₅ t₁) (free₅ t₂)
      (free₅ a) (.fvar .here) (free₅ R) (free₅ f) (fun v => free₅ (τ v))).satisfies
        (((((η.pushFree C).pushFree G).pushFree Q).pushFree S).pushFree P)) :
    (PowerlessRelativeSourceFamilyHistory.captured_conclusion_m (Δ := Δ)
      (free₅ B) (.fvar (.there (.there (.there (.there .here))))) (free₅ W) (free₅ ω)
      (.fvar (.there (.there .here))) (free₅ e) (free₅ t₀) (free₅ t₁) (free₅ t₂)
      (free₅ a) (.fvar .here) (free₅ R) (free₅ f) (fun v => free₅ (τ v))).satisfies
        (((((η.pushFree C).pushFree G).pushFree Q).pushFree S).pushFree P) := by
  let ζ := ((((η.pushFree C).pushFree G).pushFree Q).pushFree S).pushFree P
  apply PowerlessRelativeSourceFamilyHistory.capture_l hℳ (Δ := Δ)
    (free₅ B) (.fvar (.there (.there (.there (.there .here))))) (free₅ W) (free₅ ω)
    (.fvar (.there (.there .here))) (free₅ e) (free₅ t₀) (free₅ t₁) (free₅ t₂)
    (free₅ a) (.fvar .here) (free₅ R) (free₅ f) (fun v => free₅ (τ v)) ζ ?_ h
  exact (PowerlessRelativeSourceFamilyHistory.input_eval_l K η ζ W f (free₅ W) (free₅ f)
    τ (fun v => free₅ (τ v)) (free_eval_l η W C G Q S P) (free_eval_l η f C G Q S P)
    (fun v => free_eval_l η (τ v) C G Q S P)).mpr hGuard

private theorem capture_seed_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (K : PowerlessBMSQuotientCoding.source_coding_l hℳ) {Θ Δ : SortContext ℒ}
    (B W ω e t₀ t₁ t₂ a R f : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m (family_m Δ)) .set →
      Term ℒ [] Θ .set) (η : Env (SecondOrderQuotient.structure_l hℳ) [] Θ)
    (hGuard : (PowerlessRelativeSourceFamilyHistory.input_m (Δ := Δ) W f τ).satisfies η)
    (h : (historySeed_m false (Δ := Δ) B W ω e t₀ t₁ t₂ a R f τ).satisfies η) :
    (historySeed_m true (Δ := Δ) B W ω e t₀ t₁ t₂ a R f τ).satisfies η := by
  let C' : Term ℒ [] (seedContext_m Θ) .set := .fvar (.there (.there (.there (.there .here))))
  let Q' : Term ℒ [] (seedContext_m Θ) .set := .fvar (.there (.there .here))
  let P' : Term ℒ [] (seedContext_m Θ) .set := .fvar .here
  apply seed_imp_l (family_m Δ) B W ω t₀ t₁ t₂ τ
    (PowerlessRelativeSourceFamilyHistory.conclusion_m (Δ := Δ)
      (free₅ B) C' (free₅ W) (free₅ ω) Q' (free₅ e) (free₅ t₀) (free₅ t₁) (free₅ t₂)
      (free₅ a) P' (free₅ R) (free₅ f) (fun v => free₅ (τ v)))
    (PowerlessRelativeSourceFamilyHistory.captured_conclusion_m (Δ := Δ)
      (free₅ B) C' (free₅ W) (free₅ ω) Q' (free₅ e) (free₅ t₀) (free₅ t₁) (free₅ t₂)
      (free₅ a) P' (free₅ R) (free₅ f) (fun v => free₅ (τ v)))
    η (fun C G Q S P h => ?_) h
  exact capture_body_l hℳ K (Δ := Δ) B W ω e t₀ t₁ t₂ a R f τ η C G Q S P hGuard h

private theorem capture_cutoff_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (K : PowerlessBMSQuotientCoding.source_coding_l hℳ) {Θ Δ : SortContext ℒ}
    (B W ω t₀ t₁ t₂ f : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m (family_m Δ)) .set →
      Term ℒ [] Θ .set) (η : Env (SecondOrderQuotient.structure_l hℳ) [] Θ)
    (hGuard : (PowerlessRelativeSourceFamilyHistory.input_m (Δ := Δ) W f τ).satisfies η)
    (h : (cutoff_m false (Δ := Δ) B W ω t₀ t₁ t₂ f τ).satisfies η) :
    (cutoff_m true (Δ := Δ) B W ω t₀ t₁ t₂ f τ).satisfies η := by
  simp only [cutoff_m, Formula.satisfies_existsFreeTop] at h ⊢
  obtain ⟨R, e, a, h⟩ := h
  refine ⟨R, e, a, ?_⟩
  let ζ := ((η.pushFree R).pushFree e).pushFree a
  let R' : Term ℒ [] (cutoffContext_m Θ) .set := .fvar (.there (.there .here))
  let e' : Term ℒ [] (cutoffContext_m Θ) .set := .fvar (.there .here)
  let a' : Term ℒ [] (cutoffContext_m Θ) .set := .fvar .here
  change _ ∧ _ ∧ _ ∧ _ at h ⊢
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  apply capture_seed_l hℳ K (Δ := Δ) (free₃ B) (free₃ W) (free₃ ω) e'
    (free₃ t₀) (free₃ t₁) (free₃ t₂) a' R' (free₃ f) (fun v => free₃ (τ v)) ζ ?_ h.2.2.2
  simpa only [free₃, free, PowerlessRelativeSourceFamilyHistory.input_free_l K, ζ] using hGuard

/-- 消去已成立的原历史守卫，保持同一标签、排序图、种子和完整原图族。 -/
theorem capture_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Θ Δ : SortContext ℒ} (B W ω t₀ t₁ t₂ f : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyHistory.context_m Δ) .set →
      Term ℒ [] Θ .set) (η : Env (SecondOrderQuotient.structure_l hℳ) [] Θ)
    (hGuard : (input_m (Δ := Δ) W f τ).satisfies η)
    (h : (conclusion_m (Δ := Δ) B W ω t₀ t₁ t₂ f τ).satisfies η) :
    (captured_conclusion_m (Δ := Δ) B W ω t₀ t₁ t₂ f τ).satisfies η := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  let m := (PowerlessRelativeFiniteRequestFamilyClosure.requests_m (family_m Δ)).length
  obtain ⟨v, hv⟩ := (PowerlessRelativeFiniteNumeralTags.exists_formula_l m
    (payload_m false (Δ := Δ) B W ω t₀ t₁ t₂ f τ) η).mp h
  apply (PowerlessRelativeFiniteNumeralTags.exists_formula_l m
    (payload_m true (Δ := Δ) B W ω t₀ t₁ t₂ f τ) η).mpr
  refine ⟨v, ?_⟩
  let ζ := PowerlessSourceTuple.env_l η m v
  let ν : Env (SecondOrderQuotient.structure_l hℳ) [] (PowerlessRelativeSourceFamilyHistory.context_m Δ) :=
    { boundVal := fun w => nomatch w
      freeVal := fun {s} w => match s with | .set => (τ w).eval η }
  have hTerm (t : Term ℒ [] Θ .set) :
      (PowerlessRelativeCutoffFiniteElementaryImage.term_m m t).eval ζ = t.eval η :=
    PowerlessSourceRequestParameters.term_l η 0 m .nil v t
  have hτ (w : Variable (PowerlessRelativeSourceFamilyHistory.context_m Δ) .set) :
      (PowerlessRelativeCutoffFiniteElementaryImage.binding_m m τ
        (PowerlessSourceOpening.skip_m m w)).eval ζ = (τ w).eval η := by
    exact (PowerlessRelativeCutoffFiniteElementaryImage.binding_l η ν m v τ
      (fun _ => rfl) (PowerlessSourceOpening.skip_m m w)).trans
      (PowerlessSourceOpening.skip_l ν m v w)
  apply capture_cutoff_l hℳ K (Δ := Δ)
    (PowerlessRelativeCutoffFiniteElementaryImage.term_m m B)
    (PowerlessRelativeCutoffFiniteElementaryImage.term_m m W)
    (PowerlessRelativeCutoffFiniteElementaryImage.term_m m ω)
    (PowerlessRelativeCutoffFiniteElementaryImage.term_m m t₀)
    (PowerlessRelativeCutoffFiniteElementaryImage.term_m m t₁)
    (PowerlessRelativeCutoffFiniteElementaryImage.term_m m t₂)
    (PowerlessRelativeCutoffFiniteElementaryImage.term_m m f)
    (PowerlessRelativeCutoffFiniteElementaryImage.binding_m m τ) ζ ?_ hv
  rw [PowerlessRelativeSourceFamilyHistory.input_eq_m]
  apply (PowerlessRelativeSourceFamilyHistory.guard_formula_l K ζ
    (PowerlessRelativeCutoffFiniteElementaryImage.binding_m m τ (PowerlessSourceOpening.skip_m m .here))
    (PowerlessRelativeCutoffFiniteElementaryImage.binding_m m τ (PowerlessSourceOpening.skip_m m (.there .here)))
    (PowerlessRelativeCutoffFiniteElementaryImage.binding_m m τ
      (PowerlessSourceOpening.skip_m m (.there (.there .here))))
    (PowerlessRelativeCutoffFiniteElementaryImage.binding_m m τ
      (PowerlessSourceOpening.skip_m m (.there (.there (.there .here)))))
    (PowerlessRelativeCutoffFiniteElementaryImage.term_m m W)
    (PowerlessRelativeCutoffFiniteElementaryImage.term_m m f)).mpr
  simpa only [hTerm, hτ] using
    (PowerlessRelativeSourceFamilyHistory.guard_formula_l K η (τ .here) (τ (.there .here))
      (τ (.there (.there .here))) (τ (.there (.there (.there .here)))) W f).mp hGuard

def capture_schema_m {Θ Δ : SortContext ℒ} (B W ω t₀ t₁ t₂ f : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyHistory.context_m Δ) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  .imp (input_m (Δ := Δ) W f τ) <|
    .imp (conclusion_m (Δ := Δ) B W ω t₀ t₁ t₂ f τ)
      (captured_conclusion_m (Δ := Δ) B W ω t₀ t₁ t₂ f τ)

theorem capture_derives_m {Θ Δ : SortContext ℒ} (B W ω t₀ t₁ t₂ f : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyHistory.context_m Δ) .set →
      Term ℒ [] Θ .set) : Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (Metatheory.Formula.forall_close
        (capture_schema_m (Δ := Δ) B W ω t₀ t₁ t₂ f τ))) := by
  apply SecondOrderAxioms.interpretation_m
  intro ℳ hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff
    (ℳ := SecondOrderQuotient.structure_l hℳ)
    (capture_schema_m (Δ := Δ) B W ω t₀ t₁ t₂ f τ)).mpr
  intro η hGuard h
  exact capture_l hℳ (Δ := Δ) B W ω t₀ t₁ t₂ f τ η hGuard h

def schema_m {Θ Δ : SortContext ℒ} (B P₀ ω Ω W t₀ t₁ t₂ f : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyHistory.context_m Δ) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  .imp (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_m Θ B (fun v => .fvar v)) <|
    .imp (SecondOrderCanonicalLevelDerives.guard_m B P₀) <|
      .imp (SecondOrderOmegaSyntax.omega_m ω) <|
        .imp (PowerlessRelativeOrdinalCutoff.first_m B ω Ω) <|
          .imp (PowerlessRelativeHierarchySyntax.level_m B Ω W) <|
            .imp (SecondOrderObjectSyntax.member_m B W) <|
              .imp (parameters_m (PowerlessRelativeSourceFamilyHistory.context_m Δ) W τ) <|
                .imp (SecondOrderObjectSyntax.member_m t₀ W) <|
                  .imp (SecondOrderObjectSyntax.member_m t₁ W) <|
                    .imp (SecondOrderObjectSyntax.member_m t₂ W) <|
                      .imp (PowerlessRelativeFiniteProgramInstruction.tags_m t₀ t₁ t₂)
                        (conclusion_m (Δ := Δ) B W ω t₀ t₁ t₂ f τ)

def sentence_m {Θ Δ : SortContext ℒ} (B P₀ ω Ω W t₀ t₁ t₂ f : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyHistory.context_m Δ) .set →
      Term ℒ [] Θ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m (Δ := Δ) B P₀ ω Ω W t₀ t₁ t₂ f τ)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Θ Δ : SortContext ℒ} (B P₀ ω Ω W t₀ t₁ t₂ f : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyHistory.context_m Δ) .set →
      Term ℒ [] Θ .set) : (sentence_m (Δ := Δ) B P₀ ω Ω W t₀ t₁ t₂ f τ).TrueIn
        (SecondOrderQuotient.structure_l hℳ) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff
    (ℳ := SecondOrderQuotient.structure_l hℳ)
    (schema_m (Δ := Δ) B P₀ ω Ω W t₀ t₁ t₂ f τ)).mpr
  intro η hClass hSeed hω hΩ hW hBW hParams h₀ h₁ h₂ ht
  have h := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff
    (ℳ := SecondOrderQuotient.structure_l hℳ)
    (PowerlessRelativeCutoffFiniteElementaryImage.schema_m (family_m Δ)
      B P₀ ω Ω W t₀ t₁ t₂ τ)).mp
    (PowerlessRelativeCutoffFiniteElementaryImage.models_l hℳ (family_m Δ)
      B P₀ ω Ω W t₀ t₁ t₂ τ) η
  exact imp_l hℳ (Δ := Δ) B W ω t₀ t₁ t₂ f τ η
    (h hClass hSeed hω hΩ hW hBW hParams h₀ h₁ h₂ ht)

theorem derives_m {Θ Δ : SortContext ℒ} (B P₀ ω Ω W t₀ t₁ t₂ f : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyHistory.context_m Δ) .set →
      Term ℒ [] Θ .set) : Derives SecondOrderArithmetic.theory_m []
        (GraphTranslation.form_m (sentence_m (Δ := Δ) B P₀ ω Ω W t₀ t₁ t₂ f τ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ =>
    models_l hℳ (Δ := Δ) B P₀ ω Ω W t₀ t₁ t₂ f τ)

#print axioms imp_l
#print axioms capture_l
#print axioms capture_derives_m
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffHistoryImage
