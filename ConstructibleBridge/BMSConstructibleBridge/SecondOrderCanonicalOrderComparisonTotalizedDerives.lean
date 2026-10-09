import BMSConstructibleBridge.SecondOrderCanonicalOrderComparisonTotalized
import BMSConstructibleBridge.SecondOrderCanonicalOrderAmbientDerives

/-! # 无旧序守卫的后继比较行原 Z₂ 推导

一个有效编码包先于全部 f、A、P、D 固定。任意输入都产生唯一总化行；
合法旧序上仍精确给出原规范后继。这里只交付后继组件的对象总性，
不把非法输入缺省行当成良序保持结论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalOrderComparisonTotalizedDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderCanonicalOrderComparisonTotalized (output_m output_l output_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
private abbrev up₄ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up (up (up t)))
private abbrev up₆ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up (up₄ t))

def mode_m {Γ Δ : SortContext ℒ} (ω e t₁ t₂ t₃ Pair Valid : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <| .forallE .set <|
    let f : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there (.there .here)))
    let A := .bvar (.there (.there .here))
    let P := .bvar (.there .here)
    let D := .bvar .here
    .existsE .set <|
      let W : Term ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ .set := .bvar .here
      let v (t : Term ℒ Γ Δ .set) := up (up₄ t)
      .conj (output_m (v ω) (up A) (up P) (v e) (v t₁) (v t₂) (v t₃) (v Pair) (v Valid)
        (up D) (up f) W) <| .forallE .set <|
          .imp (output_m (up (v ω)) (up (up A)) (up (up P)) (up (v e)) (up (v t₁))
            (up (v t₂)) (up (v t₃)) (up (v Pair)) (up (v Valid)) (up (up D)) (up (up f)) (.bvar .here))
            (.equal (.bvar .here) (up W))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem mode_formula_l {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (ω e t₁ t₂ t₃ Pair Valid : Term ℒ Γ Δ .set) :
    (mode_m ω e t₁ t₂ t₃ Pair Valid).satisfies η ↔
      ∀ f A P D : SecondOrderQuotient.type_l hℳ, ∃! W : SecondOrderQuotient.type_l hℳ,
        output_l (𝒩 := 𝒱) (ω.eval η) A P (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
          (Pair.eval η) (Valid.eval η) D f W := by
  simp only [mode_m, Formula.satisfies, ExistsUnique, output_formula_l,
    up₄, up, Term.eval_weakenBound, Term.eval]
  rfl

def total_m {Γ Δ : SortContext ℒ} (ω : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .existsE .set <| .existsE .set <| .existsE .set <|
      .existsE .set <| .existsE .set <| .existsE .set <|
        mode_m (up₆ ω) (.bvar (.there (.there (.there (.there (.there .here))))))
          (.bvar (.there (.there (.there (.there .here))))) (.bvar (.there (.there (.there .here))))
          (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)

def schema_m : Formula ℒ [] [.set] := total_m (.fvar .here)
def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) : sentence_m.TrueIn 𝒱 := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, total_m, Formula.satisfies, omega_formula_l, mode_formula_l,
    up₆, up₄, up, Term.eval_weakenBound, Term.eval]
  intro hω
  let ω : SecondOrderQuotient.type_l hℳ := η.freeVal .here
  obtain ⟨B, hBase, hωB, _⟩ := SecondOrderFiniteParameterEnvelope.exists_l hℳ ω []
  let ω' : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨ω, PowerlessRelativeClassCorrespondence.base_l hℳ hBase hωB⟩
  have hΩ : omega_l (ℳ := PowerlessRelativeClassStructure.structure_l hℳ B hBase) ω' :=
    (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω').mpr hω
  obtain ⟨K, V, hV, e, t₁, t₂, t₃, Pair, Valid, hωEq, he, hTags, hPairMap, hPair, hValid, _⟩ :=
    PowerlessRelativeClassCanonicalOrderUniform.coding_exists_l hΩ
  obtain ⟨ht₁, ht₂, ht₃⟩ := PowerlessRelativeClassSyntaxReading.tags_l (hBase := hBase) K he hTags
  refine ⟨e.val, t₁.val, t₂.val, t₃.val, Pair.val, Valid.val, ?_⟩
  intro f A P D
  change ∃! W : SecondOrderQuotient.type_l hℳ,
    output_l (𝒩 := 𝒱) ω A P e.val t₁.val t₂.val t₃.val Pair.val Valid.val D f W
  have hωRaw : ω = K.omega := hωEq
  simpa only [hωRaw, he] using
    (SecondOrderCanonicalOrderComparisonTotalized.exists_unique_l (f := f) K
      ht₁ ht₂ ht₃ hPairMap hPair hV hValid)

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms mode_formula_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalOrderComparisonTotalizedDerives
