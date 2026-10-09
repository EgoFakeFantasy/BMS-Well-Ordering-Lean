import BMSConstructibleBridge.PowerlessHereditaryFiniteSequences

/-! # 有限序列集遗传性的原 Z₂ 推导

对象句在相对类内断言遗传参数的有限序列集存在且仍有实际可数传递包络。
量词与背景明确，正式出口是原 SecondOrderArithmetic 的 Derives。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryFiniteSequencesDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessHereditaryClassInternals

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def conclusion_m {Γ Δ : SortContext ℒ} (ω X : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .conj (PowerlessFiniteSequencesSyntax.spec_m (up ω) (up X) (.bvar .here))
    (envelope_m (.bvar .here))

theorem conclusion_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω X : Term ℒ Γ Δ .set) : (conclusion_m ω X).satisfies η ↔
      ∃ S, PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒩) (ω.eval η) (X.eval η) S ∧
        envelope_l (𝒩 := 𝒩) S := by
  simp only [conclusion_m, Formula.satisfies, PowerlessFiniteSequencesSyntax.spec_formula_l,
    envelope_formula_l, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m : Formula ℒ [] [.set, .set] :=
  let ω : Term ℒ [] [.set, .set] .set := .fvar .here
  let X : Term ℒ [] [.set, .set] .set := .fvar (.there .here)
  .imp (SecondOrderOmegaSyntax.omega_m ω) <| .imp (envelope_m X) (conclusion_m ω X)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B → ∀ y, SecondOrderQuotient.mem_l hℳ y x →
      SecondOrderQuotient.mem_l hℳ y B) :
    sentence_m.TrueIn (PowerlessRelativeClassStructure.structure_l hℳ B hBase) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, omega_formula_l, envelope_formula_l, conclusion_l]
  exact fun hω hX => PowerlessHereditaryFiniteSequences.exists_l (hBase := hBase) hω hX

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m sentence_m (fun _ h𝒩 B hBase => models_l h𝒩 B hBase)

#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryFiniteSequencesDerives
