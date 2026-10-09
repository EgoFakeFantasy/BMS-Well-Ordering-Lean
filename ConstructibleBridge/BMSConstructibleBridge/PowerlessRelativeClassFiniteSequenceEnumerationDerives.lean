import BMSConstructibleBridge.PowerlessRelativeClassFiniteSequenceEnumeration
import BMSConstructibleBridge.PowerlessRelativeClassEnumerationUnionDerives

/-! # 可枚举类参数的有限序列可数：原 Z₂ 推导

前提是实际类内 ω 满射，结论量化实际有限序列集及其类内满射。不能以
任意模型语义结果冒充最终 BMS 良序句；这里只回传这个辅助对象句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFiniteSequenceEnumerationDerives

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def conclusion_m {Γ Δ : SortContext ℒ} (ω X : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .conj (PowerlessFiniteSequencesSyntax.spec_m (up ω) (up X) (.bvar .here))
    (PowerlessRelativeClassEnumerationUnionDerives.conclusion_m (up ω) (.bvar .here))

theorem conclusion_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω X : Term ℒ Γ Δ .set) : (conclusion_m ω X).satisfies η ↔
      ∃ S, PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒩) (ω.eval η) (X.eval η) S ∧
        ∃ T, map_l (ℳ := 𝒩) T (ω.eval η) S ∧ ∀ y, member_l 𝒩 y S →
          ∃ i, member_l 𝒩 i (ω.eval η) ∧ value_l (ℳ := 𝒩) T i y := by
  simp only [conclusion_m, Formula.satisfies, PowerlessFiniteSequencesSyntax.spec_formula_l,
    PowerlessRelativeClassEnumerationUnionDerives.conclusion_l, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m : Formula ℒ [] [.set, .set, .set] :=
  let ω : Term ℒ [] [.set, .set, .set] .set := .fvar .here
  let X : Term ℒ [] [.set, .set, .set] .set := .fvar (.there .here)
  let G : Term ℒ [] [.set, .set, .set] .set := .fvar (.there (.there .here))
  .imp (SecondOrderOmegaSyntax.omega_m ω) <| .imp (SecondOrderObjectSyntax.map_m G ω X) <|
    .imp (PowerlessMemberDefSyntax.onto_m ω X G) (conclusion_m ω X)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B → ∀ y, SecondOrderQuotient.mem_l hℳ y x →
      SecondOrderQuotient.mem_l hℳ y B) :
    sentence_m.TrueIn (PowerlessRelativeClassStructure.structure_l hℳ B hBase) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, omega_formula_l, map_formula_l,
    PowerlessRelativeClassEnumerationUnionDerives.onto_l, conclusion_l]
  exact fun hω hG hOnto => PowerlessRelativeClassFiniteSequenceEnumeration.exists_l (hBase := hBase) hω hG hOnto

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m sentence_m (fun _ h𝒩 B hBase => models_l h𝒩 B hBase)

#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFiniteSequenceEnumerationDerives
