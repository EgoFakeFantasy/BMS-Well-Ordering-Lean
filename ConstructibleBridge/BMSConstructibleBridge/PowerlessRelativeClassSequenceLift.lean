import BMSConstructibleBridge.PowerlessRelativeClassFunctionComposition
import BMSConstructibleBridge.PowerlessRelativeClassEnumerationSectionDerives

/-! # 沿类内枚举提升集合序列

复合最小编号逆图，把任意给定定义域上的 X 值函数提升为 ω 值函数。
有限长度是后续编码的特殊情形；这里不增加任意可数族选择前提。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceLift

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem exists_l {ω G X A f : type_l hℳ B}
    (hω : omega_l (ℳ := structure_l hℳ B hBase) ω)
    (hOnto : ∀ y : type_l hℳ B, mem_l hℳ y.val X.val → ∃ i : type_l hℳ B,
      mem_l hℳ i.val ω.val ∧ value_l (ℳ := structure_l hℳ B hBase) G i y)
    (hf : map_l (ℳ := structure_l hℳ B hBase) f A X) :
    ∃ g : type_l hℳ B, map_l (ℳ := structure_l hℳ B hBase) g A ω ∧
      ∀ k i y : type_l hℳ B, value_l (ℳ := structure_l hℳ B hBase) g k i →
        value_l (ℳ := structure_l hℳ B hBase) f k y → value_l (ℳ := structure_l hℳ B hBase) G i y := by
  obtain ⟨R, hR, hRead⟩ := PowerlessRelativeClassEnumerationSection.exists_l hω hOnto
  obtain ⟨g, hg, hComp⟩ := PowerlessRelativeClassFunctionComposition.exists_l hf hR
  refine ⟨g, hg, ?_⟩
  intro k i y hki hky
  obtain ⟨_, _, z, _, hkz, hzi⟩ := (hComp k i).mp hki
  have hEq : z = y := PowerlessRelativeClassFunctionComposition.value_unique_l hf hkz hky
  subst z
  exact ((hRead y i).mp hzi).2.2.1

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def lifts_m {Γ Δ : SortContext ℒ} (g f G A ω : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (SecondOrderObjectSyntax.map_m g A ω) (.forallE .set (.forallE .set (.forallE .set
    (.imp (SecondOrderObjectSyntax.value_m (up (up (up g))) (.bvar (.there (.there .here))) (.bvar (.there .here)))
      (.imp (SecondOrderObjectSyntax.value_m (up (up (up f))) (.bvar (.there (.there .here))) (.bvar .here))
        (SecondOrderObjectSyntax.value_m (up (up (up G))) (.bvar (.there .here)) (.bvar .here)))))))

theorem lifts_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (g f G A ω : Term ℒ Γ Δ .set) : (lifts_m g f G A ω).satisfies η ↔
      map_l (ℳ := 𝒩) (g.eval η) (A.eval η) (ω.eval η) ∧ ∀ k i y,
        value_l (ℳ := 𝒩) (g.eval η) k i → value_l (ℳ := 𝒩) (f.eval η) k y →
          value_l (ℳ := 𝒩) (G.eval η) i y := by
  simp only [lifts_m, Formula.satisfies, map_formula_l, value_formula_l, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m : Formula ℒ [] [.set, .set, .set, .set, .set] :=
  let ω : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar .here
  let G : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let X : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let A : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let f : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .imp (PowerlessRelativeClassEnumerationSectionDerives.onto_m G ω X) <|
      .imp (SecondOrderObjectSyntax.map_m f A X) <|
        .existsE .set (lifts_m (.bvar .here) (up f) (up G) (up A) (up ω))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    sentence_m.TrueIn (structure_l hℳ B hBase) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hω hOnto hf
  have hω' := (omega_formula_l η (.fvar .here)).mp hω
  have hOnto' := (PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l η
    (.fvar (.there .here)) (.fvar .here) (.fvar (.there (.there .here)))).mp hOnto
  have hf' := (map_formula_l η (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there .here)))).mp hf
  obtain ⟨g, hg, hLift⟩ := exists_l (hBase := hBase) hω' hOnto' hf'
  exact ⟨g, (lifts_formula_l (η.pushBound g) (.bvar .here)
    (.fvar (.there (.there (.there (.there .here))))) (.fvar (.there .here))
    (.fvar (.there (.there (.there .here)))) (.fvar .here)).mpr ⟨hg, hLift⟩⟩

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m _ (fun _ h𝒩 B hBase => models_l h𝒩 B hBase)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceLift
