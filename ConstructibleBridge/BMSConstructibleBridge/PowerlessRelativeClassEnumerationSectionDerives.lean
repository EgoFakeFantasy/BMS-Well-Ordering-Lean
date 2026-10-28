import BMSConstructibleBridge.PowerlessRelativeClassEnumerationSection

/-! # 类内满射的右逆存在：原 Z₂ 对象出口

对象闭句只断言集合函数右逆。构造由最小编号实现，不引入任意集合族的选择公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassEnumerationSectionDerives

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature
  SecondOrderQuotient.structure_l PowerlessRelativeClassStructure.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def onto_m {Γ Δ : SortContext ℒ} (G ω X : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.imp (member_m (.bvar .here) (up X)) (.existsE .set (.conj
    (member_m (.bvar .here) (up (up ω))) (value_m (up (up G)) (.bvar .here) (.bvar (.there .here))))))

theorem onto_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (G ω X : Term ℒ Γ Δ .set) : (onto_m G ω X).satisfies η ↔
      ∀ x, member_l 𝒩 x (X.eval η) → ∃ i, member_l 𝒩 i (ω.eval η) ∧
        value_l (ℳ := 𝒩) (G.eval η) i x := by
  simp only [onto_m, Formula.satisfies, member_m, value_formula_l, up, Arguments.eval,
    Term.eval_weakenBound, Term.eval]
  rfl

def inverse_m {Γ Δ : SortContext ℒ} (R G ω X : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (map_m R X ω) (.forallE .set (.forallE .set (.imp
    (value_m (up (up R)) (.bvar (.there .here)) (.bvar .here))
    (value_m (up (up G)) (.bvar .here) (.bvar (.there .here))))))

theorem inverse_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (R G ω X : Term ℒ Γ Δ .set) : (inverse_m R G ω X).satisfies η ↔
      map_l (ℳ := 𝒩) (R.eval η) (X.eval η) (ω.eval η) ∧
        ∀ x i, value_l (ℳ := 𝒩) (R.eval η) x i → value_l (ℳ := 𝒩) (G.eval η) i x := by
  simp only [inverse_m, Formula.satisfies, map_formula_l, value_formula_l, up,
    Term.eval_weakenBound, Term.eval]
  rfl

def schema_m : Formula ℒ [] [.set, .set, .set] :=
  let ω : Term ℒ [] [.set, .set, .set] .set := .fvar .here
  let G : Term ℒ [] [.set, .set, .set] .set := .fvar (.there .here)
  let X : Term ℒ [] [.set, .set, .set] .set := .fvar (.there (.there .here))
  .imp (SecondOrderOmegaSyntax.omega_m ω) <| .imp (map_m G ω X) <|
    .imp (onto_m G ω X) (.existsE .set (inverse_m (.bvar .here) (up G) (up ω) (up X)))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B → ∀ y,
      SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B) :
    sentence_m.TrueIn (PowerlessRelativeClassStructure.structure_l hℳ B hBase) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hω _ hOnto
  have hω' := (omega_formula_l η (.fvar .here)).mp hω
  have hOnto' := (onto_formula_l η (.fvar (.there .here)) (.fvar .here)
    (.fvar (.there (.there .here)))).mp hOnto
  obtain ⟨R, hR, hRead⟩ := PowerlessRelativeClassEnumerationSection.exists_l (hBase := hBase) hω' hOnto'
  refine ⟨R, (inverse_formula_l (η.pushBound R) (.bvar .here) (.fvar (.there .here))
    (.fvar .here) (.fvar (.there (.there .here)))).mpr ⟨hR, ?_⟩⟩
  intro x i hRi
  exact ((hRead x i).mp hRi).2.2.1

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m _ (fun _ h𝒩 B hBase => models_l h𝒩 B hBase)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassEnumerationSectionDerives
