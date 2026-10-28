import BMSConstructibleBridge.PowerlessRelativeClassInfinity
import BMSConstructibleBridge.PowerlessRelativeClassBasicAxioms

/-! # 实数参数的精确传递基集 ω ∪ {R}

不是任意传递超集：显式规格保证基集成员恰为内部自然数及实数参数。
存在句已有原 Z₂ 推导；此处不声称基集的 ω 枚举已经属于相对类。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRealSeed

open Logic FirstOrder SecondOrderObjectSyntax
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def spec_m {Γ Δ : SortContext ℒ} (ω R B : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .iff (member_m (.bvar .here) (up B))
    (.disj (member_m (.bvar .here) (up ω)) (.equal (.bvar .here) (up R)))

theorem spec_formula_l {Γ Δ : SortContext ℒ} (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ)
    (ω R B : Term ℒ Γ Δ .set) : (spec_m ω R B).satisfies η ↔
      ∀ x, mem_l hℳ x (B.eval η) ↔ mem_l hℳ x (ω.eval η) ∨ x = R.eval η := by
  simp only [spec_m, Formula.satisfies, member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (ω R : type_l hℳ)
    (hω : SecondOrderOmega.omega_l hℳ ω) (hR : ∀ x, mem_l hℳ x R → mem_l hℳ x ω) :
    ∃ B, (∀ x, mem_l hℳ x B ↔ mem_l hℳ x ω ∨ x = R) ∧
      ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B := by
  obtain ⟨S, hS⟩ := SecondOrderPairObjects.pair_exists_l hℳ R R
  obtain ⟨P, hP⟩ := SecondOrderPairObjects.pair_exists_l hℳ ω S
  have hUnion := SecondOrderUnion.models_l hℳ
  change ∀ a : type_l hℳ, ∃ U, ∀ z, mem_l hℳ z U ↔ ∃ y, mem_l hℳ y a ∧ mem_l hℳ z y at hUnion
  obtain ⟨B, hB⟩ := hUnion P
  have hSpec : ∀ x, mem_l hℳ x B ↔ mem_l hℳ x ω ∨ x = R := by
    intro x
    rw [hB]
    constructor
    · rintro ⟨y, hy, hxy⟩
      rcases (hP y).mp hy with rfl | rfl
      · exact Or.inl hxy
      · exact Or.inr (((hS x).mp hxy).elim id id)
    · rintro (hx | hEq)
      · exact ⟨ω, (hP ω).mpr (Or.inl rfl), hx⟩
      · subst x
        exact ⟨S, (hP S).mpr (Or.inr rfl), (hS R).mpr (Or.inl rfl)⟩
  refine ⟨B, hSpec, fun x hx y hy => (hSpec y).mpr (Or.inl ?_)⟩
  rcases (hSpec x).mp hx with hxω | rfl
  · exact SecondOrderOmegaTransitive.member_l hℳ hω hxω hy
  · exact hR y hy

def schema_m : Formula ℒ [] [.set, .set] :=
  .imp (SecondOrderOmegaSyntax.omega_m (.fvar .here)) <|
    .imp (ThirdOrderTheory.subset_m (.fvar (.there .here)) (.fvar .here)) <|
      .existsE .set <| .conj (spec_m (.fvar .here) (.fvar (.there .here)) (.bvar .here))
        (PowerlessRelativeHierarchyDerives.transitive_m (.bvar .here))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hω hR
  have hω' := (SecondOrderOmegaSyntax.omega_l hℳ η (.fvar .here)).mp hω
  have hR' := (ThirdOrderSemantics.subset_formula_l η (.fvar (.there .here)) (.fvar .here)).mp hR
  obtain ⟨B, hSpec, hTrans⟩ := exists_l hℳ (η.freeVal .here) (η.freeVal (.there .here)) hω' hR'
  exact ⟨B, (spec_formula_l (η.pushBound B) (.fvar .here) (.fvar (.there .here)) (.bvar .here)).mpr hSpec,
    (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ (η.pushBound B) (.bvar .here)).mpr hTrans⟩

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRealSeed
