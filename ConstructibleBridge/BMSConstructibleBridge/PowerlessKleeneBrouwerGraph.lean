import BMSConstructibleBridge.PowerlessKleeneBrouwerSyntax
import BMSConstructibleBridge.PowerlessRelativeClassRelationalGraph

/-! # 实际类内 Kleene–Brouwer 比较图

纯隶属 ℒ，原 Z₂。用已核验的 Δ₀ 类关系图构造同一 KB 比较，
读数量化全部 raw 坐标，非自返性亦在原商中成立。
此处未证明路径树上的最小元性质，不能当作前驱优先良序 J。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerGraph

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)
open PowerlessKleeneBrouwerSyntax (compare_l compare_m compare_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def reading_l (ω I S R : Raw) : Prop :=
  ∀ f g, SecondOrderFunctionObjects.value_l hℳ R f g ↔
    mem_l hℳ f S ∧ mem_l hℳ g S ∧ compare_l (𝒩 := 𝒱) ω I f g

theorem exists_l {B ω I S : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hω : PowerlessRelativeClassCorrespondence.member_l hℳ B ω)
    (hI : PowerlessRelativeClassCorrespondence.member_l hℳ B I)
    (hS : PowerlessRelativeClassCorrespondence.member_l hℳ B S) :
    ∃ R, PowerlessRelativeClassCorrespondence.member_l hℳ B R ∧ reading_l ω I S R := by
  let O : PowerlessRelativeClassStructure.type_l hℳ B := ⟨ω, hω⟩
  let I₀ : PowerlessRelativeClassStructure.type_l hℳ B := ⟨I, hI⟩
  let S₀ : PowerlessRelativeClassStructure.type_l hℳ B := ⟨S, hS⟩
  let φ : Formula ℒ [] [.set, .set, .set, .set] := compare_m
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there .here)))
    (.fvar .here) (.fvar (.there .here))
  let η : Env (PowerlessRelativeClassStructure.structure_l hℳ B hBase) [] [.set, .set] :=
    Env.empty |>.pushFree O |>.pushFree I₀
  obtain ⟨R, hR⟩ := PowerlessRelativeClassRelationalGraph.exists_ambient_l (φ := φ)
    (PowerlessKleeneBrouwerSyntax.compare_delta_l _ _ _ _) η S₀ S₀
  have hφ (f g : Raw) :
      φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree g).pushFree f) ↔
        compare_l (𝒩 := 𝒱) ω I f g := compare_formula_l _ _ _ _ _
  exact ⟨R.val, R.property, fun f g => (hR f g).trans
    (and_congr Iff.rfl (and_congr Iff.rfl (hφ f g)))⟩

theorem irreflexive_l {ω I S R : Raw} (hR : reading_l ω I S R) (f : Raw) :
    ¬SecondOrderFunctionObjects.value_l hℳ R f f :=
  fun h => PowerlessKleeneBrouwerSyntax.irreflexive_l ((hR f f).mp h).2.2

def reading_m {Γ Δ : SortContext ℒ} (ω I S R : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <|
    .iff (PowerlessValueBounded.formula_m (up (up R)) (.bvar (.there .here)) (.bvar .here)) <|
      .conj (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (up (up S))) <|
        .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up (up S)))
          (compare_m (up (up ω)) (up (up I)) (.bvar (.there .here)) (.bvar .here))

theorem reading_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ) (ω I S R : Term ℒ Γ Δ .set) :
    (reading_m ω I S R).satisfies η ↔ reading_l (ω.eval η) (I.eval η) (S.eval η) (R.eval η) := by
  simp only [reading_m, reading_l, Formula.satisfies, PowerlessValueBounded.formula_l,
    compare_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m {Δ : SortContext ℒ} (B ω I S : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B ω) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B I) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B S) <|
          .existsE .set <| .conj (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here))
            (reading_m (up ω) (up I) (up S) (.bvar .here))

def sentence_m {Δ : SortContext ℒ} (B ω I S : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B ω I S)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B ω I S : Term ℒ [] Δ .set) : (sentence_m B ω I S).TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, reading_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  exact fun hBase hω hI hS => exists_l (hℳ := hℳ) hBase hω hI hS

theorem derives_m {Δ : SortContext ℒ} (B ω I S : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m B ω I S)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B ω I S)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerGraph
