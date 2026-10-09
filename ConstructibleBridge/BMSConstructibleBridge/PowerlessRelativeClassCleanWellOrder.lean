import BMSConstructibleBridge.PowerlessRelativeClassCleanRelation
import BMSConstructibleBridge.PowerlessRelativeClassEnumerationWellOrder
import BMSConstructibleBridge.SecondOrderRelationSyntax

/-! # 同一类内良序的无垃圾规范图

纯隶属 ℒ，原 Z₂。在实际 Class 载体积上按原 R 求值分离新图 J。
载体上的读数不变，全部 raw 子集最小元也随之保留；新图另具原关系资格。
用于拉回良序后消除非有序对垃圾，不能靠良序谓词本身取得关系资格。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCleanWellOrder

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def reading_m {Γ Δ : SortContext ℒ} (X R J : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <|
    .iff (PowerlessValueBounded.formula_m (up (up J)) (.bvar (.there .here)) (.bvar .here)) <|
      .conj (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (up (up X))) <|
        .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up (up X)))
          (PowerlessValueBounded.formula_m (up (up R)) (.bvar (.there .here)) (.bvar .here))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def reading_l (X R J : Raw) : Prop :=
  ∀ x y, value_l (ℳ := 𝒱) J x y ↔ mem_l hℳ x X ∧ mem_l hℳ y X ∧ value_l (ℳ := 𝒱) R x y

theorem reading_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ) (X R J : Term ℒ Γ Δ .set) :
    (reading_m X R J).satisfies η ↔ reading_l (X.eval η) (R.eval η) (J.eval η) := by
  simp only [reading_m, reading_l, Formula.satisfies, SecondOrderObjectSyntax.member_m,
    PowerlessValueBounded.formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem preserves_l {X R J : Raw} (hR : wellOrder_l (ℳ := 𝒱) X R) (hRead : reading_l X R J) :
    wellOrder_l (ℳ := 𝒱) X J := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx hxx
    exact hR.1 x hx ((hRead x x).mp hxx).2.2
  · intro x y z hxyz hxy hyz
    exact (hRead x z).mpr ⟨hxyz.1, hxyz.2.2,
      hR.2.1 x y z hxyz ((hRead x y).mp hxy).2.2 ((hRead y z).mp hyz).2.2⟩
  · intro x y hxy
    rcases hR.2.2.1 x y hxy with hlt | hEq | hgt
    · exact Or.inl ((hRead x y).mpr ⟨hxy.1, hxy.2, hlt⟩)
    · exact Or.inr (Or.inl hEq)
    · exact Or.inr (Or.inr ((hRead y x).mpr ⟨hxy.2, hxy.1, hgt⟩))
  · intro U hU
    obtain ⟨x, hx, hMin⟩ := hR.2.2.2 U hU
    exact ⟨x, hx, fun y hy hlt => hMin y hy ((hRead y x).mp hlt).2.2⟩

theorem exists_l {B X R : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hX : PowerlessRelativeClassCorrespondence.member_l hℳ B X)
    (hRClass : PowerlessRelativeClassCorrespondence.member_l hℳ B R)
    (hR : wellOrder_l (ℳ := 𝒱) X R) :
    ∃ J, PowerlessRelativeClassCorrespondence.member_l hℳ B J ∧
      SecondOrderRegularRelation.relation_l hℳ J X ∧ reading_l X R J ∧ wellOrder_l (ℳ := 𝒱) X J := by
  obtain ⟨J, hJClass, hClean, hRead⟩ :=
    PowerlessRelativeClassCleanRelation.exists_l hBase hX hRClass
  exact ⟨J, hJClass, hClean, hRead, preserves_l hR hRead⟩

def schema_m {Δ : SortContext ℒ} (B X R : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <| .imp (PowerlessRelativeHierarchySyntax.class_m B X) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B R) <|
      .imp (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m X R) <|
        .existsE .set <| .conj (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here)) <|
          .conj (SecondOrderRelationSyntax.relation_m (.bvar .here) (up X)) <|
            .conj (reading_m (up X) (up R) (.bvar .here))
              (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m (up X) (.bvar .here))

def sentence_m {Δ : SortContext ℒ} (B X R : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B X R)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B X R : Term ℒ [] Δ .set) : (sentence_m B X R).TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderRelationSyntax.relation_l,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l, reading_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  exact exists_l (hℳ := hℳ)

theorem derives_m {Δ : SortContext ℒ} (B X R : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m B X R)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B X R)

#print axioms preserves_l
#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCleanWellOrder
