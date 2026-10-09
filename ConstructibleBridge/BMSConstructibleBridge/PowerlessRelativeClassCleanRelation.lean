import BMSConstructibleBridge.PowerlessRelativeClassRelationalGraph
import BMSConstructibleBridge.PowerlessValueBounded
import BMSConstructibleBridge.SecondOrderRelationSyntax

/-! # 任意类内关系的无垃圾载体限制图

纯隶属 ℒ，原 Z₂。实际 Class X/R 的有界关系分离产生同一载体比较的新图。
同时保留全部 raw 坐标读数及非有序对垃圾的排除；不要求 R 良序或预具关系资格。
此通用图构造供良序规范化和可达域上的原 A 关系限制复用。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCleanRelation

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

theorem exists_l {B X R : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hX : PowerlessRelativeClassCorrespondence.member_l hℳ B X)
    (hRClass : PowerlessRelativeClassCorrespondence.member_l hℳ B R) :
    ∃ J, PowerlessRelativeClassCorrespondence.member_l hℳ B J ∧
      SecondOrderRegularRelation.relation_l hℳ J X ∧ reading_l X R J := by
  let X₀ : type_l hℳ B := ⟨X, hX⟩
  let R₀ : type_l hℳ B := ⟨R, hRClass⟩
  let φ : Formula ℒ [] [.set, .set, .set] :=
    PowerlessValueBounded.formula_m (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there .here))
  let η : Env (structure_l hℳ B hBase) [] [.set] := Env.empty |>.pushFree R₀
  obtain ⟨J, hJ⟩ := PowerlessRelativeClassRelation.exists_l
    (φ := φ) (PowerlessValueBounded.delta_l _ _ _) η X₀ X₀
  have hφ (x y : type_l hℳ B) :
      φ.satisfies ((η.pushFree y).pushFree x) ↔ value_l (ℳ := 𝒱) R x.val y.val :=
    (PowerlessValueBounded.formula_l ((η.pushFree y).pushFree x) _ _ _).trans
      (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) R₀ x y)
  have hRaw (p : Raw) : mem_l hℳ p J.val ↔ ∃ x y,
      mem_l hℳ x X ∧ mem_l hℳ y X ∧
        SecondOrderPairObjects.ordered_l hℳ x y p ∧ value_l (ℳ := 𝒱) R x y := by
    constructor
    · intro hp
      let p₀ : type_l hℳ B := ⟨p, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase J.property hp⟩
      obtain ⟨x, y, hx, hy, hPair, hValue⟩ := (hJ p₀).mp hp
      exact ⟨x.val, y.val, hx, hy,
        (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) x y p₀).mp hPair,
        (hφ x y).mp hValue⟩
    · rintro ⟨x, y, hx, hy, hPair, hValue⟩
      let x₀ : type_l hℳ B := ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hX hx⟩
      let y₀ : type_l hℳ B := ⟨y, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hX hy⟩
      let p₀ : type_l hℳ B := ⟨p, PowerlessRelativeClassPair.ordered_l hℳ hBase x₀.property y₀.property hPair⟩
      exact (hJ p₀).mpr ⟨x₀, y₀, hx, hy,
        (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) x₀ y₀ p₀).mpr hPair,
        (hφ x₀ y₀).mpr hValue⟩
  have hClean : SecondOrderRegularRelation.relation_l hℳ J.val X := by
    intro p hp
    obtain ⟨x, y, hx, hy, hPair, _⟩ := (hRaw p).mp hp
    exact ⟨x, y, hx, hy, hPair⟩
  have hRead : reading_l X R J.val := by
    intro x y
    constructor
    · rintro ⟨p, hp, hPair⟩
      obtain ⟨a, b, ha, hb, hPair', hab⟩ := (hRaw p).mp hp
      obtain ⟨hax, hby⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hPair' hPair).mp rfl
      simpa only [hax, hby] using And.intro ha (And.intro hb hab)
    · rintro ⟨hx, hy, hxy⟩
      obtain ⟨p, hPair⟩ := SecondOrderPairObjects.ordered_exists_l hℳ x y
      exact ⟨p, (hRaw p).mpr ⟨x, y, hx, hy, hPair, hxy⟩, hPair⟩
  exact ⟨J.val, J.property, hClean, hRead⟩

def schema_m {Δ : SortContext ℒ} (B X R : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <| .imp (PowerlessRelativeHierarchySyntax.class_m B X) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B R) <|
      .existsE .set <| .conj (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here)) <|
        .conj (SecondOrderRelationSyntax.relation_m (.bvar .here) (up X))
          (reading_m (up X) (up R) (.bvar .here))

def sentence_m {Δ : SortContext ℒ} (B X R : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B X R)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B X R : Term ℒ [] Δ .set) : (sentence_m B X R).TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderRelationSyntax.relation_l,
    reading_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  exact exists_l (hℳ := hℳ)

theorem derives_m {Δ : SortContext ℒ} (B X R : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m B X R)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B X R)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCleanRelation
