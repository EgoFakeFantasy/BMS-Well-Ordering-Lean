import BMSConstructibleBridge.PowerlessRelativeClassRelationalGraph
import BMSConstructibleBridge.PowerlessRelativeClassEnumerationWellOrder

/-! # 任意两个类内良序的实际字典序积

先构造类内笛卡尔积，再用有界分离形成字典序关系。非空内部子集先取
第一坐标投影的最小元，再取相应纤维的最小元；不要求 ω 枚举或 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassLexicographicWellOrder

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassEnumerationWellOrder (wellOrder_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
private abbrev up₄ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up (up (up t)))

def lex_m {Γ Δ : SortContext ℒ} (X Y R S p q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists X <| membershipLevyBound.boundedExists (up Y) <|
    membershipLevyBound.boundedExists (up (up X)) <| membershipLevyBound.boundedExists (up (up (up Y))) <|
      .conj (PowerlessPairBounded.ordered_m (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here))) (up₄ p)) <|
        .conj (PowerlessPairBounded.ordered_m (.bvar (.there .here)) (.bvar .here) (up₄ q)) <|
          .disj (PowerlessValueBounded.formula_m (up₄ R) (.bvar (.there (.there (.there .here)))) (.bvar (.there .here)))
            (.conj (.equal (.bvar (.there (.there (.there .here)))) (.bvar (.there .here)))
              (PowerlessValueBounded.formula_m (up₄ S) (.bvar (.there (.there .here))) (.bvar .here)))

theorem lex_delta_l {Γ Δ : SortContext ℒ} (X Y R S p q : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (lex_m X Y R S p q) :=
  .bounded_exists _ (.bounded_exists _ (.bounded_exists _ (.bounded_exists _
    (.conj (PowerlessPairBounded.ordered_delta_l _ _ _)
      (.conj (PowerlessPairBounded.ordered_delta_l _ _ _)
        (.disj (PowerlessValueBounded.delta_l _ _ _) (.conj (.equal _ _) (PowerlessValueBounded.delta_l _ _ _))))))))

def lex_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} (X Y R S p q : carrier_l ℳ₀) : Prop :=
  ∃ x y a b, member_l ℳ₀ x X ∧ member_l ℳ₀ y Y ∧ member_l ℳ₀ a X ∧ member_l ℳ₀ b Y ∧
    ordered_l x y p ∧ ordered_l a b q ∧ (value_l R x a ∨ x = a ∧ value_l S y b)

theorem lex_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (X Y R S p q : Term ℒ Γ Δ .set) :
    (lex_m X Y R S p q).satisfies η ↔ lex_l (X.eval η) (Y.eval η) (R.eval η) (S.eval η) (p.eval η) (q.eval η) := by
  simp only [lex_m, lex_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessPairBounded.ordered_formula_l,
    PowerlessValueBounded.formula_l, Arguments.eval, up₄, up, Term.eval_weakenBound, Term.eval]
  exact ⟨fun ⟨x, hx, y, hy, a, ha, b, hb, hp, hq, h⟩ => ⟨x, y, a, b, hx, hy, ha, hb, hp, hq, h⟩,
    fun ⟨x, y, a, b, hx, hy, ha, hb, hp, hq, h⟩ => ⟨x, hx, y, hy, a, ha, b, hb, hp, hq, h⟩⟩

def fiber_m {Γ Δ : SortContext ℒ} (U x y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists U (PowerlessPairBounded.ordered_m (up x) (up y) (.bvar .here))

theorem fiber_delta_l {Γ Δ : SortContext ℒ} (U x y : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (fiber_m U x y) :=
  .bounded_exists _ (PowerlessPairBounded.ordered_delta_l _ _ _)

theorem fiber_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (U x y : Term ℒ Γ Δ .set) :
    (fiber_m U x y).satisfies η ↔ ∃ p, member_l ℳ₀ p (U.eval η) ∧ ordered_l (x.eval η) (y.eval η) p := by
  simp only [fiber_m, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessPairBounded.ordered_formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def projection_m {Γ Δ : SortContext ℒ} (Y U x : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists Y (fiber_m (up U) (up x) (.bvar .here))

theorem projection_delta_l {Γ Δ : SortContext ℒ} (Y U x : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (projection_m Y U x) :=
  .bounded_exists _ (fiber_delta_l _ _ _)

theorem projection_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (Y U x : Term ℒ Γ Δ .set) :
    (projection_m Y U x).satisfies η ↔ ∃ y, member_l ℳ₀ y (Y.eval η) ∧
      ∃ p, member_l ℳ₀ p (U.eval η) ∧ ordered_l (x.eval η) y p := by
  simp only [projection_m, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, fiber_formula_l, Arguments.eval,
    up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "ClassModel" => structure_l hℳ B hBase

private theorem coordinates_l {x y a b p : type_l hℳ B}
    (hp : ordered_l (ℳ := ClassModel) x y p) (hq : ordered_l (ℳ := ClassModel) a b p) : x = a ∧ y = b := by
  have h := (SecondOrderPairObjects.ordered_eq_l hℳ
    ((PowerlessRelativeClassFunctionAbsolute.ordered_l x y p).mp hp)
    ((PowerlessRelativeClassFunctionAbsolute.ordered_l a b p).mp hq)).mp rfl
  exact ⟨Subtype.ext h.1, Subtype.ext h.2⟩

private theorem pair_unique_l {x y p q : type_l hℳ B}
    (hp : ordered_l (ℳ := ClassModel) x y p) (hq : ordered_l (ℳ := ClassModel) x y q) : p = q :=
  Subtype.ext (SecondOrderPairObjects.ordered_unique_l hℳ
    ((PowerlessRelativeClassFunctionAbsolute.ordered_l x y p).mp hp)
    ((PowerlessRelativeClassFunctionAbsolute.ordered_l x y q).mp hq))

theorem exists_l {X Y R S : type_l hℳ B}
    (hR : wellOrder_l (ℳ := ClassModel) X R) (hS : wellOrder_l (ℳ := ClassModel) Y S) :
    ∃ P L : type_l hℳ B,
      (∀ p : type_l hℳ B, mem_l hℳ p.val P.val ↔ ∃ x y : type_l hℳ B,
        mem_l hℳ x.val X.val ∧ mem_l hℳ y.val Y.val ∧ ordered_l (ℳ := ClassModel) x y p) ∧
      wellOrder_l (ℳ := ClassModel) P L ∧
      ∀ p q : type_l hℳ B, value_l (ℳ := ClassModel) L p q ↔ lex_l (ℳ₀ := ClassModel) X Y R S p q := by
  obtain ⟨P, hP⟩ := PowerlessRelativeClassProduct.exists_l hBase X Y
  let η : Env ClassModel [] [.set, .set, .set, .set] := ((((Env.empty).pushFree S).pushFree R).pushFree Y).pushFree X
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set] := lex_m
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here))))) (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar .here) (.fvar (.there .here))
  have hφ (p q : type_l hℳ B) : φ.satisfies ((η.pushFree q).pushFree p) ↔
      lex_l (ℳ₀ := ClassModel) X Y R S p q := lex_formula_l _ _ _ _ _ _ _
  obtain ⟨L, hL⟩ := PowerlessRelativeClassRelationalGraph.exists_l (φ := φ) (lex_delta_l _ _ _ _ _ _) η P P
  have hRead (p q : type_l hℳ B) : value_l (ℳ := ClassModel) L p q ↔ lex_l (ℳ₀ := ClassModel) X Y R S p q := by
    constructor
    · intro hpq
      exact (hφ p q).mp ((hL p q).mp hpq).2.2
    · intro hpq
      obtain ⟨x, y, a, b, hx, hy, ha, hb, hp, hq, hcomp⟩ := hpq
      exact (hL p q).mpr ⟨(hP p).mpr ⟨x, y, hx, hy, hp⟩,
        (hP q).mpr ⟨a, b, ha, hb, hq⟩, (hφ p q).mpr ⟨x, y, a, b, hx, hy, ha, hb, hp, hq, hcomp⟩⟩
  refine ⟨P, L, hP, ?_, hRead⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p _ hpp
    obtain ⟨x, y, a, b, hx, hy, _, _, hp, hq, h⟩ := (hRead p p).mp hpp
    obtain ⟨hxa, hyb⟩ := coordinates_l hp hq
    subst a
    subst b
    exact h.elim (hR.1 x hx) (fun h => hS.1 y hy h.2)
  · intro p q r _ hpq hqr
    obtain ⟨x, y, a, b, hx, hy, ha, hb, hp, hq, h₁⟩ := (hRead p q).mp hpq
    obtain ⟨a', b', c, d, _, _, hc, hd, hq', hr, h₂⟩ := (hRead q r).mp hqr
    obtain ⟨haa, hbb⟩ := coordinates_l hq hq'
    subst a'
    subst b'
    apply (hRead p r).mpr
    refine ⟨x, y, c, d, hx, hy, hc, hd, hp, hr, ?_⟩
    rcases h₁ with hxa | ⟨rfl, hyb⟩
    · rcases h₂ with hac | ⟨rfl, _⟩
      · exact Or.inl (hR.2.1 x a c ⟨hx, ha, hc⟩ hxa hac)
      · exact Or.inl hxa
    · rcases h₂ with hac | ⟨rfl, hbd⟩
      · exact Or.inl hac
      · exact Or.inr ⟨rfl, hS.2.1 y b d ⟨hy, hb, hd⟩ hyb hbd⟩
  · intro p q hpq
    obtain ⟨x, y, hx, hy, hp⟩ := (hP p).mp hpq.1
    obtain ⟨a, b, ha, hb, hq⟩ := (hP q).mp hpq.2
    rcases hR.2.2.1 x a ⟨hx, ha⟩ with hxa | hxa | hax
    · exact Or.inl ((hRead p q).mpr ⟨x, y, a, b, hx, hy, ha, hb, hp, hq, Or.inl hxa⟩)
    · subst a
      rcases hS.2.2.1 y b ⟨hy, hb⟩ with hyb | hyb | hby
      · exact Or.inl ((hRead p q).mpr ⟨x, y, x, b, hx, hy, ha, hb, hp, hq, Or.inr ⟨rfl, hyb⟩⟩)
      · subst b
        exact Or.inr (Or.inl (pair_unique_l hp hq))
      · exact Or.inr (Or.inr ((hRead q p).mpr ⟨x, b, x, y, ha, hb, hx, hy, hq, hp, Or.inr ⟨rfl, hby⟩⟩))
    · exact Or.inr (Or.inr ((hRead q p).mpr ⟨a, b, x, y, ha, hb, hx, hy, hq, hp, Or.inl hax⟩))
  · intro U hU
    let ξ : Env ClassModel [] [.set, .set] := ((Env.empty).pushFree U).pushFree Y
    let ψ : Formula ℒ [] [.set, .set, .set] := projection_m (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)
    obtain ⟨A, hA⟩ := PowerlessRelativeClassDeltaSeparation.exists_l (φ := ψ) (projection_delta_l _ _ _) ξ X
    have hARead (x : type_l hℳ B) : mem_l hℳ x.val A.val ↔ mem_l hℳ x.val X.val ∧
        ∃ y : type_l hℳ B, mem_l hℳ y.val Y.val ∧ ∃ p : type_l hℳ B, mem_l hℳ p.val U.val ∧ ordered_l (ℳ := ClassModel) x y p :=
      (hA x).trans (and_congr Iff.rfl (projection_formula_l _ _ _ _))
    obtain ⟨p₀, hp₀⟩ := hU.2
    obtain ⟨x₀, y₀, hx₀, hy₀, hxy₀⟩ := (hP p₀).mp (hU.1 p₀ hp₀)
    obtain ⟨x, hxA, hMinX⟩ := hR.2.2.2 A ⟨fun a ha => ((hARead a).mp ha).1,
      x₀, (hARead x₀).mpr ⟨hx₀, y₀, hy₀, p₀, hp₀, hxy₀⟩⟩
    obtain ⟨hx, y₁, hy₁, p₁, hp₁, hxy₁⟩ := (hARead x).mp hxA
    let ζ : Env ClassModel [] [.set, .set] := ((Env.empty).pushFree U).pushFree x
    let χ : Formula ℒ [] [.set, .set, .set] := fiber_m (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)
    obtain ⟨D, hD⟩ := PowerlessRelativeClassDeltaSeparation.exists_l (φ := χ) (fiber_delta_l _ _ _) ζ Y
    have hDRead (y : type_l hℳ B) : mem_l hℳ y.val D.val ↔ mem_l hℳ y.val Y.val ∧
        ∃ p : type_l hℳ B, mem_l hℳ p.val U.val ∧ ordered_l (ℳ := ClassModel) x y p :=
      (hD y).trans (and_congr Iff.rfl (fiber_formula_l _ _ _ _))
    obtain ⟨y, hyD, hMinY⟩ := hS.2.2.2 D ⟨fun b hb => ((hDRead b).mp hb).1,
      y₁, (hDRead y₁).mpr ⟨hy₁, p₁, hp₁, hxy₁⟩⟩
    obtain ⟨hy, p, hpU, hp⟩ := (hDRead y).mp hyD
    refine ⟨p, hpU, ?_⟩
    intro q hqU hqp
    obtain ⟨a, b, x', y', ha, hb, _, _, hq, hp', h⟩ := (hRead q p).mp hqp
    obtain ⟨hxx, hyy⟩ := coordinates_l hp' hp
    subst x'
    subst y'
    rcases h with hax | ⟨rfl, hby⟩
    · exact hMinX a ((hARead a).mpr ⟨ha, b, hb, q, hqU, hq⟩) hax
    · exact hMinY b ((hDRead b).mpr ⟨hb, q, hqU, hq⟩) hby

def specification_m {Γ Δ : SortContext ℒ} (X Y R S P L : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (.forallE .set (.iff (member_m (.bvar .here) (up P))
    (PowerlessRelativeClassProduct.body_m (up X) (up Y) (.bvar .here)))) <|
    .conj (wellOrder_m P L) <| .forallE .set <| .forallE .set <|
      .iff (value_m (up (up L)) (.bvar (.there .here)) (.bvar .here))
        (lex_m (up (up X)) (up (up Y)) (up (up R)) (up (up S)) (.bvar (.there .here)) (.bvar .here))

theorem specification_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (X Y R S P L : Term ℒ Γ Δ .set) :
    (specification_m X Y R S P L).satisfies η ↔
      (∀ p, member_l ℳ₀ p (P.eval η) ↔ ∃ x y, member_l ℳ₀ x (X.eval η) ∧ member_l ℳ₀ y (Y.eval η) ∧ ordered_l x y p) ∧
      wellOrder_l (P.eval η) (L.eval η) ∧ ∀ p q, value_l (L.eval η) p q ↔
        lex_l (X.eval η) (Y.eval η) (R.eval η) (S.eval η) p q := by
  simp only [specification_m, Formula.satisfies, member_m, Arguments.eval,
    PowerlessRelativeClassProduct.body_formula_l, PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l, value_formula_l,
    lex_formula_l, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m : Formula ℒ [] [.set, .set, .set, .set] :=
  let X : Term ℒ [] [.set, .set, .set, .set] .set := .fvar .here
  let Y : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there .here)
  let R : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let S : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  .imp (wellOrder_m X R) <| .imp (wellOrder_m Y S) <| .existsE .set <| .existsE .set <|
    specification_m (up (up X)) (up (up Y)) (up (up R)) (up (up S)) (.bvar (.there .here)) (.bvar .here)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    sentence_m.TrueIn (structure_l hℳ B hBase) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l, specification_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  exact fun hR hS => exists_l (hBase := hBase) hR hS

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m _ (fun _ h𝒩 B hBase => models_l h𝒩 B hBase)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassLexicographicWellOrder
