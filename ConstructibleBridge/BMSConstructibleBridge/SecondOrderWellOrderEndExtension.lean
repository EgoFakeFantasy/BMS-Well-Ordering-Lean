import BMSConstructibleBridge.PowerlessRelativeClassAmbientWellOrder
import BMSConstructibleBridge.SecondOrderDefinableRelationImage

/-! # 保持旧序初段的实际良序扩张

旧载体 C 的比较沿 R 保持；D 中的新成员全部接在 C 后面，再沿 S 比较。
环境任意非空子集若遇到旧载体，就分离其旧部分并用 R 取最小元；否则
直接用 S。构造和对象推导只用原 Z₂，不把任意重排当作跨层相容。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderWellOrderEndExtension

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax StabilityFrame
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def body_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} (C R S x y : carrier_l ℳ₀) : Prop :=
  (member_l ℳ₀ x C ∧ member_l ℳ₀ y C ∧ value_l R x y) ∨
    (member_l ℳ₀ x C ∧ ¬member_l ℳ₀ y C) ∨
      (¬member_l ℳ₀ x C ∧ ¬member_l ℳ₀ y C ∧ value_l S x y)

def body_m {Γ Δ : SortContext ℒ} (C R S x y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (.conj (member_m x C) (.conj (member_m y C) (PowerlessValueBounded.formula_m R x y))) <|
    .disj (.conj (member_m x C) (.neg (member_m y C))) <|
      .conj (.neg (member_m x C)) <|
        .conj (.neg (member_m y C)) (PowerlessValueBounded.formula_m S x y)

theorem body_delta_l {Γ Δ : SortContext ℒ} (C R S x y : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (body_m C R S x y) :=
  .disj (.conj (.rel _ _) (.conj (.rel _ _) (PowerlessValueBounded.delta_l _ _ _)))
    (.disj (.conj (.rel _ _) (.neg (.rel _ _)))
      (.conj (.neg (.rel _ _)) (.conj (.neg (.rel _ _)) (PowerlessValueBounded.delta_l _ _ _))))

theorem body_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (C R S x y : Term ℒ Γ Δ .set) :
    (body_m C R S x y).satisfies η ↔
      body_l (C.eval η) (R.eval η) (S.eval η) (x.eval η) (y.eval η) := by
  simp only [body_m, body_l, Formula.satisfies, member_m, Arguments.eval,
    PowerlessValueBounded.formula_l]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem of_graph_l {C D R S L : type_l hℳ}
    (hR : wellOrder_l (ℳ := 𝒱) C R) (hS : wellOrder_l (ℳ := 𝒱) D S)
    (hRead : ∀ x y, value_l (ℳ := 𝒱) L x y ↔
      mem_l hℳ x D ∧ mem_l hℳ y D ∧ body_l (ℳ₀ := 𝒱) C R S x y) :
    wellOrder_l (ℳ := 𝒱) D L := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x _ hxx
    rcases ((hRead x x).mp hxx).2.2 with ⟨hx, _, h⟩ | ⟨hx, hnx⟩ | ⟨_, _, h⟩
    · exact hR.1 x hx h
    · exact hnx hx
    · exact hS.1 x ((hRead x x).mp hxx).1 h
  · intro x y z hxyz hxy hyz
    apply (hRead x z).mpr ⟨hxyz.1, hxyz.2.2, ?_⟩
    rcases ((hRead x y).mp hxy).2.2 with ⟨hx, hy, hxy⟩ | ⟨hx, hny⟩ | ⟨hnx, hny, hxy⟩
    · rcases ((hRead y z).mp hyz).2.2 with ⟨_, hz, hyz⟩ | ⟨_, hnz⟩ | ⟨hny, _, _⟩
      · exact Or.inl ⟨hx, hz, hR.2.1 x y z ⟨hx, hy, hz⟩ hxy hyz⟩
      · exact Or.inr (Or.inl ⟨hx, hnz⟩)
      · exact (hny hy).elim
    · rcases ((hRead y z).mp hyz).2.2 with ⟨hy, _, _⟩ | ⟨hy, _⟩ | ⟨_, hnz, _⟩
      · exact (hny hy).elim
      · exact (hny hy).elim
      · exact Or.inr (Or.inl ⟨hx, hnz⟩)
    · rcases ((hRead y z).mp hyz).2.2 with ⟨hy, _, _⟩ | ⟨hy, _⟩ | ⟨_, hnz, hyz⟩
      · exact (hny hy).elim
      · exact (hny hy).elim
      · exact Or.inr (Or.inr ⟨hnx, hnz, hS.2.1 x y z hxyz hxy hyz⟩)
  · intro x y hxy
    by_cases hx : mem_l hℳ x C
    · by_cases hy : mem_l hℳ y C
      · rcases hR.2.2.1 x y ⟨hx, hy⟩ with h | h | h
        · exact Or.inl ((hRead x y).mpr ⟨hxy.1, hxy.2, Or.inl ⟨hx, hy, h⟩⟩)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ((hRead y x).mpr ⟨hxy.2, hxy.1, Or.inl ⟨hy, hx, h⟩⟩))
      · exact Or.inl ((hRead x y).mpr ⟨hxy.1, hxy.2, Or.inr (Or.inl ⟨hx, hy⟩)⟩)
    · by_cases hy : mem_l hℳ y C
      · exact Or.inr (Or.inr ((hRead y x).mpr ⟨hxy.2, hxy.1, Or.inr (Or.inl ⟨hy, hx⟩)⟩))
      · rcases hS.2.2.1 x y hxy with h | h | h
        · exact Or.inl ((hRead x y).mpr ⟨hxy.1, hxy.2, Or.inr (Or.inr ⟨hx, hy, h⟩)⟩)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ((hRead y x).mpr ⟨hxy.2, hxy.1, Or.inr (Or.inr ⟨hy, hx, h⟩)⟩))
  · intro U hU
    by_cases hOld : ∃ x, mem_l hℳ x U ∧ mem_l hℳ x C
    · let φ : Formula ℒ [] [.set, .set] := member_m (.fvar .here) (.fvar (.there .here))
      let η : Env 𝒱 [] [.set] := Env.empty.pushFree C
      obtain ⟨V, hV⟩ := (SecondOrderSeparationAxiom.schema_l hℳ φ η).mp
        (SecondOrderSeparationAxiom.models_l hℳ φ η) U
      have hVRead x : mem_l hℳ x V ↔ mem_l hℳ x U ∧ mem_l hℳ x C := hV x
      obtain ⟨x₀, hx₀, hx₀C⟩ := hOld
      obtain ⟨x, hxV, hMin⟩ := hR.2.2.2 V
        ⟨fun y hy => ((hVRead y).mp hy).2, x₀, (hVRead x₀).mpr ⟨hx₀, hx₀C⟩⟩
      obtain ⟨hxU, hxC⟩ := (hVRead x).mp hxV
      refine ⟨x, hxU, ?_⟩
      intro y hy hEdge
      rcases ((hRead y x).mp hEdge).2.2 with ⟨hyC, _, hyx⟩ | ⟨_, hnx⟩ | ⟨_, hnx, _⟩
      · exact hMin y ((hVRead y).mpr ⟨hy, hyC⟩) hyx
      · exact hnx hxC
      · exact hnx hxC
    · obtain ⟨x, hx, hMin⟩ := hS.2.2.2 U hU
      refine ⟨x, hx, ?_⟩
      intro y hy hEdge
      rcases ((hRead y x).mp hEdge).2.2 with ⟨hyC, _, _⟩ | ⟨hyC, _⟩ | ⟨_, _, hyx⟩
      · exact hOld ⟨y, hy, hyC⟩
      · exact hOld ⟨y, hy, hyC⟩
      · exact hMin y hy hyx

theorem old_l {C D R S L : type_l hℳ} (hCD : subset_l (ℳ := 𝒱) C D)
    (hRead : ∀ x y, value_l (ℳ := 𝒱) L x y ↔
      mem_l hℳ x D ∧ mem_l hℳ y D ∧ body_l (ℳ₀ := 𝒱) C R S x y)
    {x y : type_l hℳ} (hx : mem_l hℳ x C) (hy : mem_l hℳ y C) :
    value_l (ℳ := 𝒱) L x y ↔ value_l (ℳ := 𝒱) R x y := by
  constructor
  · intro h
    rcases ((hRead x y).mp h).2.2 with ⟨_, _, hxy⟩ | ⟨_, hny⟩ | ⟨hnx, _, _⟩
    · exact hxy
    · exact (hny hy).elim
    · exact (hnx hx).elim
  · exact fun h => (hRead x y).mpr ⟨hCD x hx, hCD y hy, Or.inl ⟨hx, hy, h⟩⟩

/-- 比旧成员更早的点仍在旧载体，排除扩张中的反向跨块比较。 -/
theorem initial_l {C D R S L x y : type_l hℳ}
    (hRead : ∀ x y, value_l (ℳ := 𝒱) L x y ↔
      mem_l hℳ x D ∧ mem_l hℳ y D ∧ body_l (ℳ₀ := 𝒱) C R S x y)
    (hx : mem_l hℳ x C) (hyx : value_l (ℳ := 𝒱) L y x) : mem_l hℳ y C := by
  rcases ((hRead y x).mp hyx).2.2 with ⟨hy, _, _⟩ | ⟨_, hnx⟩ | ⟨_, hnx, _⟩
  · exact hy
  · exact (hnx hx).elim
  · exact (hnx hx).elim

theorem exists_l {C D R S : type_l hℳ}
    (hR : wellOrder_l (ℳ := 𝒱) C R) (hS : wellOrder_l (ℳ := 𝒱) D S) :
    ∃ L : type_l hℳ, wellOrder_l (ℳ := 𝒱) D L ∧
      ∀ x y, value_l (ℳ := 𝒱) L x y ↔
        mem_l hℳ x D ∧ mem_l hℳ y D ∧ body_l (ℳ₀ := 𝒱) C R S x y := by
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] := body_m
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here))))) (.fvar .here) (.fvar (.there .here))
  let η : Env 𝒱 [] [.set, .set, .set] := ((Env.empty.pushFree S).pushFree R).pushFree C
  have hφ x y : φ.satisfies ((η.pushFree y).pushFree x) ↔ body_l (ℳ₀ := 𝒱) C R S x y :=
    body_formula_l _ _ _ _ _ _
  obtain ⟨L, hL⟩ := SecondOrderDefinableRelationImage.exists_l hℳ φ η D D
  have hRead x y : value_l (ℳ := 𝒱) L x y ↔
      mem_l hℳ x D ∧ mem_l hℳ y D ∧ body_l (ℳ₀ := 𝒱) C R S x y := by
    constructor
    · rintro ⟨p, hp, hxy⟩
      obtain ⟨a, b, ha, hb, hab, hp'⟩ := (hL p).mp hp
      obtain ⟨rfl, rfl⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hxy hp').mp rfl
      exact ⟨ha, hb, (hφ x y).mp hab⟩
    · rintro ⟨hx, hy, hBody⟩
      obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ x y
      exact ⟨p, (hL p).mpr ⟨x, y, hx, hy, (hφ x y).mpr hBody, hp⟩, hp⟩
  exact ⟨L, of_graph_l hR hS hRead, hRead⟩

def specification_m {Γ Δ : SortContext ℒ} (C D R S L : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m D L) <|
    .forallE .set <| .forallE .set <|
      .iff (value_m (up (up L)) (.bvar (.there .here)) (.bvar .here)) <|
        .conj (member_m (.bvar (.there .here)) (up (up D))) <|
          .conj (member_m (.bvar .here) (up (up D))) <|
            body_m (up (up C)) (up (up R)) (up (up S)) (.bvar (.there .here)) (.bvar .here)

theorem specification_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (C D R S L : Term ℒ Γ Δ .set) :
    (specification_m C D R S L).satisfies η ↔
      wellOrder_l (D.eval η) (L.eval η) ∧ ∀ x y, value_l (L.eval η) x y ↔
        member_l ℳ₀ x (D.eval η) ∧ member_l ℳ₀ y (D.eval η) ∧
          body_l (C.eval η) (R.eval η) (S.eval η) x y := by
  simp only [specification_m, Formula.satisfies,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    value_formula_l, body_formula_l, member_m, Arguments.eval,
    up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m : Formula ℒ [] [.set, .set, .set, .set] :=
  let C : Term ℒ [] [.set, .set, .set, .set] .set := .fvar .here
  let D : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there .here)
  let R : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let S : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  .imp (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m C R) <|
    .imp (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m D S) <|
      .existsE .set (specification_m (up C) (up D) (up R) (up S) (.bvar .here))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    specification_formula_l, up, Term.eval_weakenBound, Term.eval]
  exact fun hR hS => exists_l hR hS

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms of_graph_l
#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderWellOrderEndExtension
