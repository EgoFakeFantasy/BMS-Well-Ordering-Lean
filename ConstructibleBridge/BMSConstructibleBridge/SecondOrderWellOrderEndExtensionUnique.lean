import BMSConstructibleBridge.SecondOrderWellOrderEndExtension

/-! # 初段扩张的完整图及对象唯一性

比较值规格不足以确定集合图，故这里逐成员指定实际 Kuratowski 有序对。
固定旧序 R 和新候选序 S 后，扩张图唯一；这不宣称 S 已由原 Def
规范确定，更不从存在唯一性抽取宿主 Type 层选择函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderWellOrderEndExtensionUnique

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax StabilityFrame
open SecondOrderQuotient (type_l mem_l)
open SecondOrderWellOrderEndExtension (body_l body_m body_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

def graph_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (C D R S L : carrier_l ℳ₀) : Prop :=
  ∀ p, member_l ℳ₀ p L ↔ ∃ x y, member_l ℳ₀ x D ∧ member_l ℳ₀ y D ∧
    body_l C R S x y ∧ ordered_l x y p

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def graph_m {Γ Δ : SortContext ℒ} (C D R S L : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <|
    .iff (member_m (.bvar .here) (up L)) <|
      .existsE .set <| .existsE .set <|
        .conj (member_m (.bvar (.there .here)) (up (up (up D)))) <|
          .conj (member_m (.bvar .here) (up (up (up D)))) <|
            .conj (body_m (up (up (up C))) (up (up (up R))) (up (up (up S)))
              (.bvar (.there .here)) (.bvar .here))
              (ordered_m (.bvar (.there .here)) (.bvar .here) (.bvar (.there (.there .here))))

theorem graph_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (C D R S L : Term ℒ Γ Δ .set) :
    (graph_m C D R S L).satisfies η ↔
      graph_l (C.eval η) (D.eval η) (R.eval η) (S.eval η) (L.eval η) := by
  simp only [graph_m, graph_l, Formula.satisfies, body_formula_l, ordered_formula_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem unique_l {C D R S L T : type_l hℳ}
    (hL : graph_l (ℳ₀ := 𝒱) C D R S L) (hT : graph_l (ℳ₀ := 𝒱) C D R S T) : L = T :=
  SecondOrderQuotient.ext_l hℳ L T (fun p => (hL p).trans (hT p).symm)

theorem reading_l {C D R S L : type_l hℳ}
    (hL : graph_l (ℳ₀ := 𝒱) C D R S L) (x y : type_l hℳ) :
    value_l (ℳ := 𝒱) L x y ↔
      mem_l hℳ x D ∧ mem_l hℳ y D ∧ body_l (ℳ₀ := 𝒱) C R S x y := by
  constructor
  · rintro ⟨p, hp, hxy⟩
    obtain ⟨a, b, ha, hb, hab, hp'⟩ := (hL p).mp hp
    obtain ⟨rfl, rfl⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hxy hp').mp rfl
    exact ⟨ha, hb, hab⟩
  · rintro ⟨hx, hy, hBody⟩
    obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ x y
    exact ⟨p, (hL p).mpr ⟨x, y, hx, hy, hBody, hp⟩, hp⟩

theorem exists_l {C D R S : type_l hℳ}
    (hR : wellOrder_l (ℳ := 𝒱) C R) (hS : wellOrder_l (ℳ := 𝒱) D S) :
    ∃ L : type_l hℳ, graph_l (ℳ₀ := 𝒱) C D R S L ∧ wellOrder_l (ℳ := 𝒱) D L := by
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] := body_m
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here))))) (.fvar .here) (.fvar (.there .here))
  let η : Env 𝒱 [] [.set, .set, .set] := ((Env.empty.pushFree S).pushFree R).pushFree C
  have hφ x y : φ.satisfies ((η.pushFree y).pushFree x) ↔ body_l (ℳ₀ := 𝒱) C R S x y :=
    body_formula_l _ _ _ _ _ _
  obtain ⟨L, hL⟩ := SecondOrderDefinableRelationImage.exists_l hℳ φ η D D
  have hGraph : graph_l (ℳ₀ := 𝒱) C D R S L := by
    intro p
    exact (hL p).trans (exists_congr fun x => exists_congr fun y =>
      and_congr Iff.rfl (and_congr Iff.rfl (and_congr (hφ x y) Iff.rfl)))
  exact ⟨L, hGraph, SecondOrderWellOrderEndExtension.of_graph_l hR hS (reading_l hGraph)⟩

theorem exists_unique_l {C D R S : type_l hℳ}
    (hR : wellOrder_l (ℳ := 𝒱) C R) (hS : wellOrder_l (ℳ := 𝒱) D S) :
    ∃! L : type_l hℳ, graph_l (ℳ₀ := 𝒱) C D R S L ∧ wellOrder_l (ℳ := 𝒱) D L := by
  obtain ⟨L, hGraph, hL⟩ := exists_l hR hS
  exact ⟨L, ⟨hGraph, hL⟩, fun T hT => unique_l hT.1 hGraph⟩

def schema_m : Formula ℒ [] [.set, .set, .set, .set] :=
  let C : Term ℒ [] [.set, .set, .set, .set] .set := .fvar .here
  let D := .fvar (.there .here)
  let R := .fvar (.there (.there .here))
  let S := .fvar (.there (.there (.there .here)))
  .imp (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m C R) <|
    .imp (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m D S) <|
      .existsE .set <| .conj
        (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m (up D) (.bvar .here)) <|
          .conj (graph_m (up C) (up D) (up R) (up S) (.bvar .here)) <|
            .forallE .set <|
              .imp (graph_m (up (up C)) (up (up D)) (up (up R)) (up (up S)) (.bvar .here))
                (.equal (.bvar .here) (.bvar (.there .here)))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l, graph_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  intro hR hS
  obtain ⟨L, hGraph, hL⟩ := exists_l hR hS
  exact ⟨L, hL, hGraph, fun T hT => unique_l hT hGraph⟩

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderWellOrderEndExtensionUnique
