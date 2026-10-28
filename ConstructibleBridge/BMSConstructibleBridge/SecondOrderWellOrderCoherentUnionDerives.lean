import BMSConstructibleBridge.SecondOrderWellOrderCoherentUnion

/-! # 相容历史并集定理的原 Z₂ 对象推导

实际纯隶属句子量化集合函数 F、G、全部内部阶段与环境子集。只证明
给定相容历史后的良序并集，不把历史存在性或规范递归列为已完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderWellOrderCoherentUnionDerives

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax StabilityFrame
open SecondOrderWellOrderCoherentUnion

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private abbrev up₆ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  up (up (up (up (up (up t)))))

def extension_m {Γ Δ : SortContext ℒ} (A R D S : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (ThirdOrderTheory.subset_m A D) <| .conj
    (.forallE .set <| .forallE .set <|
      .imp (member_m (.bvar (.there .here)) (up (up A))) <|
        .imp (member_m (.bvar .here) (up (up A))) <|
          .iff (value_m (up (up S)) (.bvar (.there .here)) (.bvar .here))
            (value_m (up (up R)) (.bvar (.there .here)) (.bvar .here)))
    (.forallE .set <| .forallE .set <|
      .imp (member_m (.bvar (.there .here)) (up (up A))) <|
        .imp (member_m (.bvar .here) (up (up D))) <|
          .imp (value_m (up (up S)) (.bvar .here) (.bvar (.there .here)))
            (member_m (.bvar .here) (up (up A))))

def coherent_m {Γ Δ : SortContext ℒ} (I J F G : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <|
    .forallE .set <| .forallE .set <| .forallE .set <|
      let i := .bvar (.there (.there (.there (.there (.there .here)))))
      let j := .bvar (.there (.there (.there (.there .here))))
      let A := .bvar (.there (.there (.there .here)))
      let R := .bvar (.there (.there .here))
      let D := .bvar (.there .here)
      let S := .bvar .here
      .imp (stage_m (up₆ I) (up₆ F) (up₆ G) i A R) <|
        .imp (stage_m (up₆ I) (up₆ F) (up₆ G) j D S) <|
          .imp (value_m (up₆ J) i j) (extension_m A R D S)

def stages_m {Γ Δ : SortContext ℒ} (I F G : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <|
    .imp (stage_m (up (up (up I))) (up (up (up F))) (up (up (up G)))
      (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))
      (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m (.bvar (.there .here)) (.bvar .here))

def cover_m {Γ Δ : SortContext ℒ} (C I F : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <|
    .iff (member_m (.bvar .here) (up C)) <|
      .existsE .set <| .existsE .set <|
        .conj (member_m (.bvar (.there .here)) (up (up (up I)))) <|
          .conj (value_m (up (up (up F))) (.bvar (.there .here)) (.bvar .here))
            (member_m (.bvar (.there (.there .here))) (.bvar .here))

theorem extension_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (A R D S : Term ℒ Γ Δ .set) :
    (extension_m A R D S).satisfies η ↔ extension_l (A.eval η) (R.eval η) (D.eval η) (S.eval η) := by
  simp only [extension_m, extension_l, Formula.satisfies, subset_formula_l, value_formula_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem coherent_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (I J F G : Term ℒ Γ Δ .set) :
    (coherent_m I J F G).satisfies η ↔ coherent_l (I.eval η) (J.eval η) (F.eval η) (G.eval η) := by
  simp only [coherent_m, coherent_l, Formula.satisfies, stage_formula_l, value_formula_l,
    extension_formula_l, up₆, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem stages_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (I F G : Term ℒ Γ Δ .set) :
    (stages_m I F G).satisfies η ↔
      ∀ i A R, stage_l (I.eval η) (F.eval η) (G.eval η) i A R → wellOrder_l A R := by
  simp only [stages_m, Formula.satisfies, stage_formula_l,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  rfl

theorem cover_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (C I F : Term ℒ Γ Δ .set) :
    (cover_m C I F).satisfies η ↔ cover_l (C.eval η) (I.eval η) (F.eval η) := by
  simp only [cover_m, cover_l, Formula.satisfies, value_formula_l, member_m,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def specification_m {Γ Δ : SortContext ℒ} (C I F G L : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m C L) <|
    .forallE .set <| .forallE .set <|
      .iff (value_m (up (up L)) (.bvar (.there .here)) (.bvar .here))
        (edge_m (up (up I)) (up (up F)) (up (up G)) (.bvar (.there .here)) (.bvar .here))

theorem specification_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (C I F G L : Term ℒ Γ Δ .set) :
    (specification_m C I F G L).satisfies η ↔ wellOrder_l (C.eval η) (L.eval η) ∧
      ∀ x y, value_l (L.eval η) x y ↔ edge_l (I.eval η) (F.eval η) (G.eval η) x y := by
  simp only [specification_m, Formula.satisfies,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    value_formula_l, edge_formula_l, up, Term.eval_weakenBound, Term.eval]
  rfl

def graph_m {Γ Δ : SortContext ℒ} (I F G L : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .iff (member_m (.bvar .here) (up L)) <|
    .existsE .set <| .existsE .set <|
      .conj (edge_m (up (up (up I))) (up (up (up F))) (up (up (up G)))
        (.bvar (.there .here)) (.bvar .here))
        (ordered_m (.bvar (.there .here)) (.bvar .here) (.bvar (.there (.there .here))))

theorem graph_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (I F G L : Term ℒ Γ Δ .set) :
    (graph_m I F G L).satisfies η ↔ graph_l (I.eval η) (F.eval η) (G.eval η) (L.eval η) := by
  simp only [graph_m, graph_l, Formula.satisfies, edge_formula_l, ordered_formula_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set] :=
  let C : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar .here
  let I := .fvar (.there .here)
  let J := .fvar (.there (.there .here))
  let F := .fvar (.there (.there (.there .here)))
  let G := .fvar (.there (.there (.there (.there .here))))
  let X := .fvar (.there (.there (.there (.there (.there .here)))))
  let Y := .fvar (.there (.there (.there (.there (.there (.there .here))))))
  .imp (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m I J) <|
    .imp (map_m F I X) <| .imp (map_m G I Y) <|
      .imp (coherent_m I J F G) <| .imp (stages_m I F G) <| .imp (cover_m C I F) <|
        .existsE .set (specification_m (up C) (up I) (up F) (up G) (.bvar .here))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l, map_formula_l,
    coherent_formula_l, stages_formula_l, cover_formula_l, specification_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  exact fun hJ hF hG hCoherent hStages hCover =>
    SecondOrderWellOrderCoherentUnion.exists_l hJ hF hG hCoherent hStages hCover

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

/-- 极限载体和值图都在结论内构造；原历史的存在仍是显式前提。 -/
def history_schema_m : Formula ℒ [] [.set, .set, .set, .set, .set, .set] :=
  let I : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar .here
  let J := .fvar (.there .here)
  let F := .fvar (.there (.there .here))
  let G := .fvar (.there (.there (.there .here)))
  let X := .fvar (.there (.there (.there (.there .here))))
  let Y := .fvar (.there (.there (.there (.there (.there .here)))))
  .imp (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m I J) <|
    .imp (map_m F I X) <| .imp (map_m G I Y) <|
      .imp (coherent_m I J F G) <| .imp (stages_m I F G) <|
        .existsE .set <| .existsE .set <|
          .conj (cover_m (.bvar (.there .here)) (up (up I)) (up (up F))) <|
            .conj (graph_m (up (up I)) (up (up F)) (up (up G)) (.bvar .here))
              (specification_m (.bvar (.there .here)) (up (up I))
                (up (up F)) (up (up G)) (.bvar .here))

def history_sentence_m : Sentence ℒ := Metatheory.Formula.forall_close history_schema_m

theorem history_models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    history_sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [history_schema_m, Formula.satisfies,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l, map_formula_l,
    coherent_formula_l, stages_formula_l, cover_formula_l, graph_formula_l,
    specification_formula_l, up, Term.eval_weakenBound, Term.eval]
  exact fun hJ hF hG hCoherent hStages => history_exists_l hJ hF hG hCoherent hStages

theorem history_derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m history_sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => history_models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderWellOrderCoherentUnionDerives
