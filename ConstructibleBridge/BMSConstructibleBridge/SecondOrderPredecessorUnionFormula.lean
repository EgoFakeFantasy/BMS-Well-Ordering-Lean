import BMSConstructibleBridge.SecondOrderPredecessorUnion
import BMSConstructibleBridge.SecondOrderMemberDefGraphFormula

/-! # 前驱并集的原语言公式与精确读出

两张中间图分别以完整关系规格和完整筛选规格绑定；输出保留公开参数。
存在块的语义严格对应唯一原图接口，供相对层次的逐阶段正文使用。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPredecessorUnionFormula

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private theorem graph_env_l (η : Env ℳ [] [.num, .num, .set, .set, .num]) :
    SecondOrderPredecessorTaggedGraph.formula_m.satisfies η ↔
      SecondOrderPredecessorTaggedGraph.edge_l (η.freeVal (.there (.there .here)))
        (η.freeVal (.there (.there (.there .here))))
        (η.freeVal (.there (.there (.there (.there .here)))))
        (η.freeVal .here) (η.freeVal (.there .here)) := by
  have hη : η = ((((((Env.empty (M := ℳ)).pushFree
      (η.freeVal (.there (.there (.there (.there .here)))))).pushFree
      (η.freeVal (.there (.there (.there .here))))).pushFree
      (η.freeVal (.there (.there .here)))).pushFree
      (η.freeVal (.there .here))).pushFree (η.freeVal .here)) := by
    apply Env.ext
    · intro s v
      nomatch v
    · intro s v
      match v with
      | .here => rfl
      | .there .here => rfl
      | .there (.there .here) => rfl
      | .there (.there (.there .here)) => rfl
      | .there (.there (.there (.there .here))) => rfl
  conv_lhs => rw [hη]
  exact SecondOrderPredecessorTaggedGraph.formula_l _ _ _ _ _

private theorem selection_env_l (η : Env ℳ [] [.num, .set, .set, .num]) :
    SecondOrderPredecessorUnion.selector_m.satisfies η ↔
      SecondOrderPredecessorUnion.selected_l (η.freeVal (.there .here))
        (η.freeVal (.there (.there .here))) (η.freeVal (.there (.there (.there .here))))
        (η.freeVal .here) := by
  have hη : η = (((((Env.empty (M := ℳ)).pushFree
      (η.freeVal (.there (.there (.there .here))))).pushFree
      (η.freeVal (.there (.there .here)))).pushFree
      (η.freeVal (.there .here))).pushFree (η.freeVal .here)) := by
    apply Env.ext
    · intro s v
      nomatch v
    · intro s v
      match v with
      | .here => rfl
      | .there .here => rfl
      | .there (.there .here) => rfl
      | .there (.there (.there .here)) => rfl
  conv_lhs => rw [hη]
  exact SecondOrderPredecessorUnion.selector_formula_l _ _ _ _

def graph_m {Γ Δ : SortContext signature_m} (R H : Term signature_m Γ Δ .set)
    (n : Term signature_m Γ Δ .num) (G : Term signature_m Γ Δ .set) : Formula signature_m Γ Δ :=
  SecondOrderRelationSpecification.formula_m SecondOrderPredecessorTaggedGraph.formula_m G
    (fun v => match v with | .here => R | .there .here => H | .there (.there .here) => n)

def selection_m {Γ Δ : SortContext signature_m} (R H : Term signature_m Γ Δ .set)
    (n : Term signature_m Γ Δ .num) (P : Term signature_m Γ Δ .set) : Formula signature_m Γ Δ :=
  SecondOrderSetSpecification.formula_m SecondOrderPredecessorUnion.selector_m P
    (fun v => match v with | .here => R | .there .here => H | .there (.there .here) => n)

theorem graph_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (R H : Term signature_m Γ Δ .set) (n : Term signature_m Γ Δ .num)
    (G : Term signature_m Γ Δ .set) : (graph_m R H n G).satisfies η ↔
      SecondOrderPredecessorTaggedGraph.spec_l (R.eval η) (H.eval η) (n.eval η) (G.eval η) := by
  simp only [graph_m, SecondOrderRelationSpecification.formula_l, graph_env_l]
  rfl

theorem selection_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (R H : Term signature_m Γ Δ .set) (n : Term signature_m Γ Δ .num)
    (P : Term signature_m Γ Δ .set) : (selection_m R H n P).satisfies η ↔
      ∀ c, mem_l c (P.eval η) ↔ SecondOrderPredecessorUnion.selected_l
        (R.eval η) (H.eval η) (n.eval η) c := by
  simp only [selection_m, SecondOrderSetSpecification.formula_l, selection_env_l]
  rfl

def formula_m {Γ Δ : SortContext signature_m} (R H : Term signature_m Γ Δ .set)
    (n : Term signature_m Γ Δ .num) (W : Term signature_m Γ Δ .set) : Formula signature_m Γ Δ :=
  .existsE .set <| .existsE .set <| .conj
    (graph_m (R.weakenBound sort_m.set |>.weakenBound sort_m.set)
      (H.weakenBound sort_m.set |>.weakenBound sort_m.set)
      (n.weakenBound sort_m.set |>.weakenBound sort_m.set) (.bvar (.there .here))) <|
    .conj (selection_m (R.weakenBound sort_m.set |>.weakenBound sort_m.set)
      (H.weakenBound sort_m.set |>.weakenBound sort_m.set)
      (n.weakenBound sort_m.set |>.weakenBound sort_m.set) (.bvar .here))
      (SecondOrderMemberDefGraphFormula.graft_m (.bvar (.there .here)) (.bvar .here)
        (W.weakenBound sort_m.set |>.weakenBound sort_m.set))

theorem pure_m {Γ Δ : SortContext signature_m} (R H : Term signature_m Γ Δ .set)
    (n : Term signature_m Γ Δ .num) (W : Term signature_m Γ Δ .set)
    (hR : pure_term_m R = true) (hH : pure_term_m H = true)
    (hn : pure_term_m n = true) (hW : pure_term_m W = true) :
    language_m (formula_m R H n W) = true := by
  have hTwice {s : sort_m} (t : Term signature_m Γ Δ s) (ht : pure_term_m t = true) :
      pure_term_m (t.weakenBound sort_m.set |>.weakenBound sort_m.set) = true :=
    (SecondOrderSubstitution.term_weaken_m (t.weakenBound sort_m.set) sort_m.set).trans
      ((SecondOrderSubstitution.term_weaken_m t sort_m.set).trans ht)
  change (language_m _ && (language_m _ && language_m _)) = true
  simp only [Bool.and_eq_true]
  refine ⟨?_, ?_, ?_⟩
  · apply SecondOrderRelationSpecification.pure_m _ _ _ SecondOrderPredecessorTaggedGraph.pure_m rfl
    intro s v
    match v with
    | .here => exact hTwice R hR
    | .there .here => exact hTwice H hH
    | .there (.there .here) => exact hTwice n hn
  · apply SecondOrderSetSpecification.pure_m _ _ _ SecondOrderPredecessorUnion.selector_pure_m rfl
    intro s v
    match v with
    | .here => exact hTwice R hR
    | .there .here => exact hTwice H hH
    | .there (.there .here) => exact hTwice n hn
  · apply SecondOrderRelationSpecification.pure_m _ _ _ SecondOrderGraft.pure_m (hTwice W hW)
    intro s v
    match v with
    | .here => rfl
    | .there .here => rfl

theorem formula_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext signature_m}
    (η : Env ℳ Γ Δ) (R H : Term signature_m Γ Δ .set) (n : Term signature_m Γ Δ .num)
    (W : Term signature_m Γ Δ .set) : (formula_m R H n W).satisfies η ↔
      SecondOrderPredecessorUnion.output_l (R.eval η) (H.eval η) (n.eval η) (W.eval η) := by
  simp only [formula_m, Formula.satisfies, graph_formula_l, selection_formula_l,
    SecondOrderMemberDefGraphFormula.graft_formula_l hℳ, Term.eval_weakenBound, Term.eval]
  constructor
  · rintro ⟨G, P, hG, hP, hW⟩
    exact ⟨G, P, hG, hP, hW⟩
  · rintro ⟨G, P, h⟩
    exact ⟨G, P, h.graph, h.selection, h.graft⟩

#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPredecessorUnionFormula
