import BMSConstructibleBridge.SecondOrderOrdinalHierarchy
import BMSConstructibleBridge.SecondOrderSetSpecification
import BMSConstructibleBridge.SecondOrderFormulaArguments

/-! # 实际序数根呈现的完整对象正文

相等图、最小数代表域和规范前驱图均绑定为原实数的精确规格。
原始数值参数顺序由类型化替换保存，非法节点也保留相等图的全域方程。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRootPresentationFormula

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def equality_m {Γ Δ : SortContext signature_m} (A Q : Term signature_m Γ Δ .set) : Formula signature_m Γ Δ :=
  .forallE .num <| .forallE .num <| .iff
    (GraphSyntax.edge_m (Q.weakenBound sort_m.num |>.weakenBound sort_m.num) (.bvar (.there .here)) (.bvar .here))
    (GraphTranslation.atom_m GraphSyntax.eq_m
      (A.weakenBound sort_m.num |>.weakenBound sort_m.num)
      (A.weakenBound sort_m.num |>.weakenBound sort_m.num) (.bvar (.there .here)) (.bvar .here))

def representative_bind_m {Γ Δ : SortContext signature_m} (A Q : Term signature_m Γ Δ .set)
    (r : Term signature_m Γ Δ .num) : VariableSubstitution signature_m [.set, .num, .set] Γ Δ :=
  fun v => match v with | .here => A | .there .here => r | .there (.there .here) => Q

def representatives_m {Γ Δ : SortContext signature_m} (A Q D : Term signature_m Γ Δ .set)
    (r : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  SecondOrderSetSpecification.formula_m SecondOrderRootRepresentatives.formula_m D (representative_bind_m A Q r)

def predecessor_bind_m {Γ Δ : SortContext signature_m} (A Q D : Term signature_m Γ Δ .set) :
    VariableSubstitution signature_m [.set, .set, .set] Γ Δ :=
  fun v => match v with | .here => D | .there .here => A | .there (.there .here) => Q

def predecessors_m {Γ Δ : SortContext signature_m} (A Q D R : Term signature_m Γ Δ .set) : Formula signature_m Γ Δ :=
  SecondOrderRelationSpecification.formula_m SecondOrderRootOrdinalRelation.formula_m R (predecessor_bind_m A Q D)

def formula_m {Γ Δ : SortContext signature_m} (A : Term signature_m Γ Δ .set)
    (r : Term signature_m Γ Δ .num) (Q D R : Term signature_m Γ Δ .set) : Formula signature_m Γ Δ :=
  .conj (equality_m A Q) (.conj (representatives_m A Q D r) (predecessors_m A Q D R))

theorem equality_pure_m {Γ Δ : SortContext signature_m} (A Q : Term signature_m Γ Δ .set)
    (hA : pure_term_m A = true) (hQ : pure_term_m Q = true) : language_m (equality_m A Q) = true := by
  have hTwice (t : Term signature_m Γ Δ .set) (ht : pure_term_m t = true) :
      pure_term_m (t.weakenBound sort_m.num |>.weakenBound sort_m.num) = true :=
    (SecondOrderSubstitution.term_weaken_m (t.weakenBound sort_m.num) sort_m.num).trans
      ((SecondOrderSubstitution.term_weaken_m t sort_m.num).trans ht)
  have hEdge := pure_language_m _ (GraphSyntax.edge_pure_m
    (Q.weakenBound sort_m.num |>.weakenBound sort_m.num) (Γ := .num :: .num :: Γ)
    (.bvar (.there .here)) (.bvar .here) (hTwice Q hQ) rfl rfl)
  have hEqual := GraphTranslation.atom_pure_m GraphSyntax.eq_m
    (A.weakenBound sort_m.num |>.weakenBound sort_m.num)
    (A.weakenBound sort_m.num |>.weakenBound sort_m.num) (.bvar (.there .here)) (.bvar .here)
    (pure_language_m GraphSyntax.matrix_m GraphSyntax.matrix_pure_m) (hTwice A hA) (hTwice A hA) rfl rfl
  exact SecondOrderFormulaArguments.forall_pure_m .num _
    (SecondOrderFormulaArguments.forall_pure_m .num _
      (SecondOrderFormulaArguments.conj_pure_m _ _ hEdge hEqual))

theorem pure_m {Γ Δ : SortContext signature_m} (A : Term signature_m Γ Δ .set)
    (r : Term signature_m Γ Δ .num) (Q D R : Term signature_m Γ Δ .set)
    (hA : pure_term_m A = true) (hr : pure_term_m r = true) (hQ : pure_term_m Q = true)
    (hD : pure_term_m D = true) (hR : pure_term_m R = true) : language_m (formula_m A r Q D R) = true := by
  have hRep := SecondOrderSetSpecification.pure_m SecondOrderRootRepresentatives.formula_m D
    (representative_bind_m A Q r) SecondOrderRootRepresentatives.pure_m hD
    (by intro s v; match v with | .here => exact hA | .there .here => exact hr | .there (.there .here) => exact hQ)
  have hPred := SecondOrderRelationSpecification.pure_m SecondOrderRootOrdinalRelation.formula_m R
    (predecessor_bind_m A Q D) SecondOrderRootOrdinalRelation.pure_m hR
    (by intro s v; match v with | .here => exact hD | .there .here => exact hA | .there (.there .here) => exact hQ)
  exact SecondOrderFormulaArguments.conj_pure_m _ _ (equality_pure_m A Q hA hQ)
    (SecondOrderFormulaArguments.conj_pure_m _ _ hRep hPred)

theorem equality_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (A Q : Term signature_m Γ Δ .set) : (equality_m A Q).satisfies η ↔
      ∀ i j, SecondOrderPairing.relation_l (Q.eval η) i j ↔
        SecondOrderBisimulation.eq_l (A.eval η) (A.eval η) i j := by
  simp only [equality_m, Formula.satisfies, SecondOrderPairing.edge_l, SecondOrderInterpretation.eq_l,
    Term.eval_weakenBound, Term.eval]
  rfl

private theorem representative_env_l (η : Env ℳ [] [.num, .set, .num, .set]) :
    SecondOrderRootRepresentatives.formula_m.satisfies η ↔ SecondOrderRootRepresentatives.representative_l
      (η.freeVal (.there .here)) (η.freeVal (.there (.there (.there .here))))
      (η.freeVal (.there (.there .here))) (η.freeVal .here) := by
  have hη : η = (((((Env.empty (M := ℳ)).pushFree (η.freeVal (.there (.there (.there .here))))).pushFree
      (η.freeVal (.there (.there .here)))).pushFree (η.freeVal (.there .here))).pushFree (η.freeVal .here)) := by
    apply Env.ext
    · intro s v; nomatch v
    · intro s v; match v with
      | .here => rfl
      | .there .here => rfl
      | .there (.there .here) => rfl
      | .there (.there (.there .here)) => rfl
  conv_lhs => rw [hη]
  exact SecondOrderRootRepresentatives.formula_l _ _ _ _

theorem representatives_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (A Q D : Term signature_m Γ Δ .set) (r : Term signature_m Γ Δ .num) :
    (representatives_m A Q D r).satisfies η ↔ SecondOrderRootRepresentatives.spec_l (A.eval η) (Q.eval η) (D.eval η) (r.eval η) := by
  rw [representatives_m, SecondOrderSetSpecification.formula_l]
  simp only [representative_env_l]
  rfl

private theorem predecessor_env_l (η : Env ℳ [] [.num, .num, .set, .set, .set]) :
    SecondOrderRootOrdinalRelation.formula_m.satisfies η ↔ SecondOrderRootOrdinalRelation.edge_l
      (η.freeVal (.there (.there (.there .here)))) (η.freeVal (.there (.there (.there (.there .here)))))
      (η.freeVal (.there (.there .here))) (η.freeVal .here) (η.freeVal (.there .here)) := by
  have hη : η = ((((((Env.empty (M := ℳ)).pushFree (η.freeVal (.there (.there (.there (.there .here)))))).pushFree
      (η.freeVal (.there (.there (.there .here))))).pushFree (η.freeVal (.there (.there .here)))).pushFree
      (η.freeVal (.there .here))).pushFree (η.freeVal .here)) := by
    apply Env.ext
    · intro s v; nomatch v
    · intro s v; match v with
      | .here => rfl
      | .there .here => rfl
      | .there (.there .here) => rfl
      | .there (.there (.there .here)) => rfl
      | .there (.there (.there (.there .here))) => rfl
  conv_lhs => rw [hη]
  exact SecondOrderRootOrdinalRelation.formula_l _ _ _ _ _

theorem predecessors_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (A Q D R : Term signature_m Γ Δ .set) : (predecessors_m A Q D R).satisfies η ↔
      SecondOrderRootOrdinalRelation.spec_l (A.eval η) (Q.eval η) (D.eval η) (R.eval η) := by
  rw [predecessors_m, SecondOrderRelationSpecification.formula_l]
  simp only [predecessor_env_l]
  rfl

theorem formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ) (A : Term signature_m Γ Δ .set)
    (r : Term signature_m Γ Δ .num) (Q D R : Term signature_m Γ Δ .set)
    (hA : SecondOrderDomain.wf_l (A.eval η) (r.eval η)) : (formula_m A r Q D R).satisfies η ↔
      SecondOrderOrdinalHierarchy.presentation_l ⟨A.eval η, r.eval η, hA⟩ (Q.eval η) (D.eval η) (R.eval η) := by
  simp only [formula_m, Formula.satisfies, equality_formula_l, representatives_formula_l, predecessors_formula_l]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.equality, h.representatives, h.predecessors⟩⟩

#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRootPresentationFormula
