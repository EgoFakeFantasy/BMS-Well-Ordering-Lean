import BMSConstructibleBridge.SecondOrderCanonicalMemberDefGraph
import BMSConstructibleBridge.SecondOrderCanonicalGraftFormula
import BMSConstructibleBridge.SecondOrderSetSpecification

/-! # Def 输出图的切片、筛选与拼接公式

三项均约束原模型中的实际实数；完整原图边规格与旧良基切片接口分开，
避免把只在有效节点上成立的语义对应当作整个实数的唯一性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberDefGraphFormula

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def layer_m {Γ Δ : SortContext signature_m} (A F : Term signature_m Γ Δ .set)
    (r : Term signature_m Γ Δ .num) (G : Term signature_m Γ Δ .set) : Formula signature_m Γ Δ :=
  SecondOrderRelationSpecification.formula_m SecondOrderSubsetLayer.formula_m G
    (fun v => match v with | .here => A | .there .here => F | .there (.there .here) => r)

def selection_m {Γ Δ : SortContext signature_m} (V E P : Term signature_m Γ Δ .set) : Formula signature_m Γ Δ :=
  SecondOrderSetSpecification.formula_m
    (SecondOrderSelectedSubsetCollection.selector_m SecondOrderLegalFormulaIndex.formula_m) P
    (fun v => match v with | .here => V | .there .here => E)

def graft_m {Γ Δ : SortContext signature_m} (G P W : Term signature_m Γ Δ .set) : Formula signature_m Γ Δ :=
  SecondOrderRelationSpecification.formula_m SecondOrderGraft.formula_m W
    (fun v => match v with | .here => G | .there .here => P)

private theorem layer_env_l (η : Env ℳ [] [.num, .num, .set, .set, .num]) :
    SecondOrderSubsetLayer.formula_m.satisfies η ↔ SecondOrderCanonicalSubsetLayer.edge_l
      (η.freeVal (.there (.there .here))) (η.freeVal (.there (.there (.there .here))))
      (η.freeVal (.there (.there (.there (.there .here))))) (η.freeVal .here) (η.freeVal (.there .here)) := by
  have hη : η = ((((((Env.empty (M := ℳ)).pushFree (η.freeVal (.there (.there (.there (.there .here)))))).pushFree
      (η.freeVal (.there (.there (.there .here))))).pushFree (η.freeVal (.there (.there .here)))).pushFree
      (η.freeVal (.there .here))).pushFree (η.freeVal .here)) := by
    apply Env.ext (bound := []) (fun {_} v => nomatch v)
    · intro s v
      match v with
      | .here => rfl
      | .there .here => rfl
      | .there (.there .here) => rfl
      | .there (.there (.there .here)) => rfl
      | .there (.there (.there (.there .here))) => rfl
  conv_lhs => rw [hη]
  exact SecondOrderCanonicalSubsetLayer.formula_l _ _ _ _ _

private theorem graft_env_l (η : Env ℳ [] [.num, .num, .set, .set]) :
    SecondOrderGraft.formula_m.satisfies η ↔ ∃ a, η.freeVal .here = succ_l a ∧
      ((η.freeVal (.there .here) = zero_l ℳ ∧ mem_l a (η.freeVal (.there (.there (.there .here))))) ∨
        ∃ b, η.freeVal (.there .here) = succ_l b ∧
          SecondOrderPairing.relation_l (η.freeVal (.there (.there .here))) a b) := by
  simp only [SecondOrderGraft.formula_m, Formula.satisfies, SecondOrderPairing.edge_l]
  rfl

private theorem selection_env_l (η : Env ℳ [] [.num, .set, .set]) :
    (SecondOrderSelectedSubsetCollection.selector_m SecondOrderLegalFormulaIndex.formula_m).satisfies η ↔
      ∃ i, SecondOrderSubsetLayer.root_l i = η.freeVal .here ∧
        SecondOrderLegalFormulaIndex.spec_l (η.freeVal (.there .here)) (η.freeVal (.there (.there .here))) i := by
  let ρ := ((Env.empty (M := ℳ)).pushFree (η.freeVal (.there (.there .here)))).pushFree (η.freeVal (.there .here))
  have hη : η = ρ.pushFree (η.freeVal .here) := by
    apply Env.ext (bound := []) (fun {_} v => nomatch v)
    · intro s v
      match v with
      | .here => rfl
      | .there .here => rfl
      | .there (.there .here) => rfl
  conv_lhs => rw [hη]
  refine (SecondOrderSelectedSubsetCollection.selector_l _ ρ _).trans ?_
  exact exists_congr (fun i => and_congr Iff.rfl (SecondOrderLegalFormulaIndex.formula_l _))

theorem layer_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (A F : Term signature_m Γ Δ .set) (r : Term signature_m Γ Δ .num) (G : Term signature_m Γ Δ .set) :
    (layer_m A F r G).satisfies η ↔
      SecondOrderCanonicalSubsetLayer.spec_l (A.eval η) (F.eval η) (r.eval η) (G.eval η) := by
  simp only [layer_m, SecondOrderRelationSpecification.formula_l, layer_env_l]
  rfl

theorem selection_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (V E P : Term signature_m Γ Δ .set) : (selection_m V E P).satisfies η ↔
      ∀ c, mem_l c (P.eval η) ↔ ∃ i, SecondOrderSubsetLayer.root_l i = c ∧
        SecondOrderLegalFormulaIndex.spec_l (V.eval η) (E.eval η) i := by
  simp only [selection_m, SecondOrderSetSpecification.formula_l, selection_env_l]
  rfl

theorem graft_formula_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (G P W : Term signature_m Γ Δ .set) : (graft_m G P W).satisfies η ↔
      SecondOrderGraft.spec_l (G.eval η) (P.eval η) (W.eval η) := by
  refine Iff.trans ?_ (SecondOrderCanonicalGraftFormula.iff_l hℳ _ _ _)
  simp only [graft_m, SecondOrderRelationSpecification.formula_l, graft_env_l]
  rfl

#print axioms layer_formula_l
#print axioms graft_formula_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberDefGraphFormula
