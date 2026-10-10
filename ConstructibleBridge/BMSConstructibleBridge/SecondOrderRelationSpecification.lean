import BMSConstructibleBridge.SecondOrderRecursiveRelation

/-! # 任意参数二元关系的精确规格公式

统一把逐点正文实例化为实际关系图的全域方程。正文可以读取该图，也可以
读取独立参数；语法替换保留所有参数，不增加公理或新的求值约定。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelationSpecification

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def parameters_l {Γ Δ Ξ : SortContext signature_m} (η : Env ℳ Γ Ξ)
    (τ : VariableSubstitution signature_m Δ Γ Ξ) : Env ℳ [] Δ where
  boundVal := fun v => nomatch v
  freeVal := fun v => (τ v).eval η

private def bind_m {Γ Δ Ξ : SortContext signature_m}
    (x y : Term signature_m Γ Ξ .num) (τ : VariableSubstitution signature_m Δ Γ Ξ) :
    Substitution signature_m [] (.num :: .num :: Δ) Γ Ξ :=
  .map (fun v => nomatch v) (fun v => match v with
      | .here => x
      | .there .here => y
      | .there (.there v) => τ v)

def body_m {Γ Δ Ξ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: .num :: Δ))
    (x y : Term signature_m Γ Ξ .num) (τ : VariableSubstitution signature_m Δ Γ Ξ) :
    Formula signature_m Γ Ξ := φ.substitute (bind_m x y τ)

def formula_m {Γ Δ Ξ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: .num :: Δ))
    (F : Term signature_m Γ Ξ .set) (τ : VariableSubstitution signature_m Δ Γ Ξ) :
    Formula signature_m Γ Ξ :=
  .forallE .num <| .forallE .num <| .iff
    (GraphSyntax.edge_m (F.weakenBound sort_m.num |>.weakenBound sort_m.num) (.bvar (.there .here)) (.bvar .here))
    (body_m φ (.bvar (.there .here)) (.bvar .here)
      (fun v => (τ v).weakenBound sort_m.num |>.weakenBound sort_m.num))

theorem body_pure_m {Γ Δ Ξ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: .num :: Δ))
    (x y : Term signature_m Γ Ξ .num) (τ : VariableSubstitution signature_m Δ Γ Ξ)
    (hφ : language_m φ = true) (hx : pure_term_m x = true) (hy : pure_term_m y = true)
    (hτ : SecondOrderSubstitution.images_m τ) : language_m (body_m φ x y τ) = true := by
  refine (SecondOrderSubstitution.form_subst_m φ _ _ ?_ ?_).trans hφ
  · intro s v
    nomatch v
  · intro s v
    cases v with
    | here => exact hx
    | there v => cases v with
      | here => exact hy
      | there v => cases s <;> exact hτ v

theorem pure_m {Γ Δ Ξ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: .num :: Δ))
    (F : Term signature_m Γ Ξ .set) (τ : VariableSubstitution signature_m Δ Γ Ξ)
    (hφ : language_m φ = true) (hF : pure_term_m F = true)
    (hτ : SecondOrderSubstitution.images_m τ) : language_m (formula_m φ F τ) = true := by
  have hF' := (SecondOrderSubstitution.term_weaken_m (F.weakenBound sort_m.num) sort_m.num).trans
    ((SecondOrderSubstitution.term_weaken_m F sort_m.num).trans hF)
  have hEdge := pure_language_m _ (GraphSyntax.edge_pure_m _
    (Γ := .num :: .num :: Γ) (Δ := Ξ) (.bvar (.there .here)) (.bvar .here) hF' rfl rfl)
  have hBody := body_pure_m φ (Γ := .num :: .num :: Γ) (Ξ := Ξ)
    (.bvar (.there .here)) (.bvar .here)
    (fun v => (τ v).weakenBound sort_m.num |>.weakenBound sort_m.num) hφ rfl rfl
    (by
      intro s v
      exact (SecondOrderSubstitution.term_weaken_m ((τ v).weakenBound sort_m.num) sort_m.num).trans
        ((SecondOrderSubstitution.term_weaken_m (τ v) sort_m.num).trans (hτ v)))
  change (language_m _ && language_m _) = true
  rw [hEdge, hBody]
  rfl

theorem body_formula_l {Γ Δ Ξ : SortContext signature_m} (η : Env ℳ Γ Ξ)
    (φ : Formula signature_m [] (.num :: .num :: Δ))
    (x y : Term signature_m Γ Ξ .num) (τ : VariableSubstitution signature_m Δ Γ Ξ) :
    (body_m φ x y τ).satisfies η ↔
      φ.satisfies (((parameters_l η τ).pushFree (y.eval η)).pushFree (x.eval η)) := by
  rw [body_m, Formula.satisfies_substitute]
  apply Iff.of_eq
  apply congrArg (fun ξ => φ.satisfies ξ)
  apply Env.ext (bound := []) (fun {_} v => nomatch v)
  · intro s v
    cases v with
    | here => rfl
    | there v => cases v with
      | here => rfl
      | there v => cases s <;> rfl

theorem formula_l {Γ Δ Ξ : SortContext signature_m} (η : Env ℳ Γ Ξ)
    (φ : Formula signature_m [] (.num :: .num :: Δ))
    (F : Term signature_m Γ Ξ .set) (τ : VariableSubstitution signature_m Δ Γ Ξ) :
    (formula_m φ F τ).satisfies η ↔ ∀ x y, SecondOrderPairing.relation_l (F.eval η) x y ↔
      φ.satisfies (((parameters_l η τ).pushFree y).pushFree x) := by
  simp only [formula_m, Formula.satisfies, SecondOrderPairing.edge_l, body_formula_l,
    Term.eval_weakenBound, Term.eval]
  apply forall_congr'
  intro x
  apply forall_congr'
  intro y
  apply iff_congr Iff.rfl
  apply Iff.of_eq
  apply congrArg (fun ξ => φ.satisfies ξ)
  apply Env.ext (bound := []) (fun {_} v => nomatch v)
  · intro s v
    cases v with
    | here => rfl
    | there v => cases v with
      | here => rfl
      | there v =>
        change (Term.weakenBound sort_m.num (Term.weakenBound sort_m.num (τ v))).eval
          ((η.pushBound x).pushBound y) = (τ v).eval η
        rw [Term.eval_weakenBound, Term.eval_weakenBound]

#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelationSpecification
