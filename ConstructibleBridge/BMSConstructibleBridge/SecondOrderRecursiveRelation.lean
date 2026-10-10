import BMSConstructibleBridge.SecondOrderRankedRecursionTheorem

/-!
# 逐点递归规则的内部关系解

实际规则公式的自由首三槽为编号、状态、前阶段关系，其余参数保持排序。
输出全域性由二元理解给出；使用者只需证明规则读取严格较小编号。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRecursiveRelation

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private def bind {Γ Δ : SortContext signature_m} (X : Term signature_m Γ Δ .set)
    (n a : Term signature_m Γ Δ .num) :
    Substitution signature_m [] (.num :: .num :: .set :: Δ) Γ Δ :=
  .map (fun v => nomatch v) (fun v => match v with
    | .here => n
    | .there .here => a
    | .there (.there .here) => X
    | .there (.there (.there v)) => .fvar v)

def body_m {Γ Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: .num :: .set :: Δ))
    (X : Term signature_m Γ Δ .set) (n a : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ := φ.substitute (bind X n a)

def rule_l {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: .num :: .set :: Δ)) (η : Env ℳ [] Δ)
    (X : set_l ℳ) (n a : num_l ℳ) : Prop :=
  Formula.satisfies (((η.pushFree X).pushFree a).pushFree n) φ

def parameters_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ) : Env ℳ [] Δ where
  boundVal := fun v => nomatch v
  freeVal := η.freeVal

theorem body_pure_m {Γ Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: .num :: .set :: Δ))
    (X : Term signature_m Γ Δ .set) (n a : Term signature_m Γ Δ .num)
    (hφ : language_m φ = true) (hX : pure_term_m X = true)
    (hn : pure_term_m n = true) (ha : pure_term_m a = true) : language_m (body_m φ X n a) = true := by
  refine (SecondOrderSubstitution.form_subst_m φ _ _ ?_ ?_).trans hφ
  · intro s v
    nomatch v
  · intro s v
    match v with
    | .here => exact hn
    | .there .here => exact ha
    | .there (.there .here) => exact hX
    | .there (.there (.there v)) => cases s <;> rfl

theorem body_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (φ : Formula signature_m [] (.num :: .num :: .set :: Δ))
    (X : Term signature_m Γ Δ .set) (n a : Term signature_m Γ Δ .num) :
    Formula.satisfies η (body_m φ X n a) ↔
      rule_l φ (parameters_l η) (X.eval η) (n.eval η) (a.eval η) := by
  rw [body_m, Formula.satisfies_substitute]
  apply Iff.of_eq
  apply congrArg (fun η => Formula.satisfies η φ)
  apply Env.ext (bound := []) (fun {_} v => nomatch v)
  · intro s v
    match v with
    | .here => rfl
    | .there .here => rfl
    | .there (.there .here) => rfl
    | .there (.there (.there v)) => cases s <;> rfl

def operator_m {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: .num :: .set :: Δ)) : Formula signature_m [.set, .set] Δ :=
  .forallE .num (.forallE .num (.iff
    (GraphSyntax.edge_m (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))
    (body_m φ (.bvar (.there (.there (.there .here)))) (.bvar (.there .here)) (.bvar .here))))

theorem pure_m {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: .num :: .set :: Δ)) (hφ : language_m φ = true) :
    language_m (operator_m φ) = true := by
  change (language_m (GraphSyntax.edge_m (Γ := [.num, .num, .set, .set]) (Δ := Δ)
    (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)) &&
    language_m (body_m φ (.bvar (.there (.there (.there .here)))) (.bvar (.there .here)) (.bvar .here))) = true
  rw [body_pure_m φ _ _ _ hφ rfl rfl rfl, Bool.and_true]
  rfl

theorem operator_l {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: .num :: .set :: Δ)) (η : Env ℳ [] Δ) (X Y : set_l ℳ) :
    SecondOrderSetOperator.relation_l (operator_m φ) η X Y ↔
      ∀ n a, SecondOrderPairing.relation_l Y n a ↔ rule_l φ η X n a := by
  simp only [SecondOrderSetOperator.relation_l, operator_m, Formula.satisfies,
    SecondOrderPairing.edge_l, body_l]
  change (∀ n a, SecondOrderPairing.relation_l Y n a ↔ rule_l φ (parameters_l η) X n a) ↔ _
  have h : parameters_l η = η := by
    apply Env.ext (bound := []) (fun {_} v => nomatch v)
    · intro s v
      rfl
  rw [h]

theorem total_l (hℳ : Theory.Models ℳ theory_m) {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: .num :: .set :: Δ)) (hφ : language_m φ = true)
    (η : Env ℳ [] Δ) (X : set_l ℳ) :
    ∃ Y, SecondOrderSetOperator.relation_l (operator_m φ) η X Y := by
  obtain ⟨Y, hY⟩ := SecondOrderRelations.comprehension_l hℳ φ hφ (η.pushFree X)
  exact ⟨Y, (operator_l φ η X Y).mpr hY⟩

theorem exists_l (hℳ : Theory.Models ℳ theory_m) {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: .num :: .set :: Δ)) (hφ : language_m φ = true)
    (η : Env ℳ [] Δ)
    (hφ₀ : ∀ X Y n, SecondOrderInitialAgreement.agree_l X Y n →
      ∀ a, rule_l φ η X n a ↔ rule_l φ η Y n a) :
    ∃! S, ∀ n a, SecondOrderPairing.relation_l S n a ↔ rule_l φ η S n a := by
  have h : SecondOrderRankedStability.local_l (SecondOrderSetOperator.relation_l (operator_m φ) η) := by
    intro X Y U V hU hV n hn a
    exact ((operator_l φ η X U).mp hU n a).trans
      ((hφ₀ X Y n hn a).trans ((operator_l φ η Y V).mp hV n a).symm)
  obtain ⟨S, hS, hU⟩ := SecondOrderRankedRecursion.exists_l hℳ (operator_m φ) (pure_m φ hφ) η
    (total_l hℳ φ hφ η) h
  exact ⟨S, (operator_l φ η S S).mp hS, fun T hT => hU T ((operator_l φ η T T).mpr hT)⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRecursiveRelation
