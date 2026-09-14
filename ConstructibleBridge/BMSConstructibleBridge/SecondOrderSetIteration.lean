import BMSConstructibleBridge.SecondOrderSetHistory

/-!
# 可定义且输出唯一的集合值迭代

用实际公式归纳比较内部有限历史，再通过历史存在公式理解整张阶段图。
唯一性是合并所必需的前提；本模块不证明任意集合关系的可数依赖选择。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSetIteration

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def spec_l (P : set_l ℳ → set_l ℳ → Prop) (G A : set_l ℳ) : Prop :=
  SecondOrderSections.spec_l G (zero_l ℳ) A ∧ ∀ i X Y,
    SecondOrderSections.spec_l G i X → SecondOrderSections.spec_l G (succ_l i) Y → P X Y

private def succ {Γ Δ : SortContext signature_m} (s : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num := Term.app (σ := signature_m) .succ (.cons s .nil)

theorem compatible_l (hℳ : Theory.Models ℳ theory_m) (P : set_l ℳ → set_l ℳ → Prop)
    (H K A : set_l ℳ) (n m : num_l ℳ) (hP : ∀ X Y Z, P X Y → P X Z → Y = Z)
    (hH : SecondOrderSetHistory.spec_l P H A n) (hK : SecondOrderSetHistory.spec_l P K A m)
    (i : num_l ℳ) : SecondOrderOrder.lt_l i (succ_l n) → SecondOrderOrder.lt_l i (succ_l m) →
      ∀ a, relation_l H i a ↔ relation_l K i a := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  let φ : Formula signature_m [] [.num, .num, .num, .set, .set] :=
    .imp (PrimitiveFormulas.lt_m (.fvar .here) (succ (.fvar (.there .here))))
      (.imp (PrimitiveFormulas.lt_m (.fvar .here) (succ (.fvar (.there (.there .here)))))
        (.forallE .num (.iff
          (GraphSyntax.edge_m (.fvar (.there (.there (.there .here)))) (.fvar .here) (.bvar .here))
          (GraphSyntax.edge_m (.fvar (.there (.there (.there (.there .here))))) (.fvar .here) (.bvar .here)))))
  have h₀ (j : num_l ℳ) : j < succ_l j := (SecondOrderNaturalGraph.lt_succ_l hℳ _ _).mpr le_rfl
  apply induct_l hℳ φ (pure_language_m _ rfl)
    (((((Env.empty (M := ℳ)).pushFree K).pushFree H).pushFree m).pushFree n)
    (fun i => i < succ_l n → i < succ_l m → ∀ a, relation_l H i a ↔ relation_l K i a) ?_ ?_ ?_ i
  · intro i
    simp only [φ, Formula.satisfies, SecondOrderOrder.formula_l, SecondOrderPairing.edge_l]
    rfl
  · intro _ _ a
    exact (hH.1 a).symm.trans (hK.1 a)
  · intro i hi hn hm a
    have hn₁ := (SecondOrderOrder.succ_iff_l hℳ i n).mp hn
    have hm₁ := (SecondOrderOrder.succ_iff_l hℳ i m).mp hm
    obtain ⟨X, hX⟩ := SecondOrderSections.exists_l hℳ H i
    obtain ⟨Y, hY⟩ := SecondOrderSections.exists_l hℳ K i
    have h : X = Y := ext_l hℳ X Y (fun b =>
      (hX b).trans ((hi (lt_trans hn₁ (h₀ n)) (lt_trans hm₁ (h₀ m)) b).trans (hY b).symm))
    subst Y
    obtain ⟨U, hU⟩ := SecondOrderSections.exists_l hℳ H (succ_l i)
    obtain ⟨V, hV⟩ := SecondOrderSections.exists_l hℳ K (succ_l i)
    obtain rfl := hP X U V (hH.2 i X U hn₁ hX hU) (hK.2 i X V hm₁ hY hV)
    exact (hU a).symm.trans (hV a)

private def bind {Δ : SortContext signature_m} :
    Substitution signature_m [] (.set :: .set :: .num :: Δ) [.set] (.num :: .num :: .set :: Δ) :=
  .map (fun v => nomatch v) (fun v => match v with
    | .here => .bvar .here
    | .there .here => .fvar (.there (.there .here))
    | .there (.there .here) => .fvar .here
    | .there (.there (.there v)) => .fvar (.there (.there (.there v))))

def formula_m {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ) :
    Formula signature_m [] (.num :: .num :: .set :: Δ) :=
  .existsE .set (.conj ((SecondOrderSetHistory.formula_m φ).substitute bind)
    (GraphSyntax.edge_m (.bvar .here) (.fvar .here) (.fvar (.there .here))))

theorem pure_m {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ)
    (hφ : language_m φ = true) : language_m (formula_m φ) = true := by
  have h : language_m ((SecondOrderSetHistory.formula_m φ).substitute (bind (Δ := Δ))) = true := by
    refine (SecondOrderSubstitution.form_subst_m _ _ _ ?_ ?_).trans (SecondOrderSetHistory.pure_m φ hφ)
    · intro s v
      nomatch v
    · intro s v
      match v with
      | .here | .there .here | .there (.there .here) => rfl
      | .there (.there (.there _)) => cases s <;> rfl
  change (language_m ((SecondOrderSetHistory.formula_m φ).substitute bind) && true) = true
  rw [h]
  rfl

theorem graph_l (hℳ : Theory.Models ℳ theory_m) {Δ : SortContext signature_m}
    (φ : Formula signature_m [.set, .set] Δ) (hφ : language_m φ = true) (η : Env ℳ [] Δ)
    (A : set_l ℳ) : ∃ G : set_l ℳ, ∀ i a, relation_l G i a ↔
      ∃ H, SecondOrderSetHistory.spec_l (SecondOrderSetOperator.relation_l φ η) H A i ∧ relation_l H i a := by
  obtain ⟨G, hG⟩ := SecondOrderRelations.comprehension_l hℳ (formula_m φ) (pure_m φ hφ) (η.pushFree A)
  refine ⟨G, fun i a => (hG i a).trans ?_⟩
  simp only [formula_m, Formula.satisfies, SecondOrderPairing.edge_l]
  change (∃ H, Formula.satisfies ((((η.pushFree A).pushFree a).pushFree i).pushBound H)
    ((SecondOrderSetHistory.formula_m φ).substitute bind) ∧ relation_l H i a) ↔ _
  apply exists_congr
  intro H
  rw [Formula.satisfies_substitute, SecondOrderSetHistory.formula_l]
  have h : SecondOrderSetHistory.parameters_l
      ((((η.pushFree A).pushFree a).pushFree i).pushBound H |>.pullback (bind (Δ := Δ))) = η := by
    apply Env.ext
    · intro s v
      nomatch v
    · intro s v
      cases s <;> rfl
  rw [h]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ theory_m) {Δ : SortContext signature_m}
    (φ : Formula signature_m [.set, .set] Δ) (hφ : language_m φ = true) (η : Env ℳ [] Δ)
    (A : set_l ℳ) (hP : ∀ X, ∃ Y, SecondOrderSetOperator.relation_l φ η X Y)
    (hU : ∀ X Y Z, SecondOrderSetOperator.relation_l φ η X Y →
      SecondOrderSetOperator.relation_l φ η X Z → Y = Z) :
    ∃ G, spec_l (SecondOrderSetOperator.relation_l φ η) G A := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  obtain ⟨G, hG⟩ := graph_l hℳ φ hφ η A
  have h₀ (i : num_l ℳ) : i < succ_l i := (SecondOrderNaturalGraph.lt_succ_l hℳ _ _).mpr le_rfl
  have h (i : num_l ℳ) (H : set_l ℳ)
      (hH : SecondOrderSetHistory.spec_l (SecondOrderSetOperator.relation_l φ η) H A i) :
      ∀ a, relation_l G i a ↔ relation_l H i a := by
    intro a
    constructor
    · intro ha
      obtain ⟨K, hK, ha⟩ := (hG i a).mp ha
      exact (compatible_l hℳ _ K H A i i hU hK hH i (h₀ i) (h₀ i) a).mp ha
    · intro ha
      exact (hG i a).mpr ⟨H, hH, ha⟩
  refine ⟨G, ?_, ?_⟩
  · obtain ⟨H, hH⟩ := SecondOrderSetHistory.exists_l hℳ φ hφ η A hP (zero_l ℳ)
    exact fun a => (hH.1 a).trans (h _ H hH a).symm
  · intro i X Y hX hY
    obtain ⟨H, hH⟩ := SecondOrderSetHistory.exists_l hℳ φ hφ η A hP (succ_l i)
    have hH₁ : SecondOrderSetHistory.spec_l (SecondOrderSetOperator.relation_l φ η) H A i :=
      ⟨hH.1, fun j U V hj => hH.2 j U V (lt_trans hj (h₀ i))⟩
    exact hH.2 i X Y (h₀ i) (fun a => (hX a).trans (h i H hH₁ a))
      (fun a => (hY a).trans (h (succ_l i) H hH a))

theorem unique_l (hℳ : Theory.Models ℳ theory_m) (P : set_l ℳ → set_l ℳ → Prop)
    (G K A : set_l ℳ) (hP : ∀ X Y Z, P X Y → P X Z → Y = Z)
    (hG : spec_l P G A) (hK : spec_l P K A) : G = K := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  apply SecondOrderRelations.ext_l hℳ
  intro i a
  have hi : i < succ_l i := (SecondOrderNaturalGraph.lt_succ_l hℳ _ _).mpr le_rfl
  exact compatible_l hℳ P G K A i i hP ⟨hG.1, fun j X Y _ => hG.2 j X Y⟩
    ⟨hK.1, fun j X Y _ => hK.2 j X Y⟩ i hi hi a

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSetIteration
