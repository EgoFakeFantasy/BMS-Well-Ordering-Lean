import BMSConstructibleBridge.SecondOrderRankedStability

/-!
# 沿内部数值编号的唯一递归解

求值操作若全域、可定义且每行只依赖较小编号，就有唯一的内部固定点。
从阶段图取对角线，不引入外部良基性或额外递归公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRankedRecursion

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderInitialAgreement SecondOrderRankedStability

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem diagonal_l (hℳ : Theory.Models ℳ theory_m) (G : set_l ℳ) :
    ∃ S : set_l ℳ, ∀ n a, relation_l S n a ↔ ∃ X,
      SecondOrderSections.spec_l G (succ_l n) X ∧ relation_l X n a := by
  let φ : Formula signature_m [] [.num, .num, .set] :=
    .existsE .set (.conj
      (SecondOrderSections.formula_m (.fvar (.there (.there .here))) (.bvar .here)
        (Term.app (σ := signature_m) .succ (.cons (.fvar .here) .nil)))
      (GraphSyntax.edge_m (.bvar .here) (.fvar .here) (.fvar (.there .here))))
  obtain ⟨S, hS⟩ := SecondOrderRelations.comprehension_l hℳ φ rfl ((Env.empty (M := ℳ)).pushFree G)
  refine ⟨S, fun n a => (hS n a).trans ?_⟩
  simp only [φ, Formula.satisfies, SecondOrderSections.formula_l, SecondOrderPairing.edge_l]
  rfl

theorem row_l (hℳ : Theory.Models ℳ theory_m) (G S : set_l ℳ)
    (hS : ∀ n a, relation_l S n a ↔ ∃ X, SecondOrderSections.spec_l G (succ_l n) X ∧ relation_l X n a)
    (n : num_l ℳ) (Y : set_l ℳ) (hY : SecondOrderSections.spec_l G (succ_l n) Y) (a : num_l ℳ) :
    relation_l S n a ↔ relation_l Y n a := by
  refine (hS n a).trans ?_
  constructor
  · rintro ⟨X, hX, h⟩
    exact (SecondOrderSections.unique_l hℳ hX hY) ▸ h
  · intro h
    exact ⟨Y, hY, h⟩

theorem agree_l (hℳ : Theory.Models ℳ theory_m) (P : set_l ℳ → set_l ℳ → Prop)
    (G A S : set_l ℳ) (hG : SecondOrderSetIteration.spec_l P G A) (hP : local_l P)
    (hS : ∀ n a, relation_l S n a ↔ ∃ X, SecondOrderSections.spec_l G (succ_l n) X ∧ relation_l X n a)
    (n : num_l ℳ) (X : set_l ℳ) (hX : SecondOrderSections.spec_l G n X) :
    SecondOrderInitialAgreement.agree_l S X n := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  intro i hi a
  obtain ⟨Y, hY⟩ := SecondOrderSections.exists_l hℳ G (succ_l i)
  have hn : succ_l i ≤ n := by
    rw [succ_eq_l hℳ]
    exact (lt_iff_add_one_le_l hℳ i n).mp hi
  have h := stages_l hℳ P G A hG hP (succ_l i) (succ_l i) n Y X le_rfl hn hY hX
  exact (row_l hℳ G S hS i Y hY a).trans
    (h i ((SecondOrderNaturalGraph.lt_succ_l hℳ _ _).mpr le_rfl) a)

theorem output_unique_l (hℳ : Theory.Models ℳ theory_m) (P : set_l ℳ → set_l ℳ → Prop)
    (hP : local_l P) (X U V : set_l ℳ) (hU : P X U) (hV : P X V) : U = V := by
  apply SecondOrderRelations.ext_l hℳ
  intro n a
  exact hP X X U V hU hV n (fun _ _ _ => Iff.rfl) a

theorem unique_l (hℳ : Theory.Models ℳ theory_m) (P : set_l ℳ → set_l ℳ → Prop)
    (hP : local_l P) (S T : set_l ℳ) (hS : P S S) (hT : P T T) : S = T := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  apply SecondOrderInitialAgreement.ext_l hℳ S T
  let φ : Formula signature_m [] [.num, .set, .set] :=
    SecondOrderInitialAgreement.formula_m (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)
  apply induct_l hℳ φ (SecondOrderInitialAgreement.pure_m _ _ _ rfl rfl rfl)
    (((Env.empty (M := ℳ)).pushFree T).pushFree S)
    (SecondOrderInitialAgreement.agree_l S T) ?_ ?_ ?_
  · intro n
    exact SecondOrderInitialAgreement.formula_l _ _ _ _
  · intro i hi
    exact False.elim ((not_lt_of_ge (zero_le_l hℳ i)) hi)
  · intro n hn
    exact (SecondOrderInitialAgreement.successor_l hℳ S T n).mpr ⟨hn, hP S T S T hS hT n hn⟩

/-- 实际可定义、全域且局部的操作有唯一内部解；唯一输出由局部性推出。 -/
theorem exists_l (hℳ : Theory.Models ℳ theory_m) {Δ : SortContext signature_m}
    (φ : Formula signature_m [.set, .set] Δ) (hφ : language_m φ = true) (η : Env ℳ [] Δ)
    (hT : ∀ X, ∃ Y, SecondOrderSetOperator.relation_l φ η X Y)
    (hP : local_l (SecondOrderSetOperator.relation_l φ η)) :
    ∃! S, SecondOrderSetOperator.relation_l φ η S S := by
  obtain ⟨A, _⟩ := comprehension_l hℳ (Formula.falsum : Formula signature_m [] [.num]) rfl Env.empty
  obtain ⟨G, hG⟩ := SecondOrderSetIteration.exists_l hℳ φ hφ η A hT (output_unique_l hℳ _ hP)
  obtain ⟨S, hS⟩ := diagonal_l hℳ G
  obtain ⟨D, hD⟩ := hT S
  have h : D = S := by
    apply SecondOrderRelations.ext_l hℳ
    intro n a
    obtain ⟨X, hX⟩ := SecondOrderSections.exists_l hℳ G n
    obtain ⟨Y, hY⟩ := SecondOrderSections.exists_l hℳ G (succ_l n)
    exact (hP S X D Y hD (hG.2 n X Y hX hY) n (agree_l hℳ _ G A S hG hP hS n X hX) a).trans
      (row_l hℳ G S hS n Y hY a).symm
  subst D
  exact ⟨S, hD, fun T hT => unique_l hℳ _ hP T S hT hD⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRankedRecursion
