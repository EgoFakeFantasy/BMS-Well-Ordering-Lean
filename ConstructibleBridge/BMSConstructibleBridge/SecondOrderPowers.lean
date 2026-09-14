import BMSConstructibleBridge.SecondOrderIteration

/-!
# 模型内部的幂函数图

先由纯公式理解乘以固定底数的图，再用已证内部迭代产生幂函数实数。
幂指数遍历模型全部数域；宿主选值只包装这个已存在且唯一的内部图。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPowers

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def spec_l (b : num_l ℳ) (E : set_l ℳ) : Prop :=
  function_l E ∧ relation_l E (zero_l ℳ) (succ_l (zero_l ℳ)) ∧
    ∀ i x y, relation_l E i x → relation_l E (succ_l i) y → y = mul_l x b

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (b : num_l ℳ) :
    ∃ E : set_l ℳ, spec_l b E := by
  let φ : Formula signature_m [] [.num, .num, .num] :=
    .equal (.fvar (.there .here))
      (Term.app (σ := signature_m) .mul
        (.cons (.fvar .here) (.cons (.fvar (.there (.there .here))) .nil)))
  obtain ⟨F, hF⟩ := SecondOrderRelations.comprehension_l hℳ φ (pure_language_m _ rfl)
    ((Env.empty (M := ℳ)).pushFree b)
  have h₁ : ∀ x y, relation_l F x y ↔ y = mul_l x b := fun x y => hF x y
  have h₂ : function_l F := fun x =>
    ⟨mul_l x b, (h₁ x _).mpr rfl, fun y hy => (h₁ x y).mp hy⟩
  obtain ⟨E, hE, h₀, h₃⟩ :=
    SecondOrderIteration.exists_l hℳ F (succ_l (zero_l ℳ)) h₂
  exact ⟨E, hE, h₀, fun i x y hx hy => (h₁ x y).mp (h₃ i x y hx hy)⟩

noncomputable def value_l {b : num_l ℳ} {E : set_l ℳ} (hE : spec_l b E)
    (n : num_l ℳ) : num_l ℳ := (hE.1 n).exists.choose

theorem edge_l {b : num_l ℳ} {E : set_l ℳ} (hE : spec_l b E) (n : num_l ℳ) :
    relation_l E n (value_l hE n) := (hE.1 n).exists.choose_spec

theorem eq_l {b : num_l ℳ} {E : set_l ℳ} (hE : spec_l b E) (n a : num_l ℳ) :
    relation_l E n a ↔ a = value_l hE n :=
  ⟨fun h => (hE.1 n).unique h (edge_l hE n), fun h => h ▸ edge_l hE n⟩

theorem zero_l {b : num_l ℳ} {E : set_l ℳ} (hE : spec_l b E) :
    value_l hE (SecondOrderModel.zero_l ℳ) = succ_l (SecondOrderModel.zero_l ℳ) :=
  (hE.1 _).unique (edge_l hE _) hE.2.1

theorem successor_l {b : num_l ℳ} {E : set_l ℳ} (hE : spec_l b E)
    (n : num_l ℳ) : value_l hE (succ_l n) = mul_l (value_l hE n) b :=
  hE.2.2 n _ _ (edge_l hE n) (edge_l hE (succ_l n))

/-- 两张满足幂递推方程的内部图在全部模型指数上相同。 -/
theorem unique_l (hℳ : Theory.Models ℳ theory_m) {b : num_l ℳ} {E F : set_l ℳ}
    (hE : spec_l b E) (hF : spec_l b F) : E = F := by
  let φ : Formula signature_m [] [.num, .set, .set] :=
    .forallE .num (.forallE .num (.imp
      (GraphSyntax.edge_m (.fvar (.there .here)) (.fvar .here) (.bvar (.there .here)))
      (.imp (GraphSyntax.edge_m (.fvar (.there (.there .here)))
        (.fvar .here) (.bvar .here)) (.equal (.bvar (.there .here)) (.bvar .here)))))
  have h : ∀ n, value_l hE n = value_l hF n := by
    apply induct_l hℳ φ (pure_language_m _ rfl)
      (((Env.empty (M := ℳ)).pushFree F).pushFree E)
      (fun n => value_l hE n = value_l hF n) ?_ ?_ ?_
    · intro n
      simp only [φ, Formula.satisfies, SecondOrderPairing.edge_l]
      change (∀ x y, relation_l E n x → relation_l F n y → x = y) ↔ _
      simp only [eq_l hE, eq_l hF, forall_eq, forall_eq_apply_imp_iff]
    · rw [zero_l hE, zero_l hF]
    · intro n hn
      rw [successor_l hE, successor_l hF, hn]
  apply SecondOrderRelations.ext_l hℳ
  intro n a
  rw [eq_l hE, eq_l hF, h n]

/-- 幂的加法公式由含三个图值的实际公式归纳，不使用外部指数递归。 -/
theorem add_l (hℳ : Theory.Models ℳ theory_m) {b : num_l ℳ} {E : set_l ℳ}
    (hE : spec_l b E) (m n : num_l ℳ) :
    value_l hE (SecondOrderModel.add_l m n) = mul_l (value_l hE m) (value_l hE n) := by
  letI := semiring_l hℳ
  let φ : Formula signature_m [] [.num, .num, .set] :=
    .forallE .num (.forallE .num (.forallE .num (.imp
      (GraphSyntax.edge_m (.fvar (.there (.there .here)))
        (.fvar (.there .here)) (.bvar (.there (.there .here))))
      (.imp (GraphSyntax.edge_m (.fvar (.there (.there .here)))
        (.fvar .here) (.bvar (.there .here)))
      (.imp (GraphSyntax.edge_m (.fvar (.there (.there .here)))
        (Term.app (σ := signature_m) .add
          (.cons (.fvar (.there .here)) (.cons (.fvar .here) .nil))) (.bvar .here))
        (.equal (.bvar .here) (Term.app (σ := signature_m) .mul
          (.cons (.bvar (.there (.there .here))) (.cons (.bvar (.there .here)) .nil)))))))))
  apply induct_l hℳ φ (pure_language_m _ rfl)
    (((Env.empty (M := ℳ)).pushFree E).pushFree m)
    (fun n => value_l hE (m + n) = value_l hE m * value_l hE n) ?_ ?_ ?_ n
  · intro n
    simp only [φ, Formula.satisfies, SecondOrderPairing.edge_l]
    change (∀ x y z, relation_l E m x → relation_l E n y →
      relation_l E (m + n) z → z = x * y) ↔ _
    simp only [eq_l hE]
    constructor
    · intro h
      exact h _ _ _ rfl rfl rfl
    · rintro h x y z rfl rfl rfl
      exact h
  · change value_l hE (m + 0) = value_l hE m * value_l hE (SecondOrderModel.zero_l ℳ)
    rw [zero_l hE]
    change value_l hE (m + 0) = value_l hE m * 1
    rw [add_zero, mul_one]
  · intro n hn
    change value_l hE (SecondOrderModel.add_l m (succ_l n)) = _
    rw [add_succ_l hℳ, successor_l hE, successor_l hE]
    change value_l hE (m + n) * b = value_l hE m * (value_l hE n * b)
    rw [hn, mul_assoc]

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPowers
