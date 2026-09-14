import BMSConstructibleBridge.SecondOrderNumbers
import BMSConstructibleBridge.PrimitiveFormulas

/-!
# 模型内部数序与实际小于公式

正差定义使用模型自身的加法和后继。三歧性由带数量词的实际公式归纳推出，
不是给非标准数域假定一个宿主良序实例。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrder

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel SecondOrderNumbers

set_option autoImplicit false

universe u

def lt_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m} (m n : num_l ℳ) : Prop :=
  ∃ k, add_l m (succ_l k) = n

/-- 原来的实际纯加乘小于模板，在任意模型中都表示模型内部的正差关系。 -/
theorem formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ) (s t : Term signature_m Γ Δ .num) :
    Formula.satisfies η (PrimitiveFormulas.lt_m s t) ↔ lt_l (s.eval η) (t.eval η) := by
  change (∃ d : num_l ℳ,
    add_l ((s.weakenBound sort_m.num).eval (η.pushBound d)) (succ_l d) =
      (t.weakenBound sort_m.num).eval (η.pushBound d)) ↔ _
  simp only [Term.eval_weakenBound]
  rfl

theorem irrefl_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (m : num_l ℳ) : ¬lt_l m m := by
  rintro ⟨k, h⟩
  have h₁ : add_l m (succ_l k) = add_l m (zero_l ℳ) := h.trans (add_zero_l hℳ m).symm
  exact nonzero_l hℳ k ((add_cancel_l hℳ m _ _).mp h₁)

theorem succ_iff_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (m n : num_l ℳ) : lt_l (succ_l m) (succ_l n) ↔ lt_l m n := by
  unfold lt_l
  apply exists_congr
  intro k
  rw [succ_add_l hℳ, (injective_l hℳ).eq_iff]

theorem zero_succ_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (m : num_l ℳ) : lt_l (zero_l ℳ) (succ_l m) :=
  ⟨m, zero_add_l hℳ _⟩

theorem trans_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) {m n p : num_l ℳ} (h : lt_l m n) (h₁ : lt_l n p) : lt_l m p := by
  obtain ⟨a, rfl⟩ := h
  obtain ⟨b, rfl⟩ := h₁
  refine ⟨add_l a (succ_l b), ?_⟩
  rw [add_assoc_l hℳ, succ_add_l hℳ]

theorem trichotomy_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (m n : num_l ℳ) : lt_l m n ∨ m = n ∨ lt_l n m := by
  let s : Term signature_m [.num] [.num] .num := .fvar .here
  let t : Term signature_m [.num] [.num] .num := .bvar .here
  let φ : Formula signature_m [] [.num] := .forallE .num
    (.disj (PrimitiveFormulas.lt_m s t) (.disj (.equal s t) (PrimitiveFormulas.lt_m t s)))
  have hφ : language_m φ = true := by
    have h₀ := pure_language_m _ (PrimitiveFormulas.lt_pure_l s t rfl rfl)
    have h₁ := pure_language_m _ (PrimitiveFormulas.lt_pure_l t s rfl rfl)
    change (language_m (PrimitiveFormulas.lt_m s t) &&
      (true && language_m (PrimitiveFormulas.lt_m t s))) = true
    rw [h₀, h₁]
    rfl
  have hP (m : num_l ℳ) : Formula.satisfies ((Env.empty (M := ℳ)).pushFree m) φ ↔
      ∀ n : num_l ℳ, lt_l m n ∨ m = n ∨ lt_l n m := by
    simp only [φ, Formula.satisfies, formula_l]
    rfl
  apply induct_l hℳ φ hφ Env.empty
    (fun m => ∀ n, lt_l m n ∨ m = n ∨ lt_l n m) hP ?_ ?_ m n
  · intro n
    rcases predecessor_l hℳ n with rfl | ⟨n, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl (zero_succ_l hℳ n)
  · intro m h n
    rcases predecessor_l hℳ n with rfl | ⟨n, rfl⟩
    · exact Or.inr (Or.inr (zero_succ_l hℳ m))
    · rcases h n with h | h | h
      · exact Or.inl ((succ_iff_l hℳ m n).mpr h)
      · exact Or.inr (Or.inl (congrArg succ_l h))
      · exact Or.inr (Or.inr ((succ_iff_l hℳ n m).mpr h))

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrder
