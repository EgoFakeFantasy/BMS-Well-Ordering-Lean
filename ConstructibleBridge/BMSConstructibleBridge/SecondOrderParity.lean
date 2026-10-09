import BMSConstructibleBridge.SecondOrderDivision
import BMSConstructibleBridge.SecondOrderCompleteness

/-! # 全部内部自然数的奇偶分解

存在性由实际算术公式归纳；两分支的单射与不相交性由规范商余数唯一性。
既不要求数域外部标准，也不构造 Type 层的商余数选择函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderParity

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel SecondOrderNumbers

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def formula_m : Formula signature_m [] [.num] :=
  let q : Term signature_m [.num] [.num] .num := .bvar .here
  let d : Term signature_m [.num] [.num] .num := Term.app (σ := signature_m) .add (.cons q (.cons q .nil))
  .existsE .num (.disj (.equal (.fvar .here) d)
    (.equal (.fvar .here) (Term.app (σ := signature_m) .succ (.cons d .nil))))

theorem pure_m : language_m formula_m = true := pure_language_m _ rfl

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (n : num_l ℳ) :
    ∃ q, n = add_l q q ∨ n = succ_l (add_l q q) := by
  apply induct_l hℳ formula_m pure_m (Env.empty (M := ℳ))
    (fun n => ∃ q, n = add_l q q ∨ n = succ_l (add_l q q)) ?_ ?_ ?_ n
  · intro n
    simp only [formula_m, Formula.satisfies]
    rfl
  · exact ⟨zero_l ℳ, Or.inl (add_zero_l hℳ _).symm⟩
  · rintro n ⟨q, h | h⟩
    · exact ⟨q, Or.inr (congrArg succ_l h)⟩
    · refine ⟨succ_l q, Or.inl ?_⟩
      rw [h, add_succ_l hℳ, succ_add_l hℳ]

private theorem mul_two_l (hℳ : Theory.Models ℳ theory_m) (q : num_l ℳ) :
    mul_l q (succ_l (succ_l (zero_l ℳ))) = add_l q q := by
  rw [mul_succ_l hℳ, mul_succ_l hℳ, mul_zero_l hℳ, zero_add_l hℳ]

private theorem one_lt_two_l (hℳ : Theory.Models ℳ theory_m) :
    SecondOrderOrder.lt_l (succ_l (zero_l ℳ)) (succ_l (succ_l (zero_l ℳ))) :=
  (SecondOrderOrder.succ_iff_l hℳ _ _).mpr (SecondOrderOrder.zero_succ_l hℳ _)

theorem even_injective_l (hℳ : Theory.Models ℳ theory_m) {q r : num_l ℳ}
    (h : add_l q q = add_l r r) : q = r := by
  have hEq : add_l (mul_l q (succ_l (succ_l (zero_l ℳ)))) (zero_l ℳ) =
      add_l (mul_l r (succ_l (succ_l (zero_l ℳ)))) (zero_l ℳ) := by
    simpa only [mul_two_l hℳ, add_zero_l hℳ] using h
  exact (SecondOrderDivision.eq_l hℳ _ q (zero_l ℳ) r (zero_l ℳ) hEq
    (SecondOrderOrder.zero_succ_l hℳ _) (SecondOrderOrder.zero_succ_l hℳ _)).1

theorem odd_injective_l (hℳ : Theory.Models ℳ theory_m) {q r : num_l ℳ}
    (h : succ_l (add_l q q) = succ_l (add_l r r)) : q = r :=
  even_injective_l hℳ (injective_l hℳ h)

theorem disjoint_l (hℳ : Theory.Models ℳ theory_m) (q r : num_l ℳ) :
    add_l q q ≠ succ_l (add_l r r) := by
  intro h
  have hEq : add_l (mul_l q (succ_l (succ_l (zero_l ℳ)))) (zero_l ℳ) =
      add_l (mul_l r (succ_l (succ_l (zero_l ℳ)))) (succ_l (zero_l ℳ)) := by
    simpa only [mul_two_l hℳ, add_succ_l hℳ, add_zero_l hℳ] using h
  have hRem := (SecondOrderDivision.eq_l hℳ _ q (zero_l ℳ) r (succ_l (zero_l ℳ)) hEq
    (SecondOrderOrder.zero_succ_l hℳ _) (one_lt_two_l hℳ)).2
  exact nonzero_l hℳ (zero_l ℳ) hRem.symm

def sentence_m : Sentence signature_m :=
  let σ : Substitution signature_m [] [.num] [.num] [] :=
    .map (fun v => nomatch v) (fun {s} v => match s, v with
      | .num, .here => .bvar .here)
  .forallE .num (formula_m.substitute σ)

theorem derives_m : Derives theory_m [] sentence_m := by
  apply SecondOrderCompleteness.derives_m
  intro 𝒩 h𝒩
  simp only [sentence_m, Formula.TrueIn, Formula.satisfies, Formula.satisfies_substitute, formula_m]
  exact exists_l h𝒩

#print axioms exists_l
#print axioms disjoint_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderParity
