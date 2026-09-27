import BMSConstructibleBridge.SecondOrderProgramListCounter

/-!
# 原计数程序与内部长度的对应

设 `n` 是原尾迭代首次归零的步数。实际归纳公式断言：第 `k` 步的累计值在
`k ≤ n` 时是 `k`，在 `n ≤ k` 时是 `n`。此分段不变量只含原纯算术符号与图参数，
因此归纳适用于任意模型内部步数，而非仅适用于外部标准数码。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCountCorrectness

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramListIteration SecondOrderProgramListLength
open SecondOrderProgramListShift SecondOrderProgramListStops SecondOrderProgramListCounter
open PrimitiveProgram (eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 分段计数的实际归纳公式；自由槽 `[k, x, n, C]`。 -/
def count_invariant_m : Formula signature_m [] [.num, .num, .num, .set] :=
  .disj
    (.conj
      (.disj (.equal (.fvar .here) (.fvar (.there (.there .here))))
        (PrimitiveFormulas.lt_m (.fvar .here) (.fvar (.there (.there .here)))))
      (output_m (.fvar (.there (.there (.there .here)))) (.fvar (.there .here))
        (.fvar .here) (.fvar .here)))
    (.conj
      (.disj (.equal (.fvar (.there (.there .here))) (.fvar .here))
        (PrimitiveFormulas.lt_m (.fvar (.there (.there .here))) (.fvar .here)))
      (output_m (.fvar (.there (.there (.there .here)))) (.fvar (.there .here))
        (.fvar .here) (.fvar (.there (.there .here)))))

/-- 分段不变量属于原纯算术语言。 -/
theorem count_invariant_language_m : language_m count_invariant_m = true := pure_language_m _ rfl

/-- 实际公式的真值精确对应内部线序上的分段规格。 -/
theorem count_invariant_syntax_l (hℳ : Theory.Models ℳ theory_m) (C : set_l ℳ)
    (x n k : num_l ℳ) :
    letI := order_l hℳ
    Formula.satisfies (((((Env.empty (M := ℳ)).pushFree C).pushFree n).pushFree x).pushFree k)
      count_invariant_m ↔
      (k ≤ n ∧ relation_l C (value_l x k) k) ∨ (n ≤ k ∧ relation_l C (value_l x k) n) := by
  letI := order_l hℳ
  simp only [count_invariant_m, Formula.satisfies, output_syntax_l, SecondOrderOrder.formula_l]
  rfl

/-- 真实公式归纳：到归零阈值前每步加一，达到阈值后保持不变。 -/
theorem count_invariant_l (hℳ : Theory.Models ℳ theory_m) {C I : set_l ℳ}
    (hC : graph_semantics_l (graph_m count_m) C)
    (hI : graph_semantics_l (graph_m iterate_m) I) {x n : num_l ℳ}
    (hn : length_spec_l I x n) (k : num_l ℳ) :
    letI := order_l hℳ
    (k ≤ n ∧ relation_l C (value_l x k) k) ∨ (n ≤ k ∧ relation_l C (value_l x k) n) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  obtain ⟨N, _, hN⟩ := graph_total_l hℳ SecondOrderProgramNonzero.nonzero_m
  apply induct_l hℳ count_invariant_m count_invariant_language_m
    ((((Env.empty (M := ℳ)).pushFree C).pushFree n).pushFree x)
    (fun k => (k ≤ n ∧ relation_l C (value_l x k) k) ∨
      (n ≤ k ∧ relation_l C (value_l x k) n))
    (count_invariant_syntax_l hℳ C x n) ?_ ?_ k
  · exact Or.inl ⟨zero_le_l hℳ n, (count_zero_l hℳ hC x (zero_l ℳ)).mpr rfl⟩
  · intro j hj
    by_cases hjn : j < n
    · have hc : relation_l C (value_l x j) j := by
        rcases hj with ⟨_, hc⟩ | ⟨hnj, _⟩
        · exact hc
        · exact False.elim ((not_le_of_gt hjn) hnj)
      obtain ⟨w, hw, _⟩ := function_of_semantics_l hℳ iterate_m hI (value_l x j)
      have hw0 : w ≠ zero_l ℳ := fun h => hn.2 j hjn (h ▸ hw)
      have hadd : add_l j (numeral_val_l 1) = succ_l j := by
        change add_l j (succ_l (zero_l ℳ)) = succ_l j
        rw [add_succ_l hℳ, add_zero_l hℳ]
      refine Or.inl ⟨?_, (count_succ_l hℳ hC hI hN x j (succ_l j)).mpr
        ⟨j, w, numeral_val_l 1, hc, hw,
          (SecondOrderProgramNonzero.positive_l hℳ hN hw0 _).mpr rfl, hadd⟩⟩
      rw [succ_eq_l hℳ]
      exact (lt_iff_add_one_le_l hℳ j n).mp hjn
    · have hnj : n ≤ j := le_of_not_gt hjn
      have hc : relation_l C (value_l x j) n := by
        rcases hj with ⟨hjn, hc⟩ | ⟨_, hc⟩
        · exact (le_antisymm hjn hnj) ▸ hc
        · exact hc
      refine Or.inr ⟨le_trans hnj (le_of_lt (lt_own_succ_l hℳ j)), ?_⟩
      exact (count_succ_l hℳ hC hI hN x j n).mpr
        ⟨n, zero_l ℳ, zero_l ℳ, hc, (stops_iff_l hℳ hI hn j).mpr hnj,
          (SecondOrderProgramNonzero.zero_l hℳ hN _).mpr rfl, add_zero_l hℳ n⟩

/-- 在任意达到长度的内部预算处，原计数程序已经返回准确长度。 -/
theorem count_at_bound_l (hℳ : Theory.Models ℳ theory_m) {C I : set_l ℳ}
    (hC : graph_semantics_l (graph_m count_m) C)
    (hI : graph_semantics_l (graph_m iterate_m) I) {x n k : num_l ℳ}
    (hn : length_spec_l I x n) :
    letI := order_l hℳ
    n ≤ k → relation_l C (value_l x k) n := by
  letI := order_l hℳ
  intro hnk
  rcases count_invariant_l hℳ hC hI hn k with ⟨hkn, hc⟩ | ⟨_, hc⟩
  · exact (le_antisymm hkn hnk) ▸ hc
  · exact hc

/-- 原列表编码上的标准计数恰为预算与列表长度的最小值。 -/
theorem count_encode_l (s : List Nat) (k : Nat) :
    eval_l count_m (Nat.pair (Encodable.encode s) k) = min k s.length := by
  rw [count_m, PrimitiveProgram.prec_l]
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [PrimitiveHistory.run_l] at ih ⊢
      rw [step_eval_l, ih]
      split_ifs with h
      · have hk := (stops_encode_l s k).mp h
        omega
      · have hk : ¬s.length ≤ k := fun hk => h ((stops_encode_l s k).mpr hk)
        omega

#print axioms count_invariant_m
#print axioms count_invariant_language_m
#print axioms count_invariant_syntax_l
#print axioms count_invariant_l
#print axioms count_at_bound_l
#print axioms count_encode_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCountCorrectness
