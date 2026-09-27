import BMSConstructibleBridge.SecondOrderProgramListFold

/-!
# 原折叠程序的剩余列表与终态

实际归纳公式逐步比较折叠状态的第一坐标和同一个原尾码迭代。无论累计更新程序
如何变化，剩余列表都恰好按取尾迭代前进；在准确长度步处必为空码。最终读取累计
坐标的折叠图因此等价于原状态迭代恰好到达 `pair 0 输出`。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramFoldState

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramListCode SecondOrderProgramListIteration
open SecondOrderProgramListLength SecondOrderProgramListShift SecondOrderProgramListFoldStep
open SecondOrderProgramIteration SecondOrderProgramListFold
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 自由槽 `[k,x,u,R,I]`：从初始状态 `u` 迭代后的状态有尾码 `I(x,k)` 作第一坐标。 -/
def state_invariant_m : Formula signature_m [] [.num, .num, .num, .set, .set] :=
  .existsE .num (.existsE .num (.existsE .num (.conj
    (output_m (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there .here)))
      (.fvar .here) (.bvar (.there (.there .here))))
    (.conj
      (output_m (.fvar (.there (.there (.there (.there .here))))) (.fvar (.there .here))
        (.fvar .here) (.bvar (.there .here)))
      (PrimitiveFormulas.pair_m (.bvar (.there .here)) (.bvar .here)
        (.bvar (.there (.there .here))))))))

/-- 状态不变量只有原纯算术符号和原图参数。 -/
theorem state_invariant_language_m : language_m state_invariant_m = true := pure_language_m _ rfl

/-- 状态不变量逐点解释为原迭代图上的边及同一配对坐标。 -/
theorem state_invariant_syntax_l (R I : set_l ℳ) (x u k : num_l ℳ) :
    Formula.satisfies ((((((Env.empty (M := ℳ)).pushFree I).pushFree R).pushFree u).pushFree x).pushFree k)
      state_invariant_m ↔ ∃ s t w, relation_l R (value_l u k) s ∧
        relation_l I (value_l x k) t ∧ value_l t w = s := by
  simp only [state_invariant_m, Formula.satisfies, output_syntax_l, SecondOrderPairing.formula_l]
  rfl

/-- 全部内部步数上的共同状态；只对实际公式作模型归纳。 -/
theorem state_invariant_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {R I : set_l ℳ}
    (hR : graph_semantics_l (graph_m (repeat_m (fold_step_m c))) R)
    (hI : graph_semantics_l (graph_m iterate_m) I) (x v k : num_l ℳ) :
    ∃ s t w, relation_l R (value_l (value_l x v) k) s ∧
      relation_l I (value_l x k) t ∧ value_l t w = s := by
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ (fold_step_m c)
  obtain ⟨C, hCf, hC⟩ := graph_total_l hℳ c
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ tail_m
  apply induct_l hℳ state_invariant_m state_invariant_language_m
    (((((Env.empty (M := ℳ)).pushFree I).pushFree R).pushFree (value_l x v)).pushFree x)
    (fun k => ∃ s t w, relation_l R (value_l (value_l x v) k) s ∧
      relation_l I (value_l x k) t ∧ value_l t w = s)
    (state_invariant_syntax_l R I x (value_l x v)) ?_ ?_ k
  · exact ⟨value_l x v, x, v,
      (repeat_zero_l hℳ (fold_step_m c) hR _ _).mpr rfl,
      (iterate_zero_l hℳ hI x x).mpr rfl, rfl⟩
  · rintro j ⟨s, t, w, hrs, hit, htw⟩
    subst s
    have hnext : ∃ r z, relation_l T t r ∧
        relation_l S (value_l t w) (value_l r z) := by
      rcases predecessor_l hℳ t with rfl | ⟨p, rfl⟩
      · exact ⟨zero_l ℳ, w, (tail_zero_l hℳ hT _).mpr rfl,
          (fold_step_zero_l hℳ c hS w _).mpr rfl⟩
      · obtain ⟨a, r, rfl⟩ := SecondOrderUnpairing.surjective_l hℳ p
        obtain ⟨z, hz, _⟩ := hCf (value_l w a)
        exact ⟨r, z, (tail_cons_l hℳ hT a r r).mpr rfl,
          (fold_step_cons_l hℳ c hS hC a r w (value_l r z)).mpr ⟨z, hz, rfl⟩⟩
    obtain ⟨r, z, htr, hsz⟩ := hnext
    exact ⟨value_l r z, r, z,
      (repeat_succ_l hℳ (fold_step_m c) hR hS _ j _).mpr ⟨value_l t w, hrs, hsz⟩,
      (iterate_succ_l hℳ hI hT x j r).mpr ⟨t, hit, htr⟩, rfl⟩

/-- 任意原折叠状态输出在准确长度步后第一坐标为空码。 -/
theorem terminal_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {R I : set_l ℳ}
    (hR : graph_semantics_l (graph_m (repeat_m (fold_step_m c))) R)
    (hI : graph_semantics_l (graph_m iterate_m) I) {x n : num_l ℳ}
    (hn : length_spec_l I x n) (v s : num_l ℳ)
    (hs : relation_l R (value_l (value_l x v) n) s) :
    ∃ w, s = value_l (zero_l ℳ) w := by
  obtain ⟨q, t, w, hq, ht, htw⟩ := state_invariant_l hℳ c hR hI x v n
  have ht0 := function_value_unique_l (function_of_semantics_l hℳ iterate_m hI) hn.1 ht
  have hqs := function_value_unique_l (function_of_semantics_l hℳ (repeat_m (fold_step_m c)) hR) hq hs
  exact ⟨w, hqs.symm.trans (htw.symm.trans (congrArg (fun t => value_l t w) ht0.symm))⟩

/-- 原折叠图的终态规格：输出正是准确长度处状态的第二坐标，第一坐标确定为零。 -/
theorem fold_state_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {F R I : set_l ℳ}
    (hF : graph_semantics_l (graph_m (fold_m c)) F)
    (hR : graph_semantics_l (graph_m (repeat_m (fold_step_m c))) R)
    (hI : graph_semantics_l (graph_m iterate_m) I) {x n : num_l ℳ}
    (hn : length_spec_l I x n) (v y : num_l ℳ) :
    relation_l F (value_l x v) y ↔
      relation_l R (value_l (value_l x v) n) (value_l (zero_l ℳ) y) := by
  obtain ⟨L, _, hL⟩ := graph_total_l hℳ SecondOrderProgramLength.length_m
  have hln := (SecondOrderProgramLength.length_rel_l hℳ hL hI x n).mpr hn
  rw [fold_at_length_l hℳ c hF hR hL x v n y hln]
  constructor
  · rintro ⟨s, hs, hy⟩
    obtain ⟨w, rfl⟩ := terminal_l hℳ c hR hI hn v s hs
    simp only [SecondOrderUnpairing.unpair_l] at hy
    exact hy ▸ hs
  · intro hy
    exact ⟨value_l (zero_l ℳ) y, hy, by rw [SecondOrderUnpairing.unpair_l]⟩

#print axioms state_invariant_m
#print axioms state_invariant_language_m
#print axioms state_invariant_syntax_l
#print axioms state_invariant_l
#print axioms terminal_l
#print axioms fold_state_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramFoldState
