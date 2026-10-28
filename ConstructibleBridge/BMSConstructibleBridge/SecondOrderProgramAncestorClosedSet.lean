import BMSConstructibleBridge.SecondOrderProgramAncestorBudget
import BMSConstructibleBridge.SecondOrderProgramAncestorMembership
import BMSConstructibleBridge.SecondOrderProgramListAll

/-!
# 父查询封闭的内部集合包含全部祖先

集合S在从初始列b或S中元素取父节点时封闭。实际迭代中当前列始终是b或S中元素，
累计表全部属于S；反转与真实成员查询保持此性质。归纳正文明确使用模型内部集合S，
不把任意宿主谓词当作可用的归纳实例，也不要求b本身属于S。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorClosedSet

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramIteration
open SecondOrderProgramAncestorStep (step_m)
open SecondOrderProgramAncestorTransition (step_none_l step_some_l)
open SecondOrderProgramAncestorBudget (state_m state_syntax_l)
open SecondOrderProgramAncestorChain (chain_m chain_rel_l)
open SecondOrderProgramAncestorMembership (member_m member_nonzero_l)
open SecondOrderProgramListAll
open SecondOrderProgramListShift (output_m output_syntax_l length_cons_l)
open SecondOrderProgramListLength (length_zero_l)
open SecondOrderProgramLength (length_m length_rel_l)
open SecondOrderProgramListIteration (iterate_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramListReverse (reverse_m reverse_step_m)
open SecondOrderProgramListReverseEntries (reverse_length_l)
open SecondOrderProgramListFold (fold_m)
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 实际状态与真实长度，以及当前列和全部有效累计条目的集合性质。 -/
def kept_l (R L E S : set_l ℳ) (s x b n : num_l ℳ) : Prop := ∃ u t v m,
  relation_l R (value_l s n) u ∧ value_l x (value_l t v) = u ∧ relation_l L v m ∧
    (t = b ∨ mem_l t S) ∧ all_l E S v m

/-- 自由槽[n,s,x,b,R,L,E,S]，依次绑定状态u、当前列t、累计码v、长度m。 -/
def kept_m : Formula signature_m [] [.num, .num, .num, .num, .set, .set, .set, .set] :=
  .existsE .num (.existsE .num (.existsE .num (.existsE .num (.conj
    (output_m (.fvar (.there (.there (.there (.there .here))))) (.fvar (.there .here)) (.fvar .here)
      (.bvar (.there (.there (.there .here)))))
    (.conj (state_m (.fvar (.there (.there .here))) (.bvar (.there (.there .here)))
      (.bvar (.there .here)) (.bvar (.there (.there (.there .here)))))
      (.conj (GraphSyntax.edge_m (.fvar (.there (.there (.there (.there (.there .here))))))
        (.bvar (.there .here)) (.bvar .here))
        (.conj (.disj (.equal (.bvar (.there (.there .here))) (.fvar (.there (.there (.there .here)))))
          (.rel .mem (.cons (.bvar (.there (.there .here)))
            (.cons (.fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil))))
          (all_m (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
            (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
            (.bvar (.there .here)) (.bvar .here)))))))))

/-- 归纳正文属于原纯二阶算术语言。 -/
theorem kept_language_m : language_m kept_m = true := pure_language_m _ rfl

/-- 真正的公式解释不改变迭代图、初始列或内部集合。 -/
theorem kept_syntax_l (R L E S : set_l ℳ) (s x b n : num_l ℳ) :
    Formula.satisfies (((((((((Env.empty (M := ℳ)).pushFree S).pushFree E).pushFree L).pushFree R).pushFree b).pushFree x).pushFree s).pushFree n)
      kept_m ↔ kept_l R L E S s x b n := by
  simp only [kept_m, kept_l, Formula.satisfies, output_syntax_l, state_syntax_l,
    SecondOrderPairing.edge_l, all_syntax_l, Arguments.eval]
  rfl

/-- 对实际封闭的内部集合，任意内部步数都保持当前列与累计表性质。 -/
theorem kept_invariant_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {R L E C S : set_l ℳ}
    (hR : graph_semantics_l (graph_m (repeat_m (step_m c))) R)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hC : graph_semantics_l (graph_m c) C) (x b n : num_l ℳ)
    (hparent : ∀ t p, (t = b ∨ mem_l t S) → relation_l C (value_l x t) (succ_l p) → mem_l p S) :
    kept_l R L E S (value_l x (value_l b (zero_l ℳ))) x b n := by
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ (step_m c)
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  apply induct_l hℳ kept_m kept_language_m
    ((((((((Env.empty (M := ℳ)).pushFree S).pushFree E).pushFree L).pushFree R).pushFree b).pushFree x).pushFree
      (value_l x (value_l b (zero_l ℳ))))
    (fun n => kept_l R L E S (value_l x (value_l b (zero_l ℳ))) x b n)
    (kept_syntax_l R L E S (value_l x (value_l b (zero_l ℳ))) x b) ?_ ?_ n
  · exact ⟨_, b, zero_l ℳ, zero_l ℳ,
      (repeat_zero_l hℳ (step_m c) hR _ _).mpr rfl, rfl,
      (length_rel_l hℳ hL hI _ _).mpr ((length_zero_l hℳ hI _).mpr rfl),
      Or.inl rfl, all_zero_l hℳ E S _⟩
  · rintro j ⟨u, t, v, m, hr, he, hl, ht, hv⟩
    subst u
    obtain ⟨q, hq, _⟩ := function_of_semantics_l hℳ c hC (value_l x t)
    rcases predecessor_l hℳ q with rfl | ⟨p, rfl⟩
    · exact ⟨_, t, v, m,
        (repeat_succ_l hℳ (step_m c) hR hT _ j _).mpr
          ⟨_, hr, (step_none_l hℳ c hT hC hq v _).mpr rfl⟩, rfl, hl, ht, hv⟩
    · have hp := hparent t p ht hq
      exact ⟨_, p, succ_l (value_l p v), succ_l m,
        (repeat_succ_l hℳ (step_m c) hR hT _ j _).mpr
          ⟨_, hr, (step_some_l hℳ c hT hC hq v _).mpr rfl⟩, rfl,
        (length_rel_l hℳ hL hI _ _).mpr
          ((length_cons_l hℳ hI p v m).mpr ((length_rel_l hℳ hL hI v m).mp hl)),
        Or.inr hp, all_cons_l hℳ hE hp hv⟩

/-- 函数性把共同存在的不变量传到任意给定实际迭代输出。 -/
theorem output_kept_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {R L E C S : set_l ℳ}
    (hR : graph_semantics_l (graph_m (repeat_m (step_m c))) R)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hC : graph_semantics_l (graph_m c) C) {x b n u : num_l ℳ}
    (hparent : ∀ t p, (t = b ∨ mem_l t S) → relation_l C (value_l x t) (succ_l p) → mem_l p S)
    (hu : relation_l R (value_l (value_l x (value_l b (zero_l ℳ))) n) u) :
    ∃ t v m, u = value_l x (value_l t v) ∧ relation_l L v m ∧
      (t = b ∨ mem_l t S) ∧ all_l E S v m := by
  obtain ⟨s, t, v, m, hs, he, hl, ht, hv⟩ := kept_invariant_l hℳ c hR hL hE hC x b n hparent
  have hsu := function_value_unique_l (function_of_semantics_l hℳ (repeat_m (step_m c)) hR) hs hu
  exact ⟨t, v, m, hsu.symm.trans he.symm, hl, ht, hv⟩

/-- 实际最终链只反转累计表，因而其全部有效条目仍属于同一内部集合。 -/
theorem chain_all_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {A L E C S : set_l ℳ}
    (hA : graph_semantics_l (graph_m (chain_m c)) A)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hC : graph_semantics_l (graph_m c) C) {x b fuel y n : num_l ℳ}
    (hparent : ∀ t p, (t = b ∨ mem_l t S) → relation_l C (value_l x t) (succ_l p) → mem_l p S)
    (hy : relation_l A (value_l (value_l x b) fuel) y) (hn : relation_l L y n) : all_l E S y n := by
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ (repeat_m (step_m c))
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ reverse_m
  obtain ⟨F, _, hF⟩ := graph_total_l hℳ (fold_m reverse_step_m)
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  obtain ⟨s, hs, hsy⟩ := (chain_rel_l hℳ c hA hR hT x b fuel y).mp hy
  obtain ⟨t, v, m, rfl, hlv, _, hv⟩ := output_kept_l hℳ c hR hL hE hC hparent hs
  simp only [SecondOrderUnpairing.unpair_l] at hsy
  have hym := reverse_length_l hℳ hT hF hL hI v y m hsy hlv
  have hmn := function_value_unique_l (function_of_semantics_l hℳ length_m hL) hym hn
  exact hmn ▸ all_reverse_l hℳ hT hL hE hsy hlv hv

/-- 成员程序为真时，候选确实属于父查询封闭的内部集合。 -/
theorem member_mem_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {M C S : set_l ℳ}
    (hM : graph_semantics_l (graph_m (member_m c)) M)
    (hC : graph_semantics_l (graph_m c) C) {x b i : num_l ℳ}
    (hparent : ∀ t p, (t = b ∨ mem_l t S) → relation_l C (value_l x t) (succ_l p) → mem_l p S)
    (hi : ¬relation_l M (value_l (value_l x b) i) (zero_l ℳ)) : mem_l i S := by
  obtain ⟨A, hAf, hA⟩ := graph_total_l hℳ (chain_m c)
  obtain ⟨L, hLf, hL⟩ := graph_total_l hℳ length_m
  obtain ⟨E, _, hE⟩ := graph_total_l hℳ lookup_m
  obtain ⟨v, hv, _⟩ := hAf (value_l (value_l x b) b)
  obtain ⟨n, hn, _⟩ := hLf v
  obtain ⟨j, hj, hji⟩ := (member_nonzero_l hℳ c hM hA hL hE hv hn i).mp hi
  exact chain_all_l hℳ c hA hL hE hC hparent hv hn j hj i hji

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorClosedSet
