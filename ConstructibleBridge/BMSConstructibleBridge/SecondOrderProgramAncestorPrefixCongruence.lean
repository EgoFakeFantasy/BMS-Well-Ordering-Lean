import BMSConstructibleBridge.SecondOrderProgramAncestorIterationCongruence
import BMSConstructibleBridge.SecondOrderProgramAncestorOrder
import BMSConstructibleBridge.SecondOrderProgramAncestorMembership

/-!
# 祖先链只依赖起始列左侧的父查询

父查询在给定内部前缀内一致，且源父边严格向左，则从该前缀内出发的两次原祖先
迭代始终同步。复用实际coupled_m归纳公式及已证源当前列界，不对内部fuel作外部归纳，
也不要求前缀外查询一致。初始累计器固定为原chain实际使用的空码。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorPrefixCongruence

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions
open SecondOrderProgramSemantics SecondOrderProgramTotality SecondOrderProgramArithmetic
open SecondOrderProgramIteration
open SecondOrderProgramAncestorStep (step_m)
open SecondOrderProgramAncestorTransition (step_none_l step_some_l)
open SecondOrderProgramAncestorIterationCongruence (coupled_l coupled_m coupled_language_m coupled_syntax_l)
open SecondOrderProgramAncestorChain (chain_m chain_rel_l)
open SecondOrderProgramAncestorMembership (member_m member_rel_of_value_l)
open SecondOrderProgramListReverse (reverse_m)
open SecondOrderProgramListContains (contains_m)
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 界内父查询对应已足够同步任意内部fuel后的原状态；不会访问前缀外的查询。 -/
theorem common_state_l (hℳ : Theory.Models ℳ theory_m) (c d : code_m) {C D R U : set_l ℳ}
    (hC : graph_semantics_l (graph_m c) C) (hD : graph_semantics_l (graph_m d) D)
    (hR : graph_semantics_l (graph_m (repeat_m (step_m c))) R)
    (hU : graph_semantics_l (graph_m (repeat_m (step_m d))) U) (x z b : num_l ℳ)
    (hdown : ∀ j p, relation_l C (value_l x j) (succ_l p) → SecondOrderOrder.lt_l p j)
    (hparent : ∀ j, SecondOrderOrder.lt_l j b → ∀ q,
      relation_l C (value_l x j) q ↔ relation_l D (value_l z j) q)
    {k : num_l ℳ} (hk : SecondOrderOrder.lt_l k b) (n : num_l ℳ) : ∃ t w,
    relation_l R (value_l (value_l x (value_l k (zero_l ℳ))) n) (value_l x (value_l t w)) ∧
      relation_l U (value_l (value_l z (value_l k (zero_l ℳ))) n) (value_l z (value_l t w)) := by
  letI := order_l hℳ
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ (step_m c)
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ (step_m d)
  obtain ⟨L, _, hL⟩ := graph_total_l hℳ SecondOrderProgramLength.length_m
  obtain ⟨E, _, hE⟩ := graph_total_l hℳ SecondOrderProgramListLookup.lookup_m
  have hcoupled : coupled_l R U (value_l x (value_l k (zero_l ℳ)))
      (value_l z (value_l k (zero_l ℳ))) x z n := by
    apply induct_l hℳ coupled_m coupled_language_m
      (((((((Env.empty (M := ℳ)).pushFree U).pushFree R).pushFree z).pushFree x).pushFree
        (value_l z (value_l k (zero_l ℳ)))).pushFree (value_l x (value_l k (zero_l ℳ))))
      (fun n => coupled_l R U (value_l x (value_l k (zero_l ℳ)))
        (value_l z (value_l k (zero_l ℳ))) x z n)
      (coupled_syntax_l R U (value_l x (value_l k (zero_l ℳ)))
        (value_l z (value_l k (zero_l ℳ))) x z) ?_ ?_ n
    · exact ⟨k, zero_l ℳ, _, _, rfl, rfl,
        (repeat_zero_l hℳ (step_m c) hR _ _).mpr rfl,
        (repeat_zero_l hℳ (step_m d) hU _ _).mpr rfl⟩
    · rintro j ⟨t, w, a, a', ha, ha', hr, hu⟩
      subst a
      subst a'
      obtain ⟨t', w', m, he, _, htk, _⟩ :=
        SecondOrderProgramAncestorOrder.output_order_l hℳ c hR hL hE hC hdown hr
      have htt := (SecondOrderPairingBounds.injective_l hℳ t w t' w'
        (SecondOrderPairingBounds.injective_l hℳ x (value_l t w) x (value_l t' w') he).2).1
      have htb : t < b := by
        rw [htt]
        exact lt_of_le_of_lt (show t' ≤ k from htk) hk
      obtain ⟨q, hq, _⟩ := function_of_semantics_l hℳ c hC (value_l x t)
      have hd := (hparent t htb q).mp hq
      rcases predecessor_l hℳ q with rfl | ⟨p, rfl⟩
      · exact ⟨t, w, _, _, rfl, rfl,
          (repeat_succ_l hℳ (step_m c) hR hS _ j _).mpr
            ⟨_, hr, (step_none_l hℳ c hS hC hq w _).mpr rfl⟩,
          (repeat_succ_l hℳ (step_m d) hU hT _ j _).mpr
            ⟨_, hu, (step_none_l hℳ d hT hD hd w _).mpr rfl⟩⟩
      · exact ⟨p, succ_l (value_l p w), _, _, rfl, rfl,
          (repeat_succ_l hℳ (step_m c) hR hS _ j _).mpr
            ⟨_, hr, (step_some_l hℳ c hS hC hq w _).mpr rfl⟩,
          (repeat_succ_l hℳ (step_m d) hU hT _ j _).mpr
            ⟨_, hu, (step_some_l hℳ d hT hD hd w _).mpr rfl⟩⟩
  obtain ⟨t, w, a, a', ha, ha', hr, hu⟩ := hcoupled
  subst a
  subst a'
  exact ⟨t, w, hr, hu⟩

/-- 从前缀内出发，原chain同一内部fuel的完整输出码相同，不只是成员真值相同。 -/
theorem chain_congr_l (hℳ : Theory.Models ℳ theory_m) (c d : code_m) {C D A B : set_l ℳ}
    (hC : graph_semantics_l (graph_m c) C) (hD : graph_semantics_l (graph_m d) D)
    (hA : graph_semantics_l (graph_m (chain_m c)) A)
    (hB : graph_semantics_l (graph_m (chain_m d)) B) (x z b : num_l ℳ)
    (hdown : ∀ j p, relation_l C (value_l x j) (succ_l p) → SecondOrderOrder.lt_l p j)
    (hparent : ∀ j, SecondOrderOrder.lt_l j b → ∀ q,
      relation_l C (value_l x j) q ↔ relation_l D (value_l z j) q)
    {k : num_l ℳ} (hk : SecondOrderOrder.lt_l k b) (n y : num_l ℳ) :
    relation_l A (value_l (value_l x k) n) y ↔ relation_l B (value_l (value_l z k) n) y := by
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ (repeat_m (step_m c))
  obtain ⟨U, _, hU⟩ := graph_total_l hℳ (repeat_m (step_m d))
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ reverse_m
  obtain ⟨a, v, hr, hu⟩ := common_state_l hℳ c d hC hD hR hU x z b hdown hparent hk n
  constructor
  · intro hy
    obtain ⟨s, hs, ht⟩ := (chain_rel_l hℳ c hA hR hT x k n y).mp hy
    have he := function_value_unique_l (function_of_semantics_l hℳ (repeat_m (step_m c)) hR) hr hs
    rw [← he] at ht
    simp only [SecondOrderUnpairing.unpair_l] at ht
    exact (chain_rel_l hℳ d hB hU hT z k n y).mpr
      ⟨_, hu, by simpa only [SecondOrderUnpairing.unpair_l] using ht⟩
  · intro hy
    obtain ⟨s, hs, ht⟩ := (chain_rel_l hℳ d hB hU hT z k n y).mp hy
    have he := function_value_unique_l (function_of_semantics_l hℳ (repeat_m (step_m d)) hU) hu hs
    rw [← he] at ht
    simp only [SecondOrderUnpairing.unpair_l] at ht
    exact (chain_rel_l hℳ c hA hR hT x k n y).mpr
      ⟨_, hr, by simpa only [SecondOrderUnpairing.unpair_l] using ht⟩

/-- 前缀内父查询的对应传到原成员程序的全部输出值，不添加外部标准性。 -/
theorem member_congr_l (hℳ : Theory.Models ℳ theory_m) (c d : code_m) {C D M N : set_l ℳ}
    (hC : graph_semantics_l (graph_m c) C) (hD : graph_semantics_l (graph_m d) D)
    (hM : graph_semantics_l (graph_m (member_m c)) M)
    (hN : graph_semantics_l (graph_m (member_m d)) N) (x z b : num_l ℳ)
    (hdown : ∀ j p, relation_l C (value_l x j) (succ_l p) → SecondOrderOrder.lt_l p j)
    (hparent : ∀ j, SecondOrderOrder.lt_l j b → ∀ q,
      relation_l C (value_l x j) q ↔ relation_l D (value_l z j) q)
    {t : num_l ℳ} (ht : SecondOrderOrder.lt_l t b) (i y : num_l ℳ) :
    relation_l M (value_l (value_l x t) i) y ↔ relation_l N (value_l (value_l z t) i) y := by
  obtain ⟨A, _, hA⟩ := graph_total_l hℳ (chain_m c)
  obtain ⟨B, _, hB⟩ := graph_total_l hℳ (chain_m d)
  obtain ⟨K, _, hK⟩ := graph_total_l hℳ contains_m
  obtain ⟨v, hv, _⟩ := function_of_semantics_l hℳ (chain_m c) hA (value_l (value_l x t) t)
  have hv' := (chain_congr_l hℳ c d hC hD hA hB x z b hdown hparent ht t v).mp hv
  exact (member_rel_of_value_l hℳ c hM hA hK hv i y).trans
    (member_rel_of_value_l hℳ d hN hB hK hv' i y).symm

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorPrefixCongruence
