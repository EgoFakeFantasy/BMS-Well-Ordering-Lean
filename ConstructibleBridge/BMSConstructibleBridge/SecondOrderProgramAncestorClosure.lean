import BMSConstructibleBridge.SecondOrderProgramIterationClosedSet
import BMSConstructibleBridge.SecondOrderProgramListOccurrence
import BMSConstructibleBridge.SecondOrderProgramAncestorTermination
import BMSConstructibleBridge.SecondOrderProgramAncestorMembership

/-!
# 原祖先成员集合对父查询封闭

一次实际运行中，每个已访问节点的父节点已经入表，唯一允许尚未入表的是
当前列的父节点。用实际理解公式收集满足此性质的状态，再由原迭代保持。
起始列步数后的原终止定理消去这一例外；反转只改变位置，不改变有效成员。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorClosure

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramIteration
open SecondOrderProgramAncestorStep (step_m)
open SecondOrderProgramAncestorTransition (step_none_l step_some_l)
open SecondOrderProgramAncestorBudget (state_m state_syntax_l)
open SecondOrderProgramAncestorChain (chain_m chain_rel_l)
open SecondOrderProgramAncestorMembership (member_m member_nonzero_l)
open SecondOrderProgramListOccurrence (occurs_l occurs_m occurs_formula_l)
open SecondOrderProgramListShift (output_m output_syntax_l)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramListReverse (reverse_m)
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 初始列和表中每个节点，或者正是当前列，或者其父已经在表中。 -/
def linked_l (C L E : set_l ℳ) (x b t v : num_l ℳ) : Prop :=
  ∀ q, q = b ∨ occurs_l L E v q → q = t ∨
    ∀ p, relation_l C (value_l x q) (succ_l p) → occurs_l L E v p

def linked_m {Γ Δ : SortContext signature_m} (C L E : Term signature_m Γ Δ .set)
    (x b t v : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .forallE .num (.imp
    (.disj (.equal (.bvar .here) (b.weakenBound sort_m.num))
      (occurs_m (L.weakenBound sort_m.num) (E.weakenBound sort_m.num)
        (v.weakenBound sort_m.num) (.bvar .here)))
    (.disj (.equal (.bvar .here) (t.weakenBound sort_m.num))
      (.forallE .num (.imp
        (output_m ((C.weakenBound sort_m.num).weakenBound sort_m.num)
          ((x.weakenBound sort_m.num).weakenBound sort_m.num) (.bvar (.there .here))
          (Term.app (σ := signature_m) .succ (.cons (.bvar .here) .nil)))
        (occurs_m ((L.weakenBound sort_m.num).weakenBound sort_m.num)
          ((E.weakenBound sort_m.num).weakenBound sort_m.num)
          ((v.weakenBound sort_m.num).weakenBound sort_m.num) (.bvar .here))))))

theorem linked_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (C L E : Term signature_m Γ Δ .set) (x b t v : Term signature_m Γ Δ .num) :
    (linked_m C L E x b t v).satisfies η ↔
      linked_l (C.eval η) (L.eval η) (E.eval η) (x.eval η) (b.eval η) (t.eval η) (v.eval η) := by
  simp only [linked_m, linked_l, Formula.satisfies, occurs_formula_l,
    output_syntax_l, Term.eval_weakenBound]
  rfl

theorem linked_zero_l (hℳ : Theory.Models ℳ theory_m) {C L E : set_l ℳ}
    (hL : graph_semantics_l (graph_m length_m) L) (x b : num_l ℳ) :
    linked_l C L E x b b (zero_l ℳ) := by
  intro q hq
  rcases hq with hq | hq
  · exact Or.inl hq
  · exact False.elim (SecondOrderProgramListOccurrence.zero_l hℳ hL q hq)

theorem linked_cons_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {C L E : set_l ℳ}
    (hC : graph_semantics_l (graph_m c) C)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x b t v p : num_l ℳ}
    (hv : linked_l C L E x b t v) (hp : relation_l C (value_l x t) (succ_l p)) :
    linked_l C L E x b p (succ_l (value_l p v)) := by
  have h (q : num_l ℳ) (hq : q = b ∨ occurs_l L E v q) : q = p ∨
      ∀ i, relation_l C (value_l x q) (succ_l i) → occurs_l L E (succ_l (value_l p v)) i := by
    right
    intro i hi
    apply (SecondOrderProgramListOccurrence.cons_l hℳ hL hE p v i).mpr
    rcases hv q hq with hqt | hqv
    · subst q
      exact Or.inl (SecondOrderModel.injective_l hℳ
        (function_value_unique_l (function_of_semantics_l hℳ c hC) hi hp))
    · exact Or.inr (hqv i hi)
  intro q hq
  rcases hq with hq | hq
  · exact h q (Or.inl hq)
  · rcases (SecondOrderProgramListOccurrence.cons_l hℳ hL hE p v q).mp hq with hq | hq
    · exact Or.inl hq
    · exact h q (Or.inr hq)

def kept_l (C L E : set_l ℳ) (x b s : num_l ℳ) : Prop :=
  ∃ t v, value_l x (value_l t v) = s ∧ linked_l C L E x b t v

/-- 自由槽[s,x,b,C,L,E]；状态中的当前列和累计表由真实配对分解。 -/
def kept_m : Formula signature_m [] [.num, .num, .num, .set, .set, .set] :=
  .existsE .num (.existsE .num (.conj
    (state_m (.fvar (.there .here)) (.bvar (.there .here)) (.bvar .here) (.fvar .here))
    (linked_m (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there .here)) (.fvar (.there (.there .here)))
      (.bvar (.there .here)) (.bvar .here))))

theorem kept_formula_l (C L E : set_l ℳ) (x b s : num_l ℳ) :
    kept_m.satisfies (((((((Env.empty (M := ℳ)).pushFree E).pushFree L).pushFree C).pushFree b).pushFree x).pushFree s) ↔
      kept_l C L E x b s := by
  simp only [kept_m, kept_l, Formula.satisfies, state_syntax_l, linked_formula_l]
  rfl

/-- 所有内部步数均保持邻接性质；归纳仅在实际理解所得集合上实施。 -/
theorem output_kept_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {R C L E : set_l ℳ}
    (hR : graph_semantics_l (graph_m (repeat_m (step_m c))) R)
    (hC : graph_semantics_l (graph_m c) C)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x b n s : num_l ℳ}
    (hs : relation_l R (value_l (value_l x (value_l b (zero_l ℳ))) n) s) :
    kept_l C L E x b s := by
  obtain ⟨S, hS⟩ := comprehension_l hℳ kept_m (pure_language_m _ rfl)
    ((((((Env.empty (M := ℳ)).pushFree E).pushFree L).pushFree C).pushFree b).pushFree x)
  have h (s : num_l ℳ) : mem_l s S ↔ kept_l C L E x b s :=
    (hS s).trans (kept_formula_l C L E x b s)
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ (step_m c)
  have hclosed (s y : num_l ℳ) (hs : mem_l s S) (hy : relation_l T s y) : mem_l y S := by
    obtain ⟨t, v, rfl, hv⟩ := (h s).mp hs
    apply (h y).mpr
    obtain ⟨q, hq, _⟩ := function_of_semantics_l hℳ c hC (value_l x t)
    rcases predecessor_l hℳ q with rfl | ⟨p, rfl⟩
    · exact ⟨t, v, (step_none_l hℳ c hT hC hq v y).mp hy, hv⟩
    · exact ⟨p, succ_l (value_l p v), (step_some_l hℳ c hT hC hq v y).mp hy,
        linked_cons_l hℳ c hC hL hE hv hq⟩
  exact (h s).mp (SecondOrderProgramIterationClosedSet.repeat_mem_l hℳ (step_m c) hR hT
    hclosed ((h _).mpr ⟨b, zero_l ℳ, rfl, linked_zero_l hℳ hL x b⟩) hs)

/-- 足够燃料后的实际累计表没有待处理父节点。 -/
theorem output_closed_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {R C L E : set_l ℳ}
    (hR : graph_semantics_l (graph_m (repeat_m (step_m c))) R)
    (hC : graph_semantics_l (graph_m c) C)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x b s : num_l ℳ}
    (hparent : ∀ t p, relation_l C (value_l x t) (succ_l p) → SecondOrderOrder.lt_l p t)
    (hs : relation_l R (value_l (value_l x (value_l b (zero_l ℳ))) b) s) :
    ∃ t v, s = value_l x (value_l t v) ∧
      ∀ q p, (q = b ∨ occurs_l L E v q) → relation_l C (value_l x q) (succ_l p) → occurs_l L E v p := by
  obtain ⟨t, v, he, ht⟩ := SecondOrderProgramAncestorTermination.output_terminal_l hℳ c hR hC hparent hs
  obtain ⟨k, w, hw, hv⟩ := output_kept_l hℳ c hR hC hL hE hs
  have hkw := (SecondOrderPairingBounds.injective_l hℳ _ _ _ _ (hw.trans he)).2
  obtain ⟨rfl, rfl⟩ := SecondOrderPairingBounds.injective_l hℳ _ _ _ _ hkw
  refine ⟨k, w, he, ?_⟩
  intro q p hq hp
  rcases hv q hq with hq | hq
  · subst q
    exact False.elim (nonzero_l hℳ p
      (function_value_unique_l (function_of_semantics_l hℳ c hC) hp ht))
  · exact hq p hp

/-- 原成员程序定义的祖先集合，而非另造的传递闭包，对真实父查询封闭。 -/
theorem member_closed_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {M C : set_l ℳ}
    (hM : graph_semantics_l (graph_m (member_m c)) M)
    (hC : graph_semantics_l (graph_m c) C) {x b q p : num_l ℳ}
    (hparent : ∀ t p, relation_l C (value_l x t) (succ_l p) → SecondOrderOrder.lt_l p t)
    (hq : q = b ∨ ¬relation_l M (value_l (value_l x b) q) (zero_l ℳ))
    (hp : relation_l C (value_l x q) (succ_l p)) :
    ¬relation_l M (value_l (value_l x b) p) (zero_l ℳ) := by
  obtain ⟨A, hAf, hA⟩ := graph_total_l hℳ (chain_m c)
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ (repeat_m (step_m c))
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ reverse_m
  obtain ⟨L, hLf, hL⟩ := graph_total_l hℳ length_m
  obtain ⟨E, _, hE⟩ := graph_total_l hℳ lookup_m
  obtain ⟨y, hy, _⟩ := hAf (value_l (value_l x b) b)
  obtain ⟨n, hn, _⟩ := hLf y
  obtain ⟨s, hs, hsy⟩ := (chain_rel_l hℳ c hA hR hT x b b y).mp hy
  obtain ⟨t, v, rfl, hv⟩ := output_closed_l hℳ c hR hC hL hE hparent hs
  simp only [SecondOrderUnpairing.unpair_l] at hsy
  have h (i : num_l ℳ) : ¬relation_l M (value_l (value_l x b) i) (zero_l ℳ) ↔ occurs_l L E v i :=
    ((member_nonzero_l hℳ c hM hA hL hE hy hn i).trans
      (SecondOrderProgramListOccurrence.length_l hℳ hL hn i).symm).trans
        (SecondOrderProgramListOccurrence.reverse_l hℳ hT hL hE hsy i).symm
  apply (h p).mpr
  apply hv q p ?_ hp
  exact hq.elim Or.inl (fun hq => Or.inr ((h q).mp hq))

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorClosure
