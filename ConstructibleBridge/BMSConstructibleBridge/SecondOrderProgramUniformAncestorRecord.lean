import BMSConstructibleBridge.SecondOrderProgramUniformAncestorRows
import BMSConstructibleBridge.SecondOrderProgramUniformAncestorEntries
import BMSConstructibleBridge.SecondOrderProgramUniformParentSpecification
import BMSConstructibleBridge.SecondOrderProgramUniformParentLookup
import BMSConstructibleBridge.SecondOrderProgramParentZero
import BMSConstructibleBridge.SecondOrderProgramAncestorInterval

/-!
# 原统一祖先的记录最小值正向性质

后继行的实际祖先坐标严格小于其右侧每个低行候选坐标。证明收集同时满足
高行祖先和记录条件的实际内部集合，再用原成员程序的父封闭最小性覆盖整条链。
父搜索的最大候选规格负责排除从记录区间右侧跳过候选的情况。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformAncestorRecord

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramAncestorBudget (state_m state_syntax_l)
open SecondOrderProgramAncestorRecursion (ancestor_m ancestor_formula_l)
open SecondOrderProgramUniformAncestorStructure
open SecondOrderProgramUniformParentSpecification
  (eligible_l parent_succ_some_l parent_succ_none_l parent_entries_lt_l)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListShift (output_m output_syntax_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 同一行的真实some坐标严格小于给定值。 -/
def entry_lt_m {Γ Δ : SortContext signature_m} (J : Term signature_m Γ Δ .set)
    (x r t d : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .existsE .num (.existsE .num (.conj
    (state_m ((x.weakenBound sort_m.num).weakenBound sort_m.num)
      ((t.weakenBound sort_m.num).weakenBound sort_m.num)
      ((r.weakenBound sort_m.num).weakenBound sort_m.num) (.bvar .here))
    (.conj (GraphSyntax.edge_m ((J.weakenBound sort_m.num).weakenBound sort_m.num)
      (.bvar .here) (Term.app (σ := signature_m) .succ (.cons (.bvar (.there .here)) .nil)))
      (PrimitiveFormulas.lt_m (.bvar (.there .here))
        ((d.weakenBound sort_m.num).weakenBound sort_m.num)))))

theorem entry_lt_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (J : Term signature_m Γ Δ .set) (x r t d : Term signature_m Γ Δ .num) :
    (entry_lt_m J x r t d).satisfies η ↔ ∃ e,
      relation_l (J.eval η) (value_l (x.eval η) (value_l (t.eval η) (r.eval η))) (succ_l e) ∧
        SecondOrderOrder.lt_l e (d.eval η) := by
  simp only [entry_lt_m, Formula.satisfies, state_syntax_l, SecondOrderPairing.edge_l,
    SecondOrderOrder.formula_l, Term.eval_weakenBound]
  change (∃ e q, value_l (x.eval η) (value_l (t.eval η) (r.eval η)) = q ∧
    relation_l (J.eval η) q (succ_l e) ∧ SecondOrderOrder.lt_l e (d.eval η)) ↔ _
  simp only [exists_eq_left']

/-- 高行祖先，并且位于j右侧或坐标已经严格小于j的坐标。 -/
def kept_m {Γ Δ : SortContext signature_m} (M J : Term signature_m Γ Δ .set)
    (x r b j d t : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .conj (SecondOrderProgramUniformAncestorRows.row_m M x r b t)
    (.disj (.equal t j) (.disj (PrimitiveFormulas.lt_m j t) (entry_lt_m J x r t d)))

theorem kept_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (M J : Term signature_m Γ Δ .set) (x r b j d t : Term signature_m Γ Δ .num) :
    (kept_m M J x r b j d t).satisfies η ↔
      ¬relation_l (M.eval η)
        (value_l (value_l (value_l (x.eval η) (r.eval η)) (b.eval η)) (t.eval η)) (zero_l ℳ) ∧
      ((t.eval η = j.eval η) ∨ SecondOrderOrder.lt_l (j.eval η) (t.eval η) ∨
        ∃ e, relation_l (J.eval η)
          (value_l (x.eval η) (value_l (t.eval η) (r.eval η))) (succ_l e) ∧
          SecondOrderOrder.lt_l e (d.eval η)) := by
  simp only [kept_m, Formula.satisfies, SecondOrderProgramUniformAncestorRows.row_formula_l,
    SecondOrderOrder.formula_l, entry_lt_formula_l]

/-- 第零行的真实祖先坐标严格小于位于其右侧的任意中间列坐标。 -/
theorem entry_lt_zero_l (hℳ : Theory.Models ℳ theory_m) {M J L : set_l ℳ}
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hL : graph_semantics_l (graph_m length_m) L) {x n b i j a d : num_l ℳ}
    (hn : relation_l L x n)
    (hbn : SecondOrderOrder.lt_l b n)
    (hi : ¬relation_l M
      (value_l (value_l (value_l x (zero_l ℳ)) b) i) (zero_l ℳ))
    (hij : SecondOrderOrder.lt_l i j) (hjb : SecondOrderOrder.lt_l j b)
    (hai : relation_l J (value_l x (value_l i (zero_l ℳ))) (succ_l a))
    (hjd : relation_l J (value_l x (value_l j (zero_l ℳ))) (succ_l d)) :
    SecondOrderOrder.lt_l a d := by
  letI := SecondOrderAlgebra.order_l hℳ
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ parent_m
  obtain ⟨P0, _, hP0⟩ := graph_total_l hℳ SecondOrderProgramParentZero.parent_zero_m
  let φ : Formula signature_m [] [.num, .num, .num, .num, .num, .num, .set, .set] :=
    let t : Term signature_m [] _ .num := .fvar .here
    let x : Term signature_m [] _ .num := .fvar (.there .here)
    let r : Term signature_m [] _ .num := .fvar (.there (.there .here))
    let b : Term signature_m [] _ .num := .fvar (.there (.there (.there .here)))
    let j : Term signature_m [] _ .num := .fvar (.there (.there (.there (.there .here))))
    let d : Term signature_m [] _ .num := .fvar (.there (.there (.there (.there (.there .here)))))
    let M : Term signature_m [] _ .set :=
      .fvar (.there (.there (.there (.there (.there (.there .here))))))
    let J : Term signature_m [] _ .set :=
      .fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))
    kept_m M J x r b j d t
  obtain ⟨S, hS⟩ := comprehension_l hℳ φ (pure_language_m _ rfl)
    ((((((((Env.empty (M := ℳ)).pushFree J).pushFree M).pushFree d).pushFree j).pushFree b).pushFree
      (zero_l ℳ)).pushFree x)
  have hs (t : num_l ℳ) : mem_l t S ↔
      (¬relation_l M (value_l (value_l (value_l x (zero_l ℳ)) b) t) (zero_l ℳ) ∧
      (t = j ∨ SecondOrderOrder.lt_l j t ∨ ∃ e,
        relation_l J (value_l x (value_l t (zero_l ℳ))) (succ_l e) ∧
          SecondOrderOrder.lt_l e d)) := by
    refine (hS t).trans ?_
    simp only [φ, kept_formula_l, Term.eval, FirstOrder.Env.pushFree,
      FirstOrder.Assignment.push]
  have hclosed (t p : num_l ℳ) (ht : t = b ∨ mem_l t S)
      (hp : relation_l P (value_l (value_l x (zero_l ℳ)) t) (succ_l p)) : mem_l p S := by
    have htb : t = b ∨
        ¬relation_l M (value_l (value_l (value_l x (zero_l ℳ)) b) t) (zero_l ℳ) :=
      ht.imp_right (fun ht => ((hs t).mp ht).1)
    have hap := SecondOrderProgramAncestorClosure.member_closed_l hℳ parent_m hM hP
      (fun _ _ h => SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP h) htb hp
    apply (hs p).mpr
    refine ⟨hap, ?_⟩
    have htn : SecondOrderOrder.lt_l t n := by
      rcases ht with rfl | ht
      · exact hbn
      · exact SecondOrderOrder.trans_l hℳ
          (SecondOrderProgramUniformParentOrder.member_lt_l hℳ hM ((hs t).mp ht).1) hbn
    have hp0 := (SecondOrderProgramUniformParentLookup.parent_zero_l
      hℳ hP hP0 hL x n t (succ_l p) hn htn).mp hp
    have hspec := (SecondOrderProgramParentZero.parent_zero_some_l
      hℳ hP0 hL hJ hn t p).mp hp0
    obtain ⟨e, f, hpe, htf, hef⟩ :=
      SecondOrderProgramUniformParentSpecification.parent_entries_lt_l hℳ hP hJ hp
    by_cases hjp : j = p ∨ SecondOrderOrder.lt_l j p
    · exact hjp.elim (fun h => Or.inl h.symm) (fun h => Or.inr (Or.inl h))
    have hpj : SecondOrderOrder.lt_l p j := lt_of_le_of_ne
      (le_of_not_gt (not_or.mp hjp).2) (Ne.symm (not_or.mp hjp).1)
    have hsmall (hfd : SecondOrderOrder.lt_l f d) :
        ∃ e, relation_l J (value_l x (value_l p (zero_l ℳ))) (succ_l e) ∧
          SecondOrderOrder.lt_l e d := by
      have hef' : e < f := hef
      have hfd' : f < d := hfd
      exact ⟨e, hpe, lt_trans hef' hfd'⟩
    rcases ht with htb | ht
    · subst t
      by_cases hed : SecondOrderOrder.lt_l e d
      · exact Or.inr (Or.inr ⟨e, hpe, hed⟩)
      · have hde : d ≤ e := le_of_not_gt hed
        exact False.elim (hspec.2.2.2 j hpj hjb
          ⟨d, f, hjd, htf, lt_of_le_of_lt hde hef⟩)
    · obtain ⟨_, htj | hjt | htd⟩ := (hs t).mp ht
      · subst t
        have hfe : f = d := SecondOrderModel.injective_l hℳ
          (function_value_unique_l (function_of_semantics_l hℳ entry_m hJ) htf hjd)
        exact Or.inr (Or.inr ⟨e, hpe, hfe ▸ hef⟩)
      · by_cases hed : SecondOrderOrder.lt_l e d
        · exact Or.inr (Or.inr ⟨e, hpe, hed⟩)
        · have hde : d ≤ e := le_of_not_gt hed
          exact False.elim (hspec.2.2.2 j hpj hjt
            ⟨d, f, hjd, htf, lt_of_le_of_lt hde hef⟩)
      · obtain ⟨g, htg, hgd⟩ := htd
        have hfg : f = g := SecondOrderModel.injective_l hℳ
          (function_value_unique_l (function_of_semantics_l hℳ entry_m hJ) htf htg)
        exact Or.inr (Or.inr (hsmall (hfg ▸ hgd)))
  have him := SecondOrderProgramAncestorClosedSet.member_mem_l hℳ parent_m hM hP hclosed hi
  obtain ⟨_, him⟩ := (hs i).mp him
  rcases him with h | h | ⟨e, hie, hed⟩
  · exact False.elim ((ne_of_lt hij) h)
  · have hij' : i < j := hij
    have hji' : j < i := h
    exact False.elim (lt_asymm hij' hji')
  · have hea : e = a := SecondOrderModel.injective_l hℳ
      (function_value_unique_l (function_of_semantics_l hℳ entry_m hJ) hie hai)
    exact hea ▸ hed

/-- 第零行的记录最小条件足以重建真实祖先成员。 -/
theorem member_of_record_zero_l (hℳ : Theory.Models ℳ theory_m) {M J L : set_l ℳ}
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hL : graph_semantics_l (graph_m length_m) L) {x n b i a d : num_l ℳ}
    (hn : relation_l L x n) (hbn : SecondOrderOrder.lt_l b n)
    (hib : SecondOrderOrder.lt_l i b)
    (hai : relation_l J (value_l x (value_l i (zero_l ℳ))) (succ_l a))
    (hbd : relation_l J (value_l x (value_l b (zero_l ℳ))) (succ_l d))
    (hab : SecondOrderOrder.lt_l a d)
    (hrecord : ∀ t e, SecondOrderOrder.lt_l i t → SecondOrderOrder.lt_l t b →
      relation_l J (value_l x (value_l t (zero_l ℳ))) (succ_l e) →
      SecondOrderOrder.lt_l a e) :
    ¬relation_l M
      (value_l (value_l (value_l x (zero_l ℳ)) b) i) (zero_l ℳ) := by
  letI := SecondOrderAlgebra.order_l hℳ
  obtain ⟨P, hPf, hP⟩ := graph_total_l hℳ parent_m
  obtain ⟨P0, _, hP0⟩ := graph_total_l hℳ SecondOrderProgramParentZero.parent_zero_m
  have hparent (t p : num_l ℳ)
      (hp : relation_l P (value_l (value_l x (zero_l ℳ)) t) (succ_l p)) :
      SecondOrderOrder.lt_l p t :=
    SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hp
  apply SecondOrderProgramAncestorInterval.member_of_persistent_l
    hℳ parent_m hM hP hparent hib
  intro t hit ht
  have htb : SecondOrderOrder.lt_l t b ∨ t = b := by
    rcases ht with rfl | ht
    · exact Or.inr rfl
    · exact Or.inl (SecondOrderProgramUniformParentOrder.member_lt_l hℳ hM ht)
  obtain ⟨e, hte, hae⟩ : ∃ e,
      relation_l J (value_l x (value_l t (zero_l ℳ))) (succ_l e) ∧
        SecondOrderOrder.lt_l a e := by
    rcases htb with htb | rfl
    · rcases ht with h | ht
      · exact False.elim ((ne_of_lt htb) h)
      · obtain ⟨e, _, hte, _, _⟩ :=
          SecondOrderProgramUniformAncestorEntries.member_entries_lt_l hℳ hM hJ ht
        exact ⟨e, hte, hrecord t e hit htb hte⟩
    · exact ⟨d, hbd, hab⟩
  have helig : SecondOrderProgramParentZero.eligible_l J x t i :=
    ⟨a, e, hai, hte, hae⟩
  have htn : SecondOrderOrder.lt_l t n := htb.elim
    (fun h => SecondOrderOrder.trans_l hℳ h hbn) (fun h => h ▸ hbn)
  obtain ⟨q, hq, _⟩ := hPf (value_l (value_l x (zero_l ℳ)) t)
  have hq0 := (SecondOrderProgramUniformParentLookup.parent_zero_l
    hℳ hP hP0 hL x n t q hn htn).mp hq
  rcases predecessor_l hℳ q with rfl | ⟨p, rfl⟩
  · rcases (SecondOrderProgramParentZero.parent_zero_none_l
      hℳ hP0 hL hJ hn t).mp hq0 with hnt | hnone
    · exact False.elim ((not_le_of_gt htn) hnt)
    · exact False.elim (hnone i hit helig)
  · have hs := (SecondOrderProgramParentZero.parent_zero_some_l
      hℳ hP0 hL hJ hn t p).mp hq0
    have hip : i ≤ p := le_of_not_gt (fun hpi => hs.2.2.2 i hpi hit helig)
    exact ⟨p, hq, (eq_or_lt_of_le hip).elim Or.inl Or.inr⟩

/-- 第零行祖先恰是严格条目记录点。 -/
theorem member_iff_record_zero_l (hℳ : Theory.Models ℳ theory_m) {M J L : set_l ℳ}
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hL : graph_semantics_l (graph_m length_m) L) {x n b i a d : num_l ℳ}
    (hn : relation_l L x n) (hbn : SecondOrderOrder.lt_l b n)
    (hai : relation_l J (value_l x (value_l i (zero_l ℳ))) (succ_l a))
    (hbd : relation_l J (value_l x (value_l b (zero_l ℳ))) (succ_l d)) :
    (¬relation_l M
      (value_l (value_l (value_l x (zero_l ℳ)) b) i) (zero_l ℳ)) ↔
      SecondOrderOrder.lt_l i b ∧ SecondOrderOrder.lt_l a d ∧
      ∀ t e, SecondOrderOrder.lt_l i t → SecondOrderOrder.lt_l t b →
        relation_l J (value_l x (value_l t (zero_l ℳ))) (succ_l e) →
        SecondOrderOrder.lt_l a e := by
  constructor
  · intro hi
    have hib := SecondOrderProgramUniformParentOrder.member_lt_l hℳ hM hi
    obtain ⟨a', d', hia, hbd', had⟩ :=
      SecondOrderProgramUniformAncestorEntries.member_entries_lt_l hℳ hM hJ hi
    have haa : a' = a := SecondOrderModel.injective_l hℳ
      (function_value_unique_l (function_of_semantics_l hℳ entry_m hJ) hia hai)
    have hdd : d' = d := SecondOrderModel.injective_l hℳ
      (function_value_unique_l (function_of_semantics_l hℳ entry_m hJ) hbd' hbd)
    refine ⟨hib, by simpa only [haa, hdd] using had, ?_⟩
    intro t e hit htb hte
    exact entry_lt_zero_l hℳ hM hJ hL hn hbn hi hit htb hai hte
  · rintro ⟨hib, hab, hrecord⟩
    exact member_of_record_zero_l hℳ hM hJ hL hn hbn hib hai hbd hab hrecord

/-- 高行祖先坐标小于任一位于其右侧的低行祖先坐标。 -/
theorem entry_lt_l (hℳ : Theory.Models ℳ theory_m) {M J : set_l ℳ}
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J) {x r b i j a d : num_l ℳ}
    (hi : ¬relation_l M (value_l (value_l (value_l x (succ_l r)) b) i) (zero_l ℳ))
    (hj : ¬relation_l M (value_l (value_l (value_l x r) b) j) (zero_l ℳ))
    (hij : SecondOrderOrder.lt_l i j)
    (hai : relation_l J (value_l x (value_l i (succ_l r))) (succ_l a))
    (hjd : relation_l J (value_l x (value_l j (succ_l r))) (succ_l d)) :
    SecondOrderOrder.lt_l a d := by
  letI := SecondOrderAlgebra.semiring_l hℳ
  letI := SecondOrderAlgebra.order_l hℳ
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ parent_m
  obtain ⟨L, hLf, hL⟩ := graph_total_l hℳ length_m
  obtain ⟨n, hn, _⟩ := hLf x
  let φ : Formula signature_m [] [.num, .num, .num, .num, .num, .num, .set, .set] :=
    let t : Term signature_m [] _ .num := .fvar .here
    let x : Term signature_m [] _ .num := .fvar (.there .here)
    let r : Term signature_m [] _ .num := .fvar (.there (.there .here))
    let b : Term signature_m [] _ .num := .fvar (.there (.there (.there .here)))
    let j : Term signature_m [] _ .num := .fvar (.there (.there (.there (.there .here))))
    let d : Term signature_m [] _ .num := .fvar (.there (.there (.there (.there (.there .here)))))
    let M : Term signature_m [] _ .set :=
      .fvar (.there (.there (.there (.there (.there (.there .here))))))
    let J : Term signature_m [] _ .set :=
      .fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))
    kept_m M J x r b j d t
  obtain ⟨S, hS⟩ := comprehension_l hℳ φ (pure_language_m _ rfl)
    ((((((((Env.empty (M := ℳ)).pushFree J).pushFree M).pushFree d).pushFree j).pushFree b).pushFree
      (succ_l r)).pushFree x)
  have hs (t : num_l ℳ) : mem_l t S ↔
      (¬relation_l M (value_l (value_l (value_l x (succ_l r)) b) t) (zero_l ℳ) ∧
      (t = j ∨ SecondOrderOrder.lt_l j t ∨ ∃ e,
        relation_l J (value_l x (value_l t (succ_l r))) (succ_l e) ∧ SecondOrderOrder.lt_l e d)) := by
    refine (hS t).trans ?_
    simp only [φ, kept_formula_l, Term.eval, FirstOrder.Env.pushFree,
      FirstOrder.Assignment.push]
  have hclosed (t p : num_l ℳ) (ht : t = b ∨ mem_l t S)
      (hp : relation_l P (value_l (value_l x (succ_l r)) t) (succ_l p)) : mem_l p S := by
    have htp : t = b ∨
        ¬relation_l M (value_l (value_l (value_l x (succ_l r)) b) t) (zero_l ℳ) :=
      ht.imp_right (fun ht => ((hs t).mp ht).1)
    have hap := SecondOrderProgramAncestorClosure.member_closed_l hℳ parent_m hM hP
      (fun _ _ h => SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP h) htp hp
    apply (hs p).mpr
    refine ⟨hap, ?_⟩
    rcases parent_entries_lt_l hℳ hP hJ hp with ⟨e, f, hpe, htf, hef⟩
    by_cases hjp : j = p ∨ SecondOrderOrder.lt_l j p
    · exact hjp.elim (fun h => Or.inl h.symm) (fun h => Or.inr (Or.inl h))
    have hpj : SecondOrderOrder.lt_l p j := lt_of_le_of_ne (le_of_not_gt (not_or.mp hjp).2)
      (Ne.symm (not_or.mp hjp).1)
    have hsmall (hfd : SecondOrderOrder.lt_l f d) :
        ∃ e, relation_l J (value_l x (value_l p (succ_l r))) (succ_l e) ∧
          SecondOrderOrder.lt_l e d := by
      have hef' : e < f := hef
      have hfd' : f < d := hfd
      exact ⟨e, hpe, lt_trans hef' hfd'⟩
    rcases ht with htb | ht
    · subst t
      have hjb := SecondOrderProgramUniformParentOrder.member_lt_l hℳ hM hj
      have hspec := (parent_succ_some_l hℳ hP hL hM hJ hn r b p).mp hp
      by_cases hed : SecondOrderOrder.lt_l e d
      · exact Or.inr (Or.inr ⟨e, hpe, hed⟩)
      · have hde : d ≤ e := le_of_not_gt hed
        exact False.elim (hspec.2.2.2 j hpj hjb
          ⟨hj, d, f, hjd, htf, lt_of_le_of_lt hde hef⟩)
    · obtain ⟨hat, htj | hjt | htd⟩ := (hs t).mp ht
      · subst t
        have hfe : f = d := SecondOrderModel.injective_l hℳ
          (function_value_unique_l (function_of_semantics_l hℳ entry_m hJ) htf hjd)
        exact Or.inr (Or.inr ⟨e, hpe, hfe ▸ hef⟩)
      · have hrt := row_succ_l hℳ hM hat
        have htj' := comparable_l hℳ hM hj hrt hjt
        have hspec := (parent_succ_some_l hℳ hP hL hM hJ hn r t p).mp hp
        by_cases hed : SecondOrderOrder.lt_l e d
        · exact Or.inr (Or.inr ⟨e, hpe, hed⟩)
        · have hde : d ≤ e := le_of_not_gt hed
          exact False.elim (hspec.2.2.2 j hpj hjt
            ⟨htj', d, f, hjd, htf, lt_of_le_of_lt hde hef⟩)
      · obtain ⟨g, htg, hgd⟩ := htd
        have hfg : f = g := SecondOrderModel.injective_l hℳ
          (function_value_unique_l (function_of_semantics_l hℳ entry_m hJ) htf htg)
        exact Or.inr (Or.inr (hsmall (hfg ▸ hgd)))
  have him := SecondOrderProgramAncestorClosedSet.member_mem_l hℳ parent_m hM hP hclosed hi
  obtain ⟨_, him⟩ := (hs i).mp him
  rcases him with h | h | ⟨e, hie, hed⟩
  · exact False.elim ((ne_of_lt hij) h)
  · have hij' : i < j := hij
    have hji' : j < i := h
    exact False.elim (lt_asymm hij' hji')
  · have hea : e = a := SecondOrderModel.injective_l hℳ
      (function_value_unique_l (function_of_semantics_l hℳ entry_m hJ) hie hai)
    exact hea ▸ hed

/-- 低行成员及其高行严格记录条件足以重建高行的真实祖先成员。 -/
theorem member_of_record_l (hℳ : Theory.Models ℳ theory_m) {M J L : set_l ℳ}
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hL : graph_semantics_l (graph_m length_m) L) {x n r b i a d : num_l ℳ}
    (hn : relation_l L x n) (hbn : SecondOrderOrder.lt_l b n)
    (hilow : ¬relation_l M (value_l (value_l (value_l x r) b) i) (zero_l ℳ))
    (hib : SecondOrderOrder.lt_l i b)
    (hai : relation_l J (value_l x (value_l i (succ_l r))) (succ_l a))
    (hbd : relation_l J (value_l x (value_l b (succ_l r))) (succ_l d))
    (hab : SecondOrderOrder.lt_l a d)
    (hrecord : ∀ t e, SecondOrderOrder.lt_l i t → SecondOrderOrder.lt_l t b →
      (¬relation_l M (value_l (value_l (value_l x r) b) t) (zero_l ℳ)) →
      relation_l J (value_l x (value_l t (succ_l r))) (succ_l e) →
      SecondOrderOrder.lt_l a e) :
    ¬relation_l M (value_l (value_l (value_l x (succ_l r)) b) i) (zero_l ℳ) := by
  letI := SecondOrderAlgebra.semiring_l hℳ
  letI := SecondOrderAlgebra.order_l hℳ
  obtain ⟨P, hPf, hP⟩ := graph_total_l hℳ parent_m
  have hparent (t p : num_l ℳ)
      (hp : relation_l P (value_l (value_l x (succ_l r)) t) (succ_l p)) :
      SecondOrderOrder.lt_l p t :=
    SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hp
  apply SecondOrderProgramAncestorInterval.member_of_persistent_l hℳ parent_m hM hP hparent hib
  intro t hit ht
  have htb : SecondOrderOrder.lt_l t b ∨ t = b := by
    rcases ht with rfl | ht
    · exact Or.inr rfl
    · exact Or.inl (SecondOrderProgramUniformParentOrder.member_lt_l hℳ hM ht)
  have hti : ¬relation_l M (value_l (value_l (value_l x r) t) i) (zero_l ℳ) := by
    rcases ht with rfl | ht
    · exact hilow
    · have hrt := row_succ_l hℳ hM ht
      exact comparable_l hℳ hM hilow hrt hit
  obtain ⟨e, hte, hae⟩ : ∃ e,
      relation_l J (value_l x (value_l t (succ_l r))) (succ_l e) ∧
        SecondOrderOrder.lt_l a e := by
    rcases htb with htb | rfl
    · have hthigh :
          ¬relation_l M (value_l (value_l (value_l x (succ_l r)) b) t) (zero_l ℳ) := by
        rcases ht with h | ht
        · exact False.elim ((ne_of_lt htb) h)
        · exact ht
      obtain ⟨e, _, hte, _, _⟩ :=
        SecondOrderProgramUniformAncestorEntries.member_entries_lt_l hℳ hM hJ hthigh
      exact ⟨e, hte, hrecord t e hit htb (row_succ_l hℳ hM hthigh) hte⟩
    · exact ⟨d, hbd, hab⟩
  have helig : eligible_l M J x r t i := ⟨hti, a, e, hai, hte, hae⟩
  obtain ⟨q, hq, _⟩ := hPf (value_l (value_l x (succ_l r)) t)
  rcases predecessor_l hℳ q with rfl | ⟨p, rfl⟩
  · have htn : SecondOrderOrder.lt_l t n := htb.elim
      (fun h => SecondOrderOrder.trans_l hℳ h hbn) (fun h => h ▸ hbn)
    rcases (parent_succ_none_l hℳ hP hL hM hJ hn r t).mp hq with hnt | hnone
    · exact False.elim ((not_le_of_gt htn) hnt)
    · exact False.elim (hnone i hit helig)
  · have hs := (parent_succ_some_l hℳ hP hL hM hJ hn r t p).mp hq
    have hip : i ≤ p := le_of_not_gt (fun hpi => hs.2.2.2 i hpi hit helig)
    exact ⟨p, hq, (eq_or_lt_of_le hip).elim Or.inl Or.inr⟩

/-- 后继行祖先恰是低行祖先中，坐标严格低于其右侧每个有定义候选的记录点。 -/
theorem member_iff_record_l (hℳ : Theory.Models ℳ theory_m) {M J L : set_l ℳ}
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hL : graph_semantics_l (graph_m length_m) L) {x n r b i a d : num_l ℳ}
    (hn : relation_l L x n) (hbn : SecondOrderOrder.lt_l b n)
    (hai : relation_l J (value_l x (value_l i (succ_l r))) (succ_l a))
    (hbd : relation_l J (value_l x (value_l b (succ_l r))) (succ_l d)) :
    (¬relation_l M (value_l (value_l (value_l x (succ_l r)) b) i) (zero_l ℳ)) ↔
      SecondOrderOrder.lt_l i b ∧
      (¬relation_l M (value_l (value_l (value_l x r) b) i) (zero_l ℳ)) ∧
      SecondOrderOrder.lt_l a d ∧
      ∀ t e, SecondOrderOrder.lt_l i t → SecondOrderOrder.lt_l t b →
        (¬relation_l M (value_l (value_l (value_l x r) b) t) (zero_l ℳ)) →
        relation_l J (value_l x (value_l t (succ_l r))) (succ_l e) →
        SecondOrderOrder.lt_l a e := by
  constructor
  · intro hi
    have hib := SecondOrderProgramUniformParentOrder.member_lt_l hℳ hM hi
    have hilow := row_succ_l hℳ hM hi
    obtain ⟨a', d', hia, hbd', had⟩ :=
      SecondOrderProgramUniformAncestorEntries.member_entries_lt_l hℳ hM hJ hi
    have haa : a' = a := SecondOrderModel.injective_l hℳ
      (function_value_unique_l (function_of_semantics_l hℳ entry_m hJ) hia hai)
    have hdd : d' = d := SecondOrderModel.injective_l hℳ
      (function_value_unique_l (function_of_semantics_l hℳ entry_m hJ) hbd' hbd)
    refine ⟨hib, hilow, ?_, ?_⟩
    · simpa only [haa, hdd] using had
    · intro t e hit htb htlow hte
      exact entry_lt_l hℳ hM hJ hi htlow hit hai hte
  · rintro ⟨hib, hilow, hab, hrecord⟩
    exact member_of_record_l hℳ hM hJ hL hn hbn hilow hib hai hbd hab hrecord

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformAncestorRecord
