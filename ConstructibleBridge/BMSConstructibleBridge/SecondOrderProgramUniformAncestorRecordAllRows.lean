import BMSConstructibleBridge.SecondOrderProgramUniformAncestorRecord
import BMSConstructibleBridge.SecondOrderProgramUniformAncestorRows
import BMSConstructibleBridge.SecondOrderNaturalGraph

/-!
# 统一的全低行祖先记录判据

零行与后继行的原记录判据在本模块合成一条任意内部行公式：
当前行祖先当且仅当列序、全部更低行祖先、当前坐标严格序及
所有更低行祖先中间列的记录最小值成立。后继行使用实际行持久性，
没有以宿主自然数归纳替换模型中的非标准行号。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformAncestorRecordAllRows

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramLength (length_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 任意内部行的真实祖先成员关系的全低行记录刻画。 -/
theorem member_iff_record_all_l (hℳ : Theory.Models ℳ theory_m) {M J L : set_l ℳ}
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hL : graph_semantics_l (graph_m length_m) L)
    {x n row target candidate a d : num_l ℳ}
    (hn : relation_l L x n)
    (htarget : SecondOrderOrder.lt_l target n)
    (ha : relation_l J (value_l x (value_l candidate row)) (succ_l a))
    (hd : relation_l J (value_l x (value_l target row)) (succ_l d)) :
    (¬relation_l M
      (value_l (value_l (value_l x row) target) candidate) (zero_l ℳ)) ↔
      SecondOrderOrder.lt_l candidate target ∧
      (∀ s, SecondOrderOrder.lt_l s row →
        ¬relation_l M
          (value_l (value_l (value_l x s) target) candidate) (zero_l ℳ)) ∧
      SecondOrderOrder.lt_l a d ∧
      ∀ middle e, SecondOrderOrder.lt_l candidate middle →
        SecondOrderOrder.lt_l middle target →
        (∀ s, SecondOrderOrder.lt_l s row →
          ¬relation_l M
            (value_l (value_l (value_l x s) target) middle) (zero_l ℳ)) →
        relation_l J (value_l x (value_l middle row)) (succ_l e) →
        SecondOrderOrder.lt_l a e := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  rcases predecessor_l hℳ row with rfl | ⟨r, rfl⟩
  · have hrec := SecondOrderProgramUniformAncestorRecord.member_iff_record_zero_l
      hℳ hM hJ hL hn htarget ha hd
    have hempty (s : num_l ℳ) : ¬SecondOrderOrder.lt_l s (zero_l ℳ) :=
      not_lt_of_ge (zero_le_l hℳ s)
    constructor
    · intro h
      obtain ⟨hct, had, hrecord⟩ := hrec.mp h
      refine ⟨hct, ?_, had, ?_⟩
      · intro s hs
        exact False.elim (hempty s hs)
      · intro middle e hcm hmt _ hme
        exact hrecord middle e hcm hmt hme
    · rintro ⟨hct, _, had, hrecord⟩
      apply hrec.mpr
      refine ⟨hct, had, ?_⟩
      intro middle e hcm hmt hme
      exact hrecord middle e hcm hmt
        (fun s hs => False.elim (hempty s hs)) hme
  · have hrec := SecondOrderProgramUniformAncestorRecord.member_iff_record_l
      hℳ hM hJ hL hn htarget ha hd
    have hall (middle : num_l ℳ)
        (hm : ¬relation_l M
          (value_l (value_l (value_l x r) target) middle) (zero_l ℳ)) :
        ∀ s, SecondOrderOrder.lt_l s (succ_l r) →
          ¬relation_l M
            (value_l (value_l (value_l x s) target) middle) (zero_l ℳ) := by
      intro s hs
      have hsr : s ≤ r := (SecondOrderNaturalGraph.lt_succ_l hℳ s r).mp hs
      exact SecondOrderProgramUniformAncestorRows.row_le_l hℳ hM hsr hm
    constructor
    · intro h
      obtain ⟨hct, hlow, had, hrecord⟩ := hrec.mp h
      refine ⟨hct, hall candidate hlow, had, ?_⟩
      intro middle e hcm hmt hbelow hme
      exact hrecord middle e hcm hmt (hbelow r (lt_own_succ_l hℳ r)) hme
    · rintro ⟨hct, hbelow, had, hrecord⟩
      apply hrec.mpr
      refine ⟨hct, hbelow r (lt_own_succ_l hℳ r), had, ?_⟩
      intro middle e hcm hmt hmid hme
      exact hrecord middle e hcm hmt (hall middle hmid) hme

/-- 两数组的当前边界若具有同一列序、低行祖先、当前坐标序，且所有
中间列的低行祖先和记录比较可双向搬运，则真实祖先边也双向搬运。 -/
theorem member_iff_of_middle_transport_l (hℳ : Theory.Models ℳ theory_m)
    {M J L : set_l ℳ}
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hL : graph_semantics_l (graph_m length_m) L)
    {x y nx ny row b c b' c' a d a' d' : num_l ℳ}
    (hnx : relation_l L x nx) (hny : relation_l L y ny)
    (hb : SecondOrderOrder.lt_l b nx) (hb' : SecondOrderOrder.lt_l b' ny)
    (hca : relation_l J (value_l x (value_l c row)) (succ_l a))
    (hbd : relation_l J (value_l x (value_l b row)) (succ_l d))
    (hc'a' : relation_l J (value_l y (value_l c' row)) (succ_l a'))
    (hb'd' : relation_l J (value_l y (value_l b' row)) (succ_l d'))
    (hcolumns : SecondOrderOrder.lt_l c b ↔ SecondOrderOrder.lt_l c' b')
    (hbelow : ∀ s, SecondOrderOrder.lt_l s row →
      (¬relation_l M (value_l (value_l (value_l x s) b) c) (zero_l ℳ) ↔
        ¬relation_l M (value_l (value_l (value_l y s) b') c') (zero_l ℳ)))
    (hentries : SecondOrderOrder.lt_l a d ↔ SecondOrderOrder.lt_l a' d')
    (hsourceMiddle : ∀ m, SecondOrderOrder.lt_l c m →
      SecondOrderOrder.lt_l m b →
      (∀ s, SecondOrderOrder.lt_l s row →
        ¬relation_l M (value_l (value_l (value_l x s) b) m) (zero_l ℳ)) →
      ∃ m', SecondOrderOrder.lt_l c' m' ∧ SecondOrderOrder.lt_l m' b' ∧
        (∀ s, SecondOrderOrder.lt_l s row →
          (¬relation_l M (value_l (value_l (value_l x s) b) m) (zero_l ℳ) ↔
            ¬relation_l M (value_l (value_l (value_l y s) b') m') (zero_l ℳ))) ∧
        (∀ e, relation_l J (value_l x (value_l m row)) (succ_l e) →
          ∃ e', relation_l J (value_l y (value_l m' row)) (succ_l e') ∧
            (SecondOrderOrder.lt_l a e ↔ SecondOrderOrder.lt_l a' e')))
    (htargetMiddle : ∀ m', SecondOrderOrder.lt_l c' m' →
      SecondOrderOrder.lt_l m' b' →
      (∀ s, SecondOrderOrder.lt_l s row →
        ¬relation_l M (value_l (value_l (value_l y s) b') m') (zero_l ℳ)) →
      ∃ m, SecondOrderOrder.lt_l c m ∧ SecondOrderOrder.lt_l m b ∧
        (∀ s, SecondOrderOrder.lt_l s row →
          (¬relation_l M (value_l (value_l (value_l x s) b) m) (zero_l ℳ) ↔
            ¬relation_l M (value_l (value_l (value_l y s) b') m') (zero_l ℳ))) ∧
        (∀ e', relation_l J (value_l y (value_l m' row)) (succ_l e') →
          ∃ e, relation_l J (value_l x (value_l m row)) (succ_l e) ∧
            (SecondOrderOrder.lt_l a e ↔ SecondOrderOrder.lt_l a' e'))) :
    (¬relation_l M (value_l (value_l (value_l x row) b) c) (zero_l ℳ)) ↔
      (¬relation_l M (value_l (value_l (value_l y row) b') c') (zero_l ℳ)) := by
  have hx := member_iff_record_all_l hℳ hM hJ hL hnx hb hca hbd
  have hy := member_iff_record_all_l hℳ hM hJ hL hny hb' hc'a' hb'd'
  constructor
  · intro h
    obtain ⟨hcb, hlow, had, hrecord⟩ := hx.mp h
    apply hy.mpr
    refine ⟨hcolumns.mp hcb, ?_, hentries.mp had, ?_⟩
    · intro s hs
      exact (hbelow s hs).mp (hlow s hs)
    · intro m' e' hcm' hmb' hlow' hme'
      obtain ⟨m, hcm, hmb, hmid, hentry⟩ := htargetMiddle m' hcm' hmb' hlow'
      obtain ⟨e, hme, heq⟩ := hentry e' hme'
      exact heq.mp (hrecord m e hcm hmb
        (fun s hs => (hmid s hs).mpr (hlow' s hs)) hme)
  · intro h
    obtain ⟨hcb, hlow, had, hrecord⟩ := hy.mp h
    apply hx.mpr
    refine ⟨hcolumns.mpr hcb, ?_, hentries.mpr had, ?_⟩
    · intro s hs
      exact (hbelow s hs).mpr (hlow s hs)
    · intro m e hcm hmb hlow' hme
      obtain ⟨m', hcm', hmb', hmid, hentry⟩ := hsourceMiddle m hcm hmb hlow'
      obtain ⟨e', hme', heq⟩ := hentry e hme
      exact heq.mpr (hrecord m' e' hcm' hmb'
        (fun s hs => (hmid s hs).mp (hlow' s hs)) hme')

#print axioms member_iff_record_all_l
#print axioms member_iff_of_middle_transport_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformAncestorRecordAllRows
