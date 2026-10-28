import BMSConstructibleBridge.SecondOrderProgramExpansionCopyEntry
import BMSConstructibleBridge.SecondOrderProgramBadBlockEntry
import BMSConstructibleBridge.SecondOrderProgramCopyEntryOrder
import BMSConstructibleBridge.SecondOrderProgramEntryOrderTransport
import BMSConstructibleBridge.SecondOrderProgramRectangularHeight
import BMSConstructibleBridge.SecondOrderProgramExpansionAscendingBoundary

/-!
# 同一实际副本内部的条目比较对应

原坏块的局部两列、实际 `copy_m` 输出的两列，以及完整 `expand_m`
对应副本的两列，在相同上升分支时有同一严格坐标比较。
两个输出见证分别由实际程序图的函数唯一性对齐。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionInsideCopyEntryOrder

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramExpansion (expand_m)
open SecondOrderProgramExpansionSuccess (bad_m success_m)
open SecondOrderProgramMaximalParentRow (maximal_m last_index_m last_column_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramListCode (head_m)
open SecondOrderProgramSubtraction (sub_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramCopyBlock (copy_m)
open SecondOrderProgramAscending (ascending_m)
open SecondOrderProgramOptionalLookup (optional_m)
open SecondOrderProgramUniformParentComparison (entry_order_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 相同上升分支下，同一实际副本中两局部列的当前行严格比较与原数组一致。 -/
theorem entry_order_congr_l (hℳ : Theory.Models ℳ theory_m)
    {X W P I S T Z B L E D J Asc : set_l ℳ}
    (hX : graph_semantics_l (graph_m expand_m) X)
    (hW : graph_semantics_l (graph_m maximal_m) W)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hI : graph_semantics_l (graph_m last_index_m) I)
    (hS : graph_semantics_l (graph_m success_m) S)
    (hT : graph_semantics_l (graph_m SecondOrderProgramTrimArray.trim_m) T)
    (hZ : graph_semantics_l (graph_m SecondOrderProgramTrimHeight.trim_m) Z)
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hD : graph_semantics_l (graph_m sub_m) D)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hAsc : graph_semantics_l (graph_m ascending_m) Asc)
    {x j p d k maximal b height y copy row i q : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hmax : relation_l W x (succ_l maximal))
    (hlast : relation_l I x j)
    (hparent : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hb : relation_l B (value_l x (value_l k (value_l maximal p))) b)
    (hy : relation_l X (value_l x k) y)
    (hcopy : SecondOrderOrder.lt_l copy (succ_l k))
    (hi : SecondOrderOrder.lt_l i d)
    (hq : SecondOrderOrder.lt_l q d)
    (hflag : relation_l Asc
      (value_l (value_l x (value_l maximal p)) (value_l i row)) (zero_l ℳ) ↔
      relation_l Asc
        (value_l (value_l x (value_l maximal p)) (value_l q row)) (zero_l ℳ)) :
    ∃ v z, relation_l S (value_l x (value_l k (value_l maximal p))) v ∧
      relation_l T v y ∧ relation_l Z v z ∧
      (SecondOrderOrder.lt_l row z →
        (entry_order_l J x row (add_l p i) (add_l p q) ↔
          entry_order_l J y row
            (add_l p (add_l (mul_l d copy) i))
            (add_l p (add_l (mul_l d copy) q)))) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  obtain ⟨Q, _, hQ⟩ := graph_total_l hℳ copy_m
  obtain ⟨Last, _, hLast⟩ := graph_total_l hℳ last_column_m
  obtain ⟨H, hHf, hH⟩ := graph_total_l hℳ head_m
  obtain ⟨O, _, hO⟩ := graph_total_l hℳ optional_m
  obtain ⟨U, _, hU⟩ := graph_total_l hℳ SecondOrderProgramCopyOptional.update_m
  have hpj := SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hparent
  obtain ⟨v, z, l, blk, hv, htrim, hz, hl, hblk, hentryi⟩ :=
    SecondOrderProgramExpansionCopyEntry.entry_l
      hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ hQ hLast
        hx hmax hlast hparent hd hb hy hcopy hi
  obtain ⟨v', z', l', blk', hv', _, hz', hl', hblk', hentryq⟩ :=
    SecondOrderProgramExpansionCopyEntry.entry_l
      hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ hQ hLast
        hx hmax hlast hparent hd hb hy hcopy hq
  have hv_eq : v' = v :=
    function_value_unique_l (function_of_semantics_l hℳ success_m hS) hv' hv
  have hz_eq : z' = z :=
    function_value_unique_l
      (function_of_semantics_l hℳ SecondOrderProgramTrimHeight.trim_m hZ)
        (hv_eq ▸ hz') hz
  have hl_eq : l' = l :=
    function_value_unique_l (function_of_semantics_l hℳ last_column_m hLast) hl' hl
  have hblk_eq : blk' = blk :=
    function_value_unique_l (function_of_semantics_l hℳ copy_m hQ)
      (hl_eq ▸ hblk') hblk
  obtain ⟨f, hf, _⟩ := hHf b
  have hbr := SecondOrderProgramExpansionSuccessRectangular.bad_rectangular_l
    hℳ hB hL hE hD hx (Or.inr hpj) hd hb
  have hvr0 := SecondOrderProgramExpansionSuccessRectangular.success_rectangular_l
    hℳ hS hB hL hE hx hb hbr hv
  have hpn : p ≤ succ_l j :=
    Or.inr (SecondOrderOrder.trans_l hℳ hpj (lt_own_succ_l hℳ j))
  have hvr : rectangular_l L E v (add_l p (mul_l d (succ_l k))) height := by
    simpa only [min_eq_right hpn] using hvr0
  have htrimle : z ≤ height :=
    SecondOrderProgramRectangularHeight.trim_le_l hℳ hZ hL hE hvr hz
  refine ⟨v, z, hv, htrim, hz, ?_⟩
  intro hrowz
  have hrheight : SecondOrderOrder.lt_l row height := lt_of_lt_of_le hrowz htrimle
  have hrowz' : SecondOrderOrder.lt_l row z' := by simpa only [hz_eq] using hrowz
  have hsource : entry_order_l J x row (add_l p i) (add_l p q) ↔
      entry_order_l J b row i q :=
    SecondOrderProgramEntryOrderTransport.entry_order_congr_l J
    (fun a => (SecondOrderProgramBadBlockEntry.entry_l hℳ hB hL hE hD hJ
      (row := row) hx.1 hpj hd hb hi a).symm)
    (fun a => (SecondOrderProgramBadBlockEntry.entry_l hℳ hB hL hE hD hJ
      (row := row) hx.1 hpj hd hb hq a).symm)
  have hcopyOrder := SecondOrderProgramCopyEntryOrder.entry_order_congr_l
    hℳ hQ hH hL hE hAsc hO hU hD hJ hbr hf hblk hrheight hi hq hflag
  have houtput : entry_order_l J blk row i q ↔
      entry_order_l J y row
        (add_l p (add_l (mul_l d copy) i))
        (add_l p (add_l (mul_l d copy) q)) :=
    SecondOrderProgramEntryOrderTransport.entry_order_congr_l J
    (fun a => (hentryi a hrowz).symm)
    (fun a => by
      have h := hentryq a hrowz'
      simpa only [hblk_eq] using h.symm)
  exact hsource.trans (hcopyOrder.trans houtput)

/-- 零上升坐标在实际展开的零号副本与任意副本中保留同一条目。 -/
theorem entry_value_congr_of_zero_l (hℳ : Theory.Models ℳ theory_m)
    {X W P I S T Z B L E D J Asc : set_l ℳ}
    (hX : graph_semantics_l (graph_m expand_m) X)
    (hW : graph_semantics_l (graph_m maximal_m) W)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hI : graph_semantics_l (graph_m last_index_m) I)
    (hS : graph_semantics_l (graph_m success_m) S)
    (hT : graph_semantics_l (graph_m SecondOrderProgramTrimArray.trim_m) T)
    (hZ : graph_semantics_l (graph_m SecondOrderProgramTrimHeight.trim_m) Z)
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hD : graph_semantics_l (graph_m sub_m) D)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hAsc : graph_semantics_l (graph_m ascending_m) Asc)
    {x j p d k maximal b height y copy row i : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hmax : relation_l W x (succ_l maximal))
    (hlast : relation_l I x j)
    (hparent : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hb : relation_l B (value_l x (value_l k (value_l maximal p))) b)
    (hy : relation_l X (value_l x k) y)
    (hcopy : SecondOrderOrder.lt_l copy (succ_l k))
    (hi : SecondOrderOrder.lt_l i d)
    (hzero : relation_l Asc
      (value_l (value_l x (value_l maximal p)) (value_l i row)) (zero_l ℳ)) :
    ∃ v z, relation_l S (value_l x (value_l k (value_l maximal p))) v ∧
    relation_l T v y ∧ relation_l Z v z ∧
    (SecondOrderOrder.lt_l row z →
      ∃ a, relation_l J (value_l y (value_l (add_l p i) row)) (succ_l a) ∧
        relation_l J
          (value_l y (value_l (add_l p (add_l (mul_l d copy) i)) row))
          (succ_l a)) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  obtain ⟨Q, _, hQ⟩ := graph_total_l hℳ copy_m
  obtain ⟨Last, _, hLast⟩ := graph_total_l hℳ last_column_m
  obtain ⟨H, _, hH⟩ := graph_total_l hℳ head_m
  obtain ⟨O, _, hO⟩ := graph_total_l hℳ optional_m
  obtain ⟨U, _, hU⟩ := graph_total_l hℳ SecondOrderProgramCopyOptional.update_m
  have hpj := SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hparent
  obtain ⟨v, z, l₀, blk₀, hv, htrim, hz, hl₀, hblk₀, hentry₀⟩ :=
    SecondOrderProgramExpansionCopyEntry.entry_l hℳ hX hW hP hI hS hT hZ hB
      hL hE hD hJ hQ hLast hx hmax hlast hparent hd hb hy
      (t := zero_l ℳ) (SecondOrderOrder.zero_succ_l hℳ k) hi
  obtain ⟨v', z', l₁, blk₁, hv', _, hz', hl₁, hblk₁, hentry₁⟩ :=
    SecondOrderProgramExpansionCopyEntry.entry_l hℳ hX hW hP hI hS hT hZ hB
      hL hE hD hJ hQ hLast hx hmax hlast hparent hd hb hy hcopy hi
  have hv_eq : v' = v :=
    function_value_unique_l (function_of_semantics_l hℳ success_m hS) hv' hv
  have hz_eq : z' = z :=
    function_value_unique_l (function_of_semantics_l hℳ
      SecondOrderProgramTrimHeight.trim_m hZ) (hv_eq ▸ hz') hz
  obtain ⟨f, hf, _⟩ := function_of_semantics_l hℳ head_m hH b
  have hbr := SecondOrderProgramExpansionSuccessRectangular.bad_rectangular_l
    hℳ hB hL hE hD hx (Or.inr hpj) hd hb
  have hvr0 := SecondOrderProgramExpansionSuccessRectangular.success_rectangular_l
    hℳ hS hB hL hE hx hb hbr hv
  have hpn : p ≤ succ_l j :=
    Or.inr (SecondOrderOrder.trans_l hℳ hpj (lt_own_succ_l hℳ j))
  have hvr : rectangular_l L E v (add_l p (mul_l d (succ_l k))) height := by
    simpa only [min_eq_right hpn] using hvr0
  have htrimle : z ≤ height :=
    SecondOrderProgramRectangularHeight.trim_le_l hℳ hZ hL hE hvr hz
  refine ⟨v, z, hv, htrim, hz, ?_⟩
  intro hrowz
  have hrowz' : SecondOrderOrder.lt_l row z' := by simpa only [hz_eq] using hrowz
  have hrheight : SecondOrderOrder.lt_l row height := lt_of_lt_of_le hrowz htrimle
  obtain ⟨a, hblock₀, hblock₁⟩ :=
    SecondOrderProgramCopyEntryOrder.entry_value_common_of_zero_l
      hℳ hQ hH hL hE hAsc hO hU hJ hbr hf hblk₀ hblk₁ hi hrheight hzero
  have hactual₀ := (hentry₀ (succ_l a) hrowz).mpr hblock₀
  have hactual₁ := (hentry₁ (succ_l a) hrowz').mpr hblock₁
  refine ⟨a, ?_, hactual₁⟩
  simpa only [mul_zero_l hℳ d, SecondOrderNumbers.zero_add_l hℳ] using hactual₀

/-- 两个局部列都在全部低行连向原末列时，真实上升条件可自动消去。 -/
theorem entry_order_of_below_l (hℳ : Theory.Models ℳ theory_m)
    {X W P I S T Z B L E D J Asc M : set_l ℳ}
    (hX : graph_semantics_l (graph_m expand_m) X)
    (hW : graph_semantics_l (graph_m maximal_m) W)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hI : graph_semantics_l (graph_m last_index_m) I)
    (hS : graph_semantics_l (graph_m success_m) S)
    (hT : graph_semantics_l (graph_m SecondOrderProgramTrimArray.trim_m) T)
    (hZ : graph_semantics_l (graph_m SecondOrderProgramTrimHeight.trim_m) Z)
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hD : graph_semantics_l (graph_m sub_m) D)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hAsc : graph_semantics_l (graph_m ascending_m) Asc)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {x j p d k maximal b height y copy row i q ai aq : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hmax : relation_l W x (succ_l maximal))
    (hlast : relation_l I x j)
    (hparent : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hb : relation_l B (value_l x (value_l k (value_l maximal p))) b)
    (hy : relation_l X (value_l x k) y)
    (hcopy : SecondOrderOrder.lt_l copy (succ_l k))
    (hrow : SecondOrderOrder.lt_l row maximal)
    (hi : SecondOrderOrder.lt_l i d)
    (hq : SecondOrderOrder.lt_l q d)
    (hei : relation_l J (value_l x (value_l (add_l p i) row)) (succ_l ai))
    (heq : relation_l J (value_l x (value_l (add_l p q) row)) (succ_l aq))
    (hbelowi : ∀ s, SecondOrderOrder.lt_l s row →
      ¬relation_l M
        (value_l (value_l (value_l x s) j) (add_l p i)) (zero_l ℳ))
    (hbelowq : ∀ s, SecondOrderOrder.lt_l s row →
      ¬relation_l M
        (value_l (value_l (value_l x s) j) (add_l p q)) (zero_l ℳ)) :
    ∃ v z, relation_l S (value_l x (value_l k (value_l maximal p))) v ∧
      relation_l T v y ∧ relation_l Z v z ∧
      (SecondOrderOrder.lt_l row z →
        (entry_order_l J x row (add_l p i) (add_l p q) ↔
          entry_order_l J y row
            (add_l p (add_l (mul_l d copy) i))
            (add_l p (add_l (mul_l d copy) q)))) := by
  have hzi := SecondOrderProgramExpansionAscendingBoundary.nonzero_l
    hℳ hP hM hAsc hJ hL hD hx.1 hparent hd hrow hi hei hbelowi
  have hzq := SecondOrderProgramExpansionAscendingBoundary.nonzero_l
    hℳ hP hM hAsc hJ hL hD hx.1 hparent hd hrow hq heq hbelowq
  have hflags : relation_l Asc
      (value_l (value_l x (value_l maximal p)) (value_l i row)) (zero_l ℳ) ↔
      relation_l Asc
        (value_l (value_l x (value_l maximal p)) (value_l q row)) (zero_l ℳ) := by
    exact iff_of_false hzi hzq
  exact entry_order_congr_l hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc
    hx hmax hlast hparent hd hb hy hcopy hi hq hflags

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionInsideCopyEntryOrder
