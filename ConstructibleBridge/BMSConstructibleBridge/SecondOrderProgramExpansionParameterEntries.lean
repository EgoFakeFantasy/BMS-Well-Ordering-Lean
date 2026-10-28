import BMSConstructibleBridge.SecondOrderProgramMaximalParentRow
import BMSConstructibleBridge.SecondOrderProgramExpansionBadBlock
import BMSConstructibleBridge.SecondOrderProgramEntrySpecification
import BMSConstructibleBridge.SecondOrderProgramExpansionBoundarySource
import BMSConstructibleBridge.SecondOrderProgramExpansionSuccessRectangular

/-!
# 实际展开参数列的读取身份

`copied_m` 的末列参数必须是原数组最后一列的真实列表码，不能仅凭
列号相等推测其逐行值。本模块先把该复合程序图拆回 `lookup_m`。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionParameterEntries

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramMaximalParentRow (last_index_m last_column_m)
open SecondOrderProgramExpansionSuccess (bad_m)
open SecondOrderProgramListCode (head_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramSubtraction (sub_m)
open SecondOrderProgramOptionalLookup (optional_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramRectangular (rectangular_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 实际末列参数图的输出，就是原数组实际末列索引处的列表码。 -/
theorem last_column_lookup_l (hℳ : Theory.Models ℳ theory_m) {I H E : set_l ℳ}
    (hI : graph_semantics_l (graph_m last_index_m) I)
    (hH : graph_semantics_l (graph_m last_column_m) H)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    {x j l : num_l ℳ}
    (hj : relation_l I x j) (hl : relation_l H x l) :
    relation_l E (value_l x j) l := by
  obtain ⟨A, _, hA⟩ := graph_total_l hℳ
    (.pair PrimitiveProgram.id_m last_index_m)
  obtain ⟨Id, _, hId⟩ := graph_total_l hℳ PrimitiveProgram.id_m
  obtain ⟨a, ha, he⟩ :=
    (comp_rel_l hℳ (graph_m lookup_m)
      (graph_m (.pair PrimitiveProgram.id_m last_index_m)) E A hE hA hH x l).mp hl
  obtain ⟨u, v, hu, hv, heq⟩ :=
    (pair_rel_l hℳ (graph_m PrimitiveProgram.id_m) (graph_m last_index_m)
      Id I hId hI hA x a).mp ha
  have hux : x = u := (id_spec_l hℳ hId x u).mp hu
  have hvj : v = j :=
    function_value_unique_l (function_of_semantics_l hℳ last_index_m hI) hv hj
  subst u
  subst v
  exact heq ▸ he

/-- 父列严格早于末列时，原坏块的内部宽度非零。 -/
theorem width_pos_l (hℳ : Theory.Models ℳ theory_m) {D : set_l ℳ}
    (hD : graph_semantics_l (graph_m sub_m) D)
    {j p d : num_l ℳ} (hpj : SecondOrderOrder.lt_l p j)
    (hd : relation_l D (value_l j p) d) :
    SecondOrderOrder.lt_l (zero_l ℳ) d := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  have hda : add_l d p = j :=
    SecondOrderProgramSubtractionBounds.sub_add_l hℳ hD hd (Or.inr hpj)
  by_contra hnot
  have hle : d ≤ zero_l ℳ := le_of_not_gt hnot
  have hdz : d = zero_l ℳ := le_antisymm hle (zero_le_l hℳ d)
  rw [hdz, SecondOrderNumbers.zero_add_l hℳ p] at hda
  exact (ne_of_lt hpj) hda

/-- 实际坏块的首列参数就是原数组父列的列表码。 -/
theorem bad_head_lookup_l (hℳ : Theory.Models ℳ theory_m) {B H L E D : set_l ℳ}
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hH : graph_semantics_l (graph_m head_m) H)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hD : graph_semantics_l (graph_m sub_m) D)
    {x j p d k maximal b f : num_l ℳ}
    (hx : relation_l L x (succ_l j))
    (hpj : SecondOrderOrder.lt_l p j)
    (hd : relation_l D (value_l j p) d)
    (hb : relation_l B (value_l x (value_l k (value_l maximal p))) b)
    (hf : relation_l H b f) : relation_l E (value_l x p) f := by
  letI := order_l hℳ
  have hdp := width_pos_l hℳ hD hpj hd
  have hb0 : relation_l E (value_l b (zero_l ℳ)) f :=
    (SecondOrderProgramListLookup.lookup_zero_l hℳ hE hH b f).mpr hf
  have hpx := (SecondOrderProgramExpansionBadBlock.bad_lookup_l
    hℳ hB hL hE hD hx (Or.inr hpj) hd hb hdp f).mp hb0
  simpa only [add_zero_l hℳ p] using hpx

/-- 实际坏块第零列的 some 坐标正是其首列参数的 some 坐标。 -/
theorem bad_first_entry_l (hℳ : Theory.Models ℳ theory_m)
    {B H L E D O J : set_l ℳ}
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hH : graph_semantics_l (graph_m head_m) H)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hD : graph_semantics_l (graph_m sub_m) D)
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    {x j p d k maximal b f height row a : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hpj : SecondOrderOrder.lt_l p j)
    (hd : relation_l D (value_l j p) d)
    (hb : relation_l B (value_l x (value_l k (value_l maximal p))) b)
    (hf : relation_l H b f)
    (ha : relation_l O (value_l f row) (succ_l a)) :
    relation_l J (value_l b (value_l (zero_l ℳ) row)) (succ_l a) := by
  have hbr := SecondOrderProgramExpansionSuccessRectangular.bad_rectangular_l
    hℳ hB hL hE hD hx (Or.inr hpj) hd hb
  have hb0 : relation_l E (value_l b (zero_l ℳ)) f :=
    (SecondOrderProgramListLookup.lookup_zero_l hℳ hE hH b f).mpr hf
  have hopt := (SecondOrderProgramEntrySpecification.optional_some_l
    hℳ hO hL hE hbr.1 (zero_l ℳ) f).mpr
      ⟨width_pos_l hℳ hD hpj hd, hb0⟩
  exact (SecondOrderProgramEntrySpecification.entry_column_l
    hℳ hJ hO hopt row (succ_l a)).mpr ha

/-- 原最大父行以下，实际复制程序读取的首末列参数具有同一个正差值。 -/
theorem parameter_gap_l (hℳ : Theory.Models ℳ theory_m)
    {P M J D I Last B H L E O : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hD : graph_semantics_l (graph_m sub_m) D)
    (hI : graph_semantics_l (graph_m last_index_m) I)
    (hLast : graph_semantics_l (graph_m last_column_m) Last)
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hH : graph_semantics_l (graph_m head_m) H)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hO : graph_semantics_l (graph_m optional_m) O)
    {x j p k maximal row b f l : num_l ℳ}
    (hx : relation_l L x (succ_l j))
    (hj : relation_l I x j)
    (hparent : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hrow : SecondOrderOrder.lt_l row maximal)
    (hb : relation_l B (value_l x (value_l k (value_l maximal p))) b)
    (hf : relation_l H b f)
    (hl : relation_l Last x l) :
    ∃ a c gap, relation_l O (value_l f row) (succ_l a) ∧
      relation_l O (value_l l row) (succ_l c) ∧
      relation_l J (value_l x (value_l p row)) (succ_l a) ∧
      relation_l J (value_l x (value_l j row)) (succ_l c) ∧
      relation_l D (value_l c a) gap ∧
      SecondOrderOrder.lt_l (zero_l ℳ) gap ∧ add_l a gap = c := by
  have hpj := SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hparent
  obtain ⟨width, hwidth, _⟩ :=
    function_of_semantics_l hℳ sub_m hD (value_l j p)
  have hfirst := bad_head_lookup_l hℳ hB hH hL hE hD hx hpj hwidth hb hf
  have hlast := last_column_lookup_l hℳ hI hLast hE hj hl
  obtain ⟨a, c, gap, ha, hc, hd, hpos, hsum⟩ :=
    SecondOrderProgramExpansionBoundarySource.positive_entry_gap_l
      hℳ hP hM hJ hD hparent hrow
  have hpf : relation_l O (value_l x p) (succ_l f) :=
    (SecondOrderProgramEntrySpecification.optional_some_l hℳ hO hL hE hx p f).mpr
      ⟨SecondOrderOrder.trans_l hℳ hpj (lt_own_succ_l hℳ j), hfirst⟩
  have hjl : relation_l O (value_l x j) (succ_l l) :=
    (SecondOrderProgramEntrySpecification.optional_some_l hℳ hO hL hE hx j l).mpr
      ⟨lt_own_succ_l hℳ j, hlast⟩
  have hfa := (SecondOrderProgramEntrySpecification.entry_column_l
    hℳ hJ hO hpf row (succ_l a)).mp ha
  have hlc := (SecondOrderProgramEntrySpecification.entry_column_l
    hℳ hJ hO hjl row (succ_l c)).mp hc
  exact ⟨a, c, gap, hfa, hlc, ha, hc, hd, hpos, hsum⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionParameterEntries
