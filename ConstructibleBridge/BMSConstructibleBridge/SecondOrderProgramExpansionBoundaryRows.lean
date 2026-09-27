import BMSConstructibleBridge.SecondOrderProgramExpansionBoundaryStep
import BMSConstructibleBridge.SecondOrderProgramExpansionBoundarySync
import BMSConstructibleBridge.SecondOrderProgramExpansionBoundarySource
import BMSConstructibleBridge.SecondOrderProgramExpansionParameterEntries
import BMSConstructibleBridge.SecondOrderProgramExpansionTrimLowerBound

/-!
# 相邻副本边界的全部内部行祖先对应

真实展开成功分支的当前行推进与对象语言逐行同步公式在此合并。
归纳发生在模型内部自然数上，覆盖非标准行号；行必须同时低于
原最大父行和实际裁剪后高度。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionBoundaryRows

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramExpansion (expand_m)
open SecondOrderProgramExpansionSuccess (bad_m success_m)
open SecondOrderProgramMaximalParentRow (maximal_m last_index_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramSubtraction (sub_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramAscending (ascending_m)
open SecondOrderProgramOptionalLookup (optional_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 真实成功展开中，每个内部副本边界在全部保留的低行上与原末列同步。 -/
theorem member_congr_l (hℳ : Theory.Models ℳ theory_m)
    {X W P I S T Z B L E D J Asc M O : set_l ℳ}
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
    (hO : graph_semantics_l (graph_m optional_m) O)
    {x j p d k maximal bad height y v z : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hmax : relation_l W x (succ_l maximal))
    (hlast : relation_l I x j)
    (hparent : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hbad : relation_l B (value_l x (value_l k (value_l maximal p))) bad)
    (hy : relation_l X (value_l x k) y)
    (hv : relation_l S (value_l x (value_l k (value_l maximal p))) v)
    (htrim : relation_l T v y)
    (hz : relation_l Z v z) :
    letI := SecondOrderAlgebra.order_l hℳ
    ∀ row, SecondOrderOrder.lt_l row (min maximal z) →
      ∀ t i, SecondOrderOrder.lt_l t k → SecondOrderOrder.lt_l i d →
      (¬relation_l M
        (value_l (value_l (value_l x row) j) (add_l p i)) (zero_l ℳ) ↔
        ¬relation_l M
          (value_l (value_l (value_l y row) (add_l p (mul_l d (succ_l t))))
            (add_l p (add_l (mul_l d t) i))) (zero_l ℳ)) := by
  letI := SecondOrderAlgebra.order_l hℳ
  apply SecondOrderProgramExpansionBoundarySync.all_rows_of_step_l hℳ
  intro row ih hr t i ht hi
  change row < min maximal z at hr
  have hbound := (lt_min_iff.mp hr)
  apply SecondOrderProgramExpansionBoundaryStep.member_iff_of_below_l
    hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc hM hO
      hx hmax hlast hparent hd hbad hy hv htrim hz ht hi hbound.1 hbound.2
  intro s hs q hq
  exact ih s hs (SecondOrderOrder.trans_l hℳ hs hr) t q ht hq

/-- 原末列最大父行的首列父边产生相邻真实副本首列的祖先边。 -/
theorem adjacent_first_l (hℳ : Theory.Models ℳ theory_m)
    {X W P I S T Z B L E D J Asc M O : set_l ℳ}
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
    (hO : graph_semantics_l (graph_m optional_m) O)
    {x j p d k maximal bad height y v z row t : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hmax : relation_l W x (succ_l maximal))
    (hlast : relation_l I x j)
    (hparent : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hbad : relation_l B (value_l x (value_l k (value_l maximal p))) bad)
    (hy : relation_l X (value_l x k) y)
    (hv : relation_l S (value_l x (value_l k (value_l maximal p))) v)
    (htrim : relation_l T v y)
    (hz : relation_l Z v z)
    (hrowmax : SecondOrderOrder.lt_l row maximal)
    (hrowz : SecondOrderOrder.lt_l row z)
    (ht : SecondOrderOrder.lt_l t k) :
    ¬relation_l M
      (value_l (value_l (value_l y row) (add_l p (mul_l d (succ_l t))))
        (add_l p (mul_l d t))) (zero_l ℳ) := by
  letI := SecondOrderAlgebra.order_l hℳ
  have hpj := SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hparent
  have hdpos := SecondOrderProgramExpansionParameterEntries.width_pos_l
    hℳ hD hpj hd
  have hrowmin : SecondOrderOrder.lt_l row (min maximal z) := by
    change row < min maximal z
    exact lt_min_iff.mpr ⟨hrowmax, hrowz⟩
  have hsync := member_congr_l hℳ hX hW hP hI hS hT hZ hB hL hE
    hD hJ hAsc hM hO hx hmax hlast hparent hd hbad hy hv htrim hz
      row hrowmin t (zero_l ℳ) ht hdpos
  have hsource : ¬relation_l M
      (value_l (value_l (value_l x row) j) (add_l p (zero_l ℳ)))
        (zero_l ℳ) := by
    simpa only [add_zero_l hℳ p] using
      SecondOrderProgramExpansionBoundarySource.member_below_parent_row_l
        hℳ hP hM hparent hrowmax
  simpa only [add_zero_l hℳ (mul_l d t)] using hsync.mp hsource

/-- 复制次数为正时，真实裁剪至少保留最大父行以下的所有行；
因此边界对应可写成 Hunter Lemma 2.5(iii) 的原行界。 -/
theorem member_congr_below_maximal_l (hℳ : Theory.Models ℳ theory_m)
    {X W P I S T Z B L E D J Asc M O : set_l ℳ}
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
    (hO : graph_semantics_l (graph_m optional_m) O)
    {x j p d k maximal bad height y v z : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hmax : relation_l W x (succ_l maximal))
    (hlast : relation_l I x j)
    (hparent : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hbad : relation_l B (value_l x (value_l k (value_l maximal p))) bad)
    (hy : relation_l X (value_l x k) y)
    (hv : relation_l S (value_l x (value_l k (value_l maximal p))) v)
    (htrim : relation_l T v y)
    (hz : relation_l Z v z)
    (hk : SecondOrderOrder.lt_l (zero_l ℳ) k) :
    ∀ row, SecondOrderOrder.lt_l row maximal →
      ∀ t i, SecondOrderOrder.lt_l t k → SecondOrderOrder.lt_l i d →
      (¬relation_l M
        (value_l (value_l (value_l x row) j) (add_l p i)) (zero_l ℳ) ↔
        ¬relation_l M
          (value_l (value_l (value_l y row) (add_l p (mul_l d (succ_l t))))
            (add_l p (add_l (mul_l d t) i))) (zero_l ℳ)) := by
  letI := order_l hℳ
  have hmaxle := SecondOrderProgramExpansionTrimLowerBound.maximal_le_l
    hℳ hP hI hS hB hL hE hD hJ hZ
      hx hlast hparent hd hbad hv hz hk
  intro row hrow t i ht hi
  have hrowz : SecondOrderOrder.lt_l row z := lt_of_lt_of_le hrow hmaxle
  have hrowmin : SecondOrderOrder.lt_l row (min maximal z) := by
    change row < min maximal z
    exact lt_min_iff.mpr ⟨hrow, hrowz⟩
  exact member_congr_l hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc hM hO
    hx hmax hlast hparent hd hbad hy hv htrim hz row hrowmin t i ht hi

#print axioms member_congr_l
#print axioms adjacent_first_l
#print axioms member_congr_below_maximal_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionBoundaryRows
