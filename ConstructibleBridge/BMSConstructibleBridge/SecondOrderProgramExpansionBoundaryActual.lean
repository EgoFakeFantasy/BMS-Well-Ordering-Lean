import BMSConstructibleBridge.SecondOrderProgramExpansionBoundaryRows
import BMSConstructibleBridge.SecondOrderProgramExpansionSelected

/-!
# 完整展开输出的无中间见证边界接口

从一次真实 `expand_m` 图调用自动取出坏块、成功正文和裁剪高度，
对所有内部 `t < k` 与 `row < maximal` 返回 Hunter Lemma 2.5(iii)
的边界祖先对应。`k=0` 时副本边界量化为空，无需额外正性前提。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionBoundaryActual

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics SecondOrderProgramTotality
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

/-- 完整真实展开在最大父行以下保持全部相邻副本边界祖先查询。 -/
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
    {x j p d k maximal height y : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hmax : relation_l W x (succ_l maximal))
    (hlast : relation_l I x j)
    (hparent : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hy : relation_l X (value_l x k) y) :
    ∀ row, SecondOrderOrder.lt_l row maximal →
      ∀ t i, SecondOrderOrder.lt_l t k → SecondOrderOrder.lt_l i d →
      (¬relation_l M
        (value_l (value_l (value_l x row) j) (add_l p i)) (zero_l ℳ) ↔
        ¬relation_l M
          (value_l (value_l (value_l y row) (add_l p (mul_l d (succ_l t))))
            (add_l p (add_l (mul_l d t) i))) (zero_l ℳ)) := by
  letI := order_l hℳ
  obtain ⟨bad, hbad, _⟩ :=
    function_of_semantics_l hℳ bad_m hB
      (value_l x (value_l k (value_l maximal p)))
  obtain ⟨v, hv, htrim⟩ :=
    (SecondOrderProgramExpansionSelected.expand_some_l
      hℳ hX hW hP hI hS hT hmax hlast hparent k y).mp hy
  obtain ⟨z, hz, _⟩ := function_of_semantics_l hℳ
    SecondOrderProgramTrimHeight.trim_m hZ v
  intro row hrow t i ht hi
  have hk : SecondOrderOrder.lt_l (zero_l ℳ) k :=
    lt_of_le_of_lt (zero_le_l hℳ t) ht
  exact SecondOrderProgramExpansionBoundaryRows.member_congr_below_maximal_l
    hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc hM hO
      hx hmax hlast hparent hd hbad hy hv htrim hz hk row hrow t i ht hi

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionBoundaryActual
