import BMSConstructibleBridge.SecondOrderListInduction
import BMSConstructibleBridge.SecondOrderProgramCopyAncestorForward
import BMSConstructibleBridge.SecondOrderProgramCopyAncestorReverse

/-!
# 源块与任意副本的全部内部行祖先同步

当前行的正、反两步只消费全部更低行的同步。这里用原二阶语言中的实际公式描述“本行
界内祖先同步”，再调用模型内部强归纳；行号可以是非标准内部自然数，不使用宿主 `Nat`
归纳或外部良基性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopyAncestorRows

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing
open SecondOrderProgramSemantics
open SecondOrderProgramCopyBlock (copy_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListCode (head_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramAscending (ascending_m)
open SecondOrderProgramOptionalLookup (optional_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramRectangular (rectangular_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 当前行低于高度时，源块与副本的全部界内祖先查询一致。 -/
def sync_m {Γ Δ : SortContext signature_m} (M : Term signature_m Γ Δ .set)
    (b blk w h r : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .imp (PrimitiveFormulas.lt_m r h) (.forallE .num (.forallE .num
    (.imp (PrimitiveFormulas.lt_m (.bvar (.there .here))
      ((w.weakenBound sort_m.num).weakenBound sort_m.num))
    (.imp (PrimitiveFormulas.lt_m (.bvar .here)
      ((w.weakenBound sort_m.num).weakenBound sort_m.num))
    (.iff
      (SecondOrderProgramUniformAncestorRows.row_m
        ((M.weakenBound sort_m.num).weakenBound sort_m.num)
        ((b.weakenBound sort_m.num).weakenBound sort_m.num)
        ((r.weakenBound sort_m.num).weakenBound sort_m.num) (.bvar .here)
        (.bvar (.there .here)))
      (SecondOrderProgramUniformAncestorRows.row_m
        ((M.weakenBound sort_m.num).weakenBound sort_m.num)
        ((blk.weakenBound sort_m.num).weakenBound sort_m.num)
        ((r.weakenBound sort_m.num).weakenBound sort_m.num) (.bvar .here)
        (.bvar (.there .here))))))))

theorem sync_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (M : Term signature_m Γ Δ .set) (b blk w h r : Term signature_m Γ Δ .num) :
    (sync_m M b blk w h r).satisfies η ↔
      (SecondOrderOrder.lt_l (r.eval η) (h.eval η) → ∀ i j,
        SecondOrderOrder.lt_l i (w.eval η) → SecondOrderOrder.lt_l j (w.eval η) →
        (¬relation_l (M.eval η)
            (value_l (value_l (value_l (b.eval η) (r.eval η)) j) i) (zero_l ℳ) ↔
          ¬relation_l (M.eval η)
            (value_l (value_l (value_l (blk.eval η) (r.eval η)) j) i) (zero_l ℳ))) := by
  simp only [sync_m, Formula.satisfies, SecondOrderOrder.formula_l,
    SecondOrderProgramUniformAncestorRows.row_formula_l, Term.eval_weakenBound]
  simp only [Term.eval, FirstOrder.Env.pushBound, FirstOrder.Assignment.push]

private def rows_m : Formula signature_m []
    [.num, .num, .num, .num, .num, .set] :=
  sync_m (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)

private def rows_base_env_l (M : set_l ℳ) (b blk w h : num_l ℳ) :
    Env ℳ [] [.num, .num, .num, .num, .set] :=
  ((((Env.empty (M := ℳ)).pushFree M).pushFree b).pushFree blk).pushFree w |>.pushFree h

private def rows_env_l (M : set_l ℳ) (b blk w h r : num_l ℳ) :
    Env ℳ [] [.num, .num, .num, .num, .num, .set] :=
  (rows_base_env_l M b blk w h).pushFree r

private theorem rows_syntax_l (M : set_l ℳ) (b blk w h r : num_l ℳ) :
    Formula.satisfies (rows_env_l M b blk w h r) rows_m ↔
      (SecondOrderOrder.lt_l r h → ∀ i j, SecondOrderOrder.lt_l i w →
        SecondOrderOrder.lt_l j w →
        (¬relation_l M (value_l (value_l (value_l b r) j) i) (zero_l ℳ) ↔
          ¬relation_l M (value_l (value_l (value_l blk r) j) i) (zero_l ℳ))) := by
  simpa only [rows_m, rows_env_l, rows_base_env_l, Term.eval, FirstOrder.Env.pushFree,
    FirstOrder.Assignment.push]
    using sync_formula_l
      (rows_env_l M b blk w h r)
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)

/-- 对所有内部行，源块与任意编号副本的界内祖先关系一致。 -/
theorem member_congr_l (hℳ : Theory.Models ℳ theory_m)
    {C H L E B O U D J M : set_l ℳ}
    (hC : graph_semantics_l (graph_m copy_m) C)
    (hH : graph_semantics_l (graph_m head_m) H)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hB : graph_semantics_l (graph_m ascending_m) B)
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hU : graph_semantics_l (graph_m SecondOrderProgramCopyOptional.update_m) U)
    (hD : graph_semantics_l (graph_m SecondOrderProgramSubtraction.sub_m) D)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {x n height b w h m p k l blk f : num_l ℳ}
    (hx : rectangular_l L E x n height) (hb : rectangular_l L E b w h)
    (hpw : add_l p w = n ∨ SecondOrderOrder.lt_l (add_l p w) n)
    (hh : h = height ∨ SecondOrderOrder.lt_l h height)
    (hf : relation_l H b f)
    (hblk : relation_l C
      (value_l b (value_l (value_l x (value_l m p)) (value_l k l))) blk)
    (hsource : ∀ s u v, SecondOrderOrder.lt_l s h →
      SecondOrderOrder.lt_l u w → SecondOrderOrder.lt_l v w →
      (¬relation_l M (value_l (value_l (value_l b s) v) u) (zero_l ℳ)) →
      ¬relation_l M
        (value_l (value_l (value_l x s) (add_l p v)) (add_l p u)) (zero_l ℳ)) :
    ∀ r, SecondOrderOrder.lt_l r h → ∀ i j,
      SecondOrderOrder.lt_l i w → SecondOrderOrder.lt_l j w →
      (¬relation_l M (value_l (value_l (value_l b r) j) i) (zero_l ℳ) ↔
        ¬relation_l M (value_l (value_l (value_l blk r) j) i) (zero_l ℳ)) := by
  let P (r : num_l ℳ) : Prop := SecondOrderOrder.lt_l r h → ∀ i j,
    SecondOrderOrder.lt_l i w → SecondOrderOrder.lt_l j w →
    (¬relation_l M (value_l (value_l (value_l b r) j) i) (zero_l ℳ) ↔
      ¬relation_l M (value_l (value_l (value_l blk r) j) i) (zero_l ℳ))
  apply SecondOrderListInduction.strong_induct_l hℳ rows_m (pure_language_m _ rfl)
    (rows_base_env_l M b blk w h)
    P (rows_syntax_l M b blk w h) ?_
  intro r ih hr i j hi hj
  have hbelow (s : num_l ℳ) (hs : SecondOrderOrder.lt_l s r) (u v : num_l ℳ)
      (hu : SecondOrderOrder.lt_l u w) (hv : SecondOrderOrder.lt_l v w) :=
    ih s hs (SecondOrderOrder.trans_l hℳ hs hr) u v hu hv
  constructor
  · exact SecondOrderProgramCopyAncestorForward.member_of_source_l
      hℳ hC hH hL hE hB hO hU hD hJ hM hb hf hblk hr hi hj hsource hbelow
  · exact SecondOrderProgramCopyAncestorReverse.member_source_of_copy_l
      hℳ hC hH hL hE hB hO hU hD hJ hM hx hb hpw hh hf hblk hr hi hj hsource hbelow

#print axioms sync_m
#print axioms sync_formula_l
#print axioms member_congr_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopyAncestorRows
