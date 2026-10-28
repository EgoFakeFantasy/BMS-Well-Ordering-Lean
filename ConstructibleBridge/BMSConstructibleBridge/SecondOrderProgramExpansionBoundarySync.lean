import BMSConstructibleBridge.SecondOrderProgramUniformAncestorRows
import BMSConstructibleBridge.SecondOrderProgramArithmetic
import BMSConstructibleBridge.SecondOrderListInduction

/-!
# 相邻副本边界的模型内部逐行同步公式

对固定原数组、展开数组及边界参数，本公式在每一内部行同时量化全部副本号
和坏块局部候选列。后续强归纳直接使用该公式，不能对非标准行号做宿主归纳。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionBoundarySync

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderProgramArithmetic

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private def addT {Γ Δ : SortContext signature_m} (a b : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .add (.cons a (.cons b .nil))

private def mulT {Γ Δ : SortContext signature_m} (a b : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .mul (.cons a (.cons b .nil))

private def succT {Γ Δ : SortContext signature_m} (a : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .succ (.cons a .nil)

/-- 当前内部行上，原候选到原末列与前一副本候选到下一首列同步。 -/
def sync_m {Γ Δ : SortContext signature_m} (M : Term signature_m Γ Δ .set)
    (x y j p d k h r : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  let M' := (M.weakenBound sort_m.num).weakenBound sort_m.num
  let x' := (x.weakenBound sort_m.num).weakenBound sort_m.num
  let y' := (y.weakenBound sort_m.num).weakenBound sort_m.num
  let j' := (j.weakenBound sort_m.num).weakenBound sort_m.num
  let p' := (p.weakenBound sort_m.num).weakenBound sort_m.num
  let d' := (d.weakenBound sort_m.num).weakenBound sort_m.num
  let k' := (k.weakenBound sort_m.num).weakenBound sort_m.num
  let r' := (r.weakenBound sort_m.num).weakenBound sort_m.num
  let t : Term signature_m (.num :: .num :: Γ) Δ .num := .bvar (.there .here)
  let i : Term signature_m (.num :: .num :: Γ) Δ .num := .bvar .here
  .imp (PrimitiveFormulas.lt_m r h)
    (.forallE .num (.forallE .num
      (.imp (PrimitiveFormulas.lt_m t k')
        (.imp (PrimitiveFormulas.lt_m i d')
          (.iff
            (SecondOrderProgramUniformAncestorRows.row_m M' x' r' j' (addT p' i))
            (SecondOrderProgramUniformAncestorRows.row_m M' y' r'
              (addT p' (mulT d' (succT t)))
              (addT p' (addT (mulT d' t) i))))))))

theorem sync_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (M : Term signature_m Γ Δ .set)
    (x y j p d k h r : Term signature_m Γ Δ .num) :
    (sync_m M x y j p d k h r).satisfies η ↔
      (SecondOrderOrder.lt_l (r.eval η) (h.eval η) → ∀ t i,
        SecondOrderOrder.lt_l t (k.eval η) →
        SecondOrderOrder.lt_l i (d.eval η) →
        (¬relation_l (M.eval η)
            (value_l (value_l (value_l (x.eval η) (r.eval η)) (j.eval η))
              (add_l (p.eval η) i)) (zero_l ℳ) ↔
          ¬relation_l (M.eval η)
            (value_l (value_l (value_l (y.eval η) (r.eval η))
              (add_l (p.eval η) (mul_l (d.eval η) (succ_l t))))
              (add_l (p.eval η) (add_l (mul_l (d.eval η) t) i)))
                (zero_l ℳ))) := by
  simp only [sync_m, Formula.satisfies, SecondOrderOrder.formula_l,
    SecondOrderProgramUniformAncestorRows.row_formula_l,
    addT, mulT, succT, Term.eval, Arguments.eval]
  simp only [Term.eval_weakenBound]
  simp only [FirstOrder.Env.pushBound, FirstOrder.Assignment.push,
    SecondOrderModel.add_l, SecondOrderModel.mul_l, SecondOrderModel.succ_l]

private abbrev Δ : SortContext signature_m :=
  [.num, .num, .num, .num, .num, .num, .num, .set]

private def rows_m : Formula signature_m [] (.num :: Δ) :=
  sync_m
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there .here)))
    (.fvar (.there .here))
    (.fvar .here)

private def rows_base_env_l (M : set_l ℳ) (x y j p d k h : num_l ℳ) :
    Env ℳ [] Δ :=
  ((((((((Env.empty (M := ℳ)).pushFree M).pushFree x).pushFree y).pushFree j).pushFree p)
    |>.pushFree d).pushFree k).pushFree h

private theorem rows_syntax_l (M : set_l ℳ) (x y j p d k h r : num_l ℳ) :
    Formula.satisfies ((rows_base_env_l M x y j p d k h).pushFree r) rows_m ↔
      (SecondOrderOrder.lt_l r h → ∀ t i,
        SecondOrderOrder.lt_l t k → SecondOrderOrder.lt_l i d →
        (¬relation_l M (value_l (value_l (value_l x r) j) (add_l p i))
            (zero_l ℳ) ↔
          ¬relation_l M
            (value_l (value_l (value_l y r) (add_l p (mul_l d (succ_l t))))
              (add_l p (add_l (mul_l d t) i))) (zero_l ℳ))) := by
  simpa only [rows_m, rows_base_env_l, Term.eval, FirstOrder.Env.pushFree,
    FirstOrder.Assignment.push] using
    sync_formula_l ((rows_base_env_l M x y j p d k h).pushFree r)
      (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there .here)))
      (.fvar (.there .here))
      (.fvar .here)

/-- 若当前行同步可从所有更低内部行同步推出，则所有内部行同步。 -/
theorem all_rows_of_step_l (hℳ : Theory.Models ℳ theory_m) {M : set_l ℳ}
    {x y j p d k h : num_l ℳ}
    (hstep : ∀ r,
      (∀ s, SecondOrderOrder.lt_l s r →
        (SecondOrderOrder.lt_l s h → ∀ t i,
          SecondOrderOrder.lt_l t k → SecondOrderOrder.lt_l i d →
          (¬relation_l M (value_l (value_l (value_l x s) j) (add_l p i))
              (zero_l ℳ) ↔
            ¬relation_l M
              (value_l (value_l (value_l y s) (add_l p (mul_l d (succ_l t))))
                (add_l p (add_l (mul_l d t) i))) (zero_l ℳ)))) →
      (SecondOrderOrder.lt_l r h → ∀ t i,
        SecondOrderOrder.lt_l t k → SecondOrderOrder.lt_l i d →
        (¬relation_l M (value_l (value_l (value_l x r) j) (add_l p i))
            (zero_l ℳ) ↔
          ¬relation_l M
            (value_l (value_l (value_l y r) (add_l p (mul_l d (succ_l t))))
              (add_l p (add_l (mul_l d t) i))) (zero_l ℳ)))) :
    ∀ r, SecondOrderOrder.lt_l r h → ∀ t i,
      SecondOrderOrder.lt_l t k → SecondOrderOrder.lt_l i d →
      (¬relation_l M (value_l (value_l (value_l x r) j) (add_l p i))
          (zero_l ℳ) ↔
        ¬relation_l M
          (value_l (value_l (value_l y r) (add_l p (mul_l d (succ_l t))))
            (add_l p (add_l (mul_l d t) i))) (zero_l ℳ)) := by
  exact SecondOrderListInduction.strong_induct_l hℳ rows_m
    (pure_language_m _ rfl) (rows_base_env_l M x y j p d k h)
    (fun r => SecondOrderOrder.lt_l r h → ∀ t i,
      SecondOrderOrder.lt_l t k → SecondOrderOrder.lt_l i d →
      (¬relation_l M (value_l (value_l (value_l x r) j) (add_l p i))
          (zero_l ℳ) ↔
        ¬relation_l M
          (value_l (value_l (value_l y r) (add_l p (mul_l d (succ_l t))))
            (add_l p (add_l (mul_l d t) i))) (zero_l ℳ)))
    (rows_syntax_l M x y j p d k h) hstep

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionBoundarySync
