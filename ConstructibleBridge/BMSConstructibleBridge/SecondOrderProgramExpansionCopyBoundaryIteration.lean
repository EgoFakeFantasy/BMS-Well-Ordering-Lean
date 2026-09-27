import BMSConstructibleBridge.SecondOrderProgramUniformAncestorRows

/-!
# 相邻副本首列祖先的内部迭代

只要给定真实成员程序在每一对相邻副本首列间的祖先边，模型内部归纳就把它们
传递到第零与任意较晚副本之间。归纳变量是模型内部副本编号，不把非标准副本数
当成宿主自然数处理。相邻边的证明须由实际展开程序另行提供。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionCopyBoundaryIteration

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private abbrev Δ : SortContext signature_m := [.set, .num, .num, .num, .num, .num]
private abbrev Φ : SortContext signature_m := .num :: Δ

private def addT {Γ Δ : SortContext signature_m} (a b : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .add (.cons a (.cons b .nil))

private def mulT {Γ Δ : SortContext signature_m} (a b : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .mul (.cons a (.cons b .nil))

private def succT {Γ Δ : SortContext signature_m} (a : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .succ (.cons a .nil)

private def slot_s {Γ : SortContext signature_m} : Term signature_m Γ Φ .num := .fvar .here
private def slot_M {Γ : SortContext signature_m} : Term signature_m Γ Φ .set :=
  .fvar (.there .here)
private def slot_y {Γ : SortContext signature_m} : Term signature_m Γ Φ .num :=
  .fvar (.there (.there .here))
private def slot_row {Γ : SortContext signature_m} : Term signature_m Γ Φ .num :=
  .fvar (.there (.there (.there .here)))
private def slot_p {Γ : SortContext signature_m} : Term signature_m Γ Φ .num :=
  .fvar (.there (.there (.there (.there .here))))
private def slot_d {Γ : SortContext signature_m} : Term signature_m Γ Φ .num :=
  .fvar (.there (.there (.there (.there (.there .here)))))
private def slot_k {Γ : SortContext signature_m} : Term signature_m Γ Φ .num :=
  .fvar (.there (.there (.there (.there (.there (.there .here))))))

/-- 第 `s+1` 个副本首列以第零副本首列为祖先的有界归纳正文。 -/
def connected_m : Formula signature_m [] Φ :=
  .imp (PrimitiveFormulas.lt_m slot_s slot_k)
    (SecondOrderProgramUniformAncestorRows.row_m slot_M slot_y slot_row
      (addT slot_p (mulT slot_d (succT slot_s))) slot_p)

theorem connected_language_m : language_m connected_m = true := pure_language_m _ rfl

private def envSlots (M : set_l ℳ) (y row p d k : num_l ℳ) : Env ℳ [] Δ :=
  let η₀ := Env.pushFree (Env.empty (M := ℳ)) k
  let η₁ := Env.pushFree η₀ d
  let η₂ := Env.pushFree η₁ p
  let η₃ := Env.pushFree η₂ row
  let η₄ := Env.pushFree η₃ y
  Env.pushFree η₄ M

theorem connected_syntax_l (M : set_l ℳ) (y row p d k s : num_l ℳ) :
    Formula.satisfies (Env.pushFree (envSlots M y row p d k) s) connected_m ↔
      SecondOrderOrder.lt_l s k →
        ¬relation_l M
          (value_l (value_l (value_l y row) (add_l p (mul_l d (succ_l s)))) p)
            (zero_l ℳ) := by
  simp only [connected_m, slot_s, slot_M, slot_y, slot_row, slot_p, slot_d, slot_k,
    envSlots, Formula.satisfies, SecondOrderOrder.formula_l,
    SecondOrderProgramUniformAncestorRows.row_formula_l,
    addT, mulT, succT, Term.eval, Arguments.eval, Env.pushFree, Assignment.push]
  rfl

/-- 实际相邻副本的边界祖先逐项成立时，第零首列到任意较晚首列的祖先也成立。 -/
theorem first_to_l (hℳ : Theory.Models ℳ theory_m) {M : set_l ℳ}
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {y row p d k s : num_l ℳ}
    (hadjacent : ∀ t, SecondOrderOrder.lt_l t k →
      ¬relation_l M
        (value_l (value_l (value_l y row) (add_l p (mul_l d (succ_l t))))
          (add_l p (mul_l d t))) (zero_l ℳ))
    (hs : SecondOrderOrder.lt_l s k) :
    ¬relation_l M
      (value_l (value_l (value_l y row) (add_l p (mul_l d (succ_l s)))) p)
        (zero_l ℳ) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  have h : ∀ t, SecondOrderOrder.lt_l t k →
      ¬relation_l M
        (value_l (value_l (value_l y row) (add_l p (mul_l d (succ_l t)))) p)
          (zero_l ℳ) := by
    intro t
    refine induct_l hℳ connected_m connected_language_m (envSlots M y row p d k)
      (fun t => SecondOrderOrder.lt_l t k →
        ¬relation_l M
          (value_l (value_l (value_l y row) (add_l p (mul_l d (succ_l t)))) p)
            (zero_l ℳ))
      (connected_syntax_l M y row p d k) ?_ ?_ t
    · intro hzero
      have hbase := hadjacent (zero_l ℳ) hzero
      rw [mul_zero_l hℳ d, add_zero_l hℳ p] at hbase
      exact hbase
    · intro t ih ht
      have htk : SecondOrderOrder.lt_l t k :=
        SecondOrderOrder.trans_l hℳ (lt_own_succ_l hℳ t) ht
      exact SecondOrderProgramUniformAncestorStructure.trans_l hℳ hM
        (hadjacent (succ_l t) ht) (ih htk)
  exact h s hs

#print axioms connected_m
#print axioms connected_language_m
#print axioms connected_syntax_l
#print axioms first_to_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionCopyBoundaryIteration
