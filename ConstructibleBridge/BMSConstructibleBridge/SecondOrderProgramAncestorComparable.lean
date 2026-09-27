import BMSConstructibleBridge.SecondOrderProgramAncestorRecursion

/-!
# 同一原祖先链中成员的可比性

固定成员j，实际理解公式收集j、j的祖先和以j为祖先的列。原父递归式使这个
内部集合对父查询封闭；从共同目标出发的真实成员因而属于该集合。不借助宿主
传递闭包、外部有限链或内部自然数的外部良基性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorComparable

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderProgramSemantics
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramAncestorClosure (member_closed_l)
open SecondOrderProgramAncestorClosedSet (member_mem_l)
open SecondOrderProgramAncestorRecursion (ancestor_m ancestor_formula_l member_some_l)
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 自由槽[t,x,j,M]：t=j，或t是j的祖先，或j是t的祖先。 -/
private def comparable_m : Formula signature_m [] [.num, .num, .num, .set] :=
  let t : Term signature_m [] _ .num := .fvar .here
  let x : Term signature_m [] _ .num := .fvar (.there .here)
  let j : Term signature_m [] _ .num := .fvar (.there (.there .here))
  let M : Term signature_m [] _ .set := .fvar (.there (.there (.there .here)))
  .disj (.equal t j) (.disj (ancestor_m M x j t) (ancestor_m M x t j))

private theorem comparable_formula_l (M : set_l ℳ) (x j t : num_l ℳ) :
    comparable_m.satisfies (((((Env.empty (M := ℳ)).pushFree M).pushFree j).pushFree x).pushFree t) ↔
      t = j ∨ ¬relation_l M (value_l (value_l x j) t) (zero_l ℳ) ∨
        ¬relation_l M (value_l (value_l x t) j) (zero_l ℳ) := by
  simp only [comparable_m, Formula.satisfies, ancestor_formula_l]
  rfl

/-- 共同目标的两个实际祖先相同，或其中一个是另一个的实际祖先。 -/
theorem comparable_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {M C : set_l ℳ}
    (hM : graph_semantics_l (graph_m (member_m c)) M)
    (hC : graph_semantics_l (graph_m c) C) {x b i j : num_l ℳ}
    (hparent : ∀ t p, relation_l C (value_l x t) (succ_l p) → SecondOrderOrder.lt_l p t)
    (hi : ¬relation_l M (value_l (value_l x b) i) (zero_l ℳ))
    (hj : ¬relation_l M (value_l (value_l x b) j) (zero_l ℳ)) :
    i = j ∨ ¬relation_l M (value_l (value_l x j) i) (zero_l ℳ) ∨
      ¬relation_l M (value_l (value_l x i) j) (zero_l ℳ) := by
  obtain ⟨S, hS⟩ := comprehension_l hℳ comparable_m (pure_language_m _ rfl)
    ((((Env.empty (M := ℳ)).pushFree M).pushFree j).pushFree x)
  have hs (t : num_l ℳ) : mem_l t S ↔ t = j ∨
      ¬relation_l M (value_l (value_l x j) t) (zero_l ℳ) ∨
      ¬relation_l M (value_l (value_l x t) j) (zero_l ℳ) :=
    (hS t).trans (comparable_formula_l M x j t)
  have hclosed (t p : num_l ℳ) (ht : t = b ∨ mem_l t S)
      (hp : relation_l C (value_l x t) (succ_l p)) : mem_l p S := by
    have ht : t = j ∨ ¬relation_l M (value_l (value_l x j) t) (zero_l ℳ) ∨
        ¬relation_l M (value_l (value_l x t) j) (zero_l ℳ) := by
      rcases ht with rfl | ht
      · exact Or.inr (Or.inr hj)
      · exact (hs t).mp ht
    apply (hs p).mpr
    rcases ht with rfl | ht | ht
    · exact Or.inr (Or.inl (member_closed_l hℳ c hM hC hparent (Or.inl rfl) hp))
    · exact Or.inr (Or.inl (member_closed_l hℳ c hM hC hparent (Or.inr ht) hp))
    · rcases (member_some_l hℳ c hM hC hparent hp).mp ht with he | ht
      · exact Or.inl he.symm
      · exact Or.inr (Or.inr ht)
  exact (hs i).mp (member_mem_l hℳ c hM hC hclosed hi)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorComparable
