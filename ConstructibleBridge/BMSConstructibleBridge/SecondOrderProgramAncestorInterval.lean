import BMSConstructibleBridge.SecondOrderProgramAncestorRecursion
import BMSConstructibleBridge.SecondOrderMinimum

/-!
# 原祖先段中持续存在的父查询见证

在候选i右侧的实际祖先段中取内部最小列。若每列的真实父输出都不越过i，
这个最小列的父节点只能是i。最小元所用集合由原成员图的实际公式理解产生，
不把任意宿主性质作为内部集合；持续性仍是本定理的显式前提。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorInterval

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderProgramSemantics
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramAncestorClosure (member_closed_l)
open SecondOrderProgramListShift (output_m output_syntax_l)
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 自由槽[t,b,i,u,M]，其中u是原参数与目标列的实际配对值。 -/
private def interval_m : Formula signature_m [] [.num, .num, .num, .num, .set] :=
  .conj (PrimitiveFormulas.lt_m (.fvar (.there (.there .here))) (.fvar .here))
    (.disj (.equal (.fvar .here) (.fvar (.there .here)))
      (.neg (output_m (.fvar (.there (.there (.there (.there .here)))))
        (.fvar (.there (.there (.there .here)))) (.fvar .here)
        (Term.app (σ := signature_m) .zero .nil))))

private theorem interval_formula_l (M : set_l ℳ) (u b i t : num_l ℳ) :
    interval_m.satisfies
      ((((((Env.empty (M := ℳ)).pushFree M).pushFree u).pushFree i).pushFree b).pushFree t) ↔
      SecondOrderOrder.lt_l i t ∧
        (t = b ∨ ¬relation_l M (value_l u t) (zero_l ℳ)) := by
  simp only [interval_m, Formula.satisfies, SecondOrderOrder.formula_l, output_syntax_l]
  rfl

/-- 真实祖先段上每个更右列均有不越过候选的父输出时，候选确为实际祖先。 -/
theorem member_of_persistent_l (hℳ : Theory.Models ℳ theory_m) (c : code_m)
    {M C : set_l ℳ}
    (hM : graph_semantics_l (graph_m (member_m c)) M)
    (hC : graph_semantics_l (graph_m c) C) {x b i : num_l ℳ}
    (hparent : ∀ t p, relation_l C (value_l x t) (succ_l p) → SecondOrderOrder.lt_l p t)
    (hlt : SecondOrderOrder.lt_l i b)
    (hpersist : ∀ t, SecondOrderOrder.lt_l i t →
      (t = b ∨ ¬relation_l M (value_l (value_l x b) t) (zero_l ℳ)) →
      ∃ p, relation_l C (value_l x t) (succ_l p) ∧ (i = p ∨ SecondOrderOrder.lt_l i p)) :
    ¬relation_l M (value_l (value_l x b) i) (zero_l ℳ) := by
  obtain ⟨S, hS⟩ := comprehension_l hℳ interval_m (pure_language_m _ rfl)
    (((((Env.empty (M := ℳ)).pushFree M).pushFree (value_l x b)).pushFree i).pushFree b)
  have hs (t : num_l ℳ) : mem_l t S ↔ SecondOrderOrder.lt_l i t ∧
      (t = b ∨ ¬relation_l M (value_l (value_l x b) t) (zero_l ℳ)) :=
    (hS t).trans (interval_formula_l M (value_l x b) b i t)
  obtain ⟨t, ht, hmin⟩ := SecondOrderMinimum.exists_l hℳ S
    ⟨b, (hs b).mpr ⟨hlt, Or.inl rfl⟩⟩
  obtain ⟨hit, ht⟩ := (hs t).mp ht
  obtain ⟨p, hp, hip⟩ := hpersist t hit ht
  have ha := member_closed_l hℳ c hM hC hparent ht hp
  rcases hip with rfl | hip
  · exact ha
  · exact False.elim (hmin p (hparent t p hp) ((hs p).mpr ⟨hip, Or.inr ha⟩))

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorInterval
