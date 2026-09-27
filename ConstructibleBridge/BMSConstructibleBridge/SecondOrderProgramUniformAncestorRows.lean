import BMSConstructibleBridge.SecondOrderProgramUniformAncestorStructure
import BMSConstructibleBridge.SecondOrderMinimum

/-!
# 原祖先关系包含于所有较低的内部行

行号为同一模型的自然数，不限于固定外部数码。由实际祖先公式构造不低于
指定行的可达行集合，内部最小元与相邻行包含迫使其最小行恰为指定行。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformAncestorRows

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderProgramSemantics
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramAncestorRecursion (ancestor_m ancestor_formula_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 原统一成员程序的行参数也是实际内部数项。 -/
def row_m {Γ Δ : SortContext signature_m} (M : Term signature_m Γ Δ .set)
    (x r b i : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .existsE .num (.conj
    (PrimitiveFormulas.pair_m (x.weakenBound sort_m.num) (r.weakenBound sort_m.num) (.bvar .here))
    (ancestor_m (M.weakenBound sort_m.num) (.bvar .here)
      (b.weakenBound sort_m.num) (i.weakenBound sort_m.num)))

theorem row_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (M : Term signature_m Γ Δ .set) (x r b i : Term signature_m Γ Δ .num) :
    (row_m M x r b i).satisfies η ↔ ¬relation_l (M.eval η)
      (value_l (value_l (value_l (x.eval η) (r.eval η)) (b.eval η)) (i.eval η)) (zero_l ℳ) := by
  simp only [row_m, Formula.satisfies, SecondOrderPairing.formula_l,
    ancestor_formula_l, Term.eval_weakenBound]
  change (∃ q, value_l (x.eval η) (r.eval η) = q ∧
    ¬relation_l (M.eval η) (value_l (value_l q (b.eval η)) (i.eval η)) (zero_l ℳ)) ↔ _
  simp only [exists_eq_left']

/-- 任意内部低行包含：不以宿主Nat枚举从s到r的行号。 -/
theorem row_le_l (hℳ : Theory.Models ℳ theory_m) {M : set_l ℳ}
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M) {x r s b i : num_l ℳ}
    (hsr : s = r ∨ SecondOrderOrder.lt_l s r)
    (hi : ¬relation_l M (value_l (value_l (value_l x r) b) i) (zero_l ℳ)) :
    ¬relation_l M (value_l (value_l (value_l x s) b) i) (zero_l ℳ) := by
  letI := SecondOrderAlgebra.semiring_l hℳ
  letI := SecondOrderAlgebra.order_l hℳ
  let φ : Formula signature_m [] [.num, .num, .num, .num, .num, .set] :=
    .conj (PrimitiveFormulas.lt_m (.fvar (.there .here))
      (Term.app (σ := signature_m) .succ (.cons (.fvar .here) .nil)))
      (row_m (.fvar (.there (.there (.there (.there (.there .here))))))
        (.fvar (.there (.there .here))) (.fvar .here)
        (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here))))))
  obtain ⟨S, hS⟩ := comprehension_l hℳ φ (pure_language_m _ rfl)
    ((((((Env.empty (M := ℳ)).pushFree M).pushFree i).pushFree b).pushFree x).pushFree s)
  have h (q : num_l ℳ) : mem_l q S ↔ s ≤ q ∧
      ¬relation_l M (value_l (value_l (value_l x q) b) i) (zero_l ℳ) := by
    refine (hS q).trans ?_
    simp only [φ, Formula.satisfies, SecondOrderOrder.formula_l, row_formula_l, Term.eval,
      Arguments.eval, FirstOrder.Env.pushFree, FirstOrder.Assignment.push]
    change (s < succ_l q ∧ _) ↔ _
    rw [SecondOrderNaturalGraph.lt_succ_l hℳ]
  obtain ⟨q, hq, hmin⟩ := SecondOrderMinimum.exists_l hℳ S ⟨r, (h r).mpr ⟨hsr, hi⟩⟩
  obtain ⟨hsq, hqi⟩ := (h q).mp hq
  rcases eq_or_lt_of_le hsq with he | hs
  · exact he ▸ hqi
  · rcases predecessor_l hℳ q with rfl | ⟨p, rfl⟩
    · exact False.elim ((not_lt_of_ge (SecondOrderAlgebra.zero_le_l hℳ s)) hs)
    · exact False.elim (hmin p (lt_own_succ_l hℳ p)
        ((h p).mpr ⟨(SecondOrderNaturalGraph.lt_succ_l hℳ s p).mp hs,
          SecondOrderProgramUniformAncestorStructure.row_succ_l hℳ hM hqi⟩))

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformAncestorRows
