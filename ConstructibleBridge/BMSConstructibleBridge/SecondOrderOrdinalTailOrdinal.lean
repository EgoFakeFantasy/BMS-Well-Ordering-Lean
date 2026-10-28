import BMSConstructibleBridge.SecondOrderOrdinalTailMembers
import BMSConstructibleBridge.SecondOrderOrdinalSuccessor
import BMSConstructibleBridge.SecondOrderGraphOrdinalFormula

/-! # ω 尾节点确实是原商中的序数

零节点为基础序数的后继，之后每个内部后继节点满足精确后继方程。
对实际序数公式作原模型归纳，不假设模型在外部良基。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalTailOrdinal

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private abbrev quotient_l (hℳ : Theory.Models ℳ theory_m) :=
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)

private def zero_m {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  .app (σ := signature_m) .zero .nil
private def one_m {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  .app (σ := signature_m) .succ (.cons zero_m .nil)

theorem ordinal_l (hℳ : Theory.Models ℳ theory_m) {S G : set_l ℳ} {r : num_l ℳ}
    (hG : SecondOrderOrdinalTailGraph.spec_l S r G) (hS : ∀ a, SecondOrderDomain.wf_l S a)
    (hα : SetTheory.Structure.IsOrdinal (quotient_l hℳ)
      (SecondOrderQuotient.mk_l hℳ ⟨S, r, hS r⟩)) :
    ∀ n, SetTheory.Structure.IsOrdinal (quotient_l hℳ)
      (SecondOrderQuotient.mk_l hℳ (SecondOrderOrdinalTailGraph.code_l hℳ hG hS n)) := by
  let φ : Formula signature_m [] [.num, .set] := .existsE .num (.conj
    (PrimitiveFormulas.pair_m one_m (.fvar .here) (.bvar .here))
    (SecondOrderGraphOrdinalFormula.formula_m (.fvar (.there .here)) (.bvar .here)))
  have hPure : language_m φ = true := by
    change (true && _) = true
    exact SecondOrderGraphOrdinalFormula.pure_m _ _ rfl rfl
  have hRead (n : num_l ℳ) : φ.satisfies
      (((Env.empty (M := ℳ)).pushFree G).pushFree n) ↔
        SetTheory.Structure.IsOrdinal (quotient_l hℳ)
          (SecondOrderQuotient.mk_l hℳ (SecondOrderOrdinalTailGraph.code_l hℳ hG hS n)) := by
    simp only [φ, Formula.satisfies, SecondOrderPairing.formula_l, one_m, zero_m, Term.eval]
    change (∃ q : num_l ℳ, value_l (succ_l (zero_l ℳ)) n = q ∧
      (SecondOrderGraphOrdinalFormula.formula_m (.fvar (.there .here)) (.bvar .here)).satisfies
        ((((Env.empty (M := ℳ)).pushFree G).pushFree n).pushBound q)) ↔ _
    let η (q : num_l ℳ) : Env ℳ [.num] [.num, .set] :=
      (((Env.empty (M := ℳ)).pushFree G).pushFree n).pushBound q
    have hRow (q : num_l ℳ) := SecondOrderGraphOrdinalFormula.formula_l hℳ
      (η q) (.fvar (.there .here)) (.bvar .here)
      (show SecondOrderDomain.wf_l G q from SecondOrderOrdinalTailGraph.wf_l hℳ hG hS q)
    constructor
    · rintro ⟨q, rfl, h⟩
      exact (hRow _).mp h
    · intro h
      exact ⟨value_l (succ_l (zero_l ℳ)) n, rfl, (hRow _).mpr h⟩
  apply induct_l hℳ φ hPure ((Env.empty (M := ℳ)).pushFree G) _ hRead
  · apply SecondOrderOrdinalSuccessor.ordinal_l hℳ ⟨S, r, hS r⟩ _ hα
    intro X
    rw [SecondOrderOrdinalTailMembers.members_l hℳ hG hS]
    constructor
    · rintro (hX | hX | ⟨m, hm, _⟩)
      · exact Or.inl hX
      · exact Or.inr hX
      · letI := SecondOrderAlgebra.semiring_l hℳ
        letI := SecondOrderAlgebra.order_l hℳ
        exact (not_lt_of_ge (SecondOrderAlgebra.zero_le_l hℳ m) hm).elim
    · exact fun h => h.elim Or.inl (fun h => Or.inr (Or.inl h))
  · intro n hn
    exact SecondOrderOrdinalSuccessor.ordinal_l hℳ _ _ hn
      (SecondOrderOrdinalTailMembers.successor_l hℳ hG hS n)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalTailOrdinal
