import BMSConstructibleBridge.SecondOrderMemberStructure
import BMSConstructibleBridge.SecondOrderDefinableRespect

/-!
# 实际成员结构的全内部相容子集族

全数域原子相容条件由实际商成员表示消去。同一个内部族既覆盖全部上游
公式和参数，又对每个内部索引保持成员代表不变。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberFamily

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    (a : num_l ℳ) (ha : relation_l A.real a A.root) : ∃ F : set_l ℳ,
      (∀ i n m, SecondOrderGraph.eq_l (SecondOrderMemberNormalizer.code_l hℳ A a ha n)
        (SecondOrderMemberNormalizer.code_l hℳ A a ha m) → (relation_l F i n ↔ relation_l F i m)) ∧
      ∀ (Γ Δ : SortContext ℒ) (η : Env (SecondOrderMemberStructure.structure_l hℳ A a ha) Γ Δ)
        (φ : Formula ℒ (.set :: Γ) Δ), ∃ i, ∀ n, relation_l F i n ↔
          Formula.satisfies (η.pushBound (SecondOrderMemberStructure.value_l hℳ A a ha n)) φ := by
  let f := SecondOrderMemberStructure.value_l hℳ A a ha
  obtain ⟨D, Q, R, hD, hQ, hR⟩ := SecondOrderMemberStructure.graphs_l hℳ A a ha
  have h₀ (n : num_l ℳ) : relation_l Q n n := (hQ n n).mpr rfl
  have h₁ : SecondOrderRelatedAssignments.respects_l Q Q := by
    intro n m n' m' hn hm
    have hn₀ := (hQ n n').mp hn
    have hm₀ := (hQ m m').mp hm
    exact (hQ n m).trans ((Iff.intro
      (fun h => hn₀.symm.trans (h.trans hm₀))
      (fun h => hn₀.trans (h.trans hm₀.symm))).trans (hQ n' m').symm)
  have h₂ : SecondOrderRelatedAssignments.respects_l Q R := by
    intro n m n' m' hn hm
    exact (hR n m).trans ((iff_of_eq (congrArg₂
      (SecondOrderSourceSatisfaction.member_l (SecondOrderMemberStructure.structure_l hℳ A a ha))
      ((hQ n n').mp hn) ((hQ m m').mp hm))).trans (hR n' m').symm)
  have hS (y : (SecondOrderMemberStructure.structure_l hℳ A a ha).Carrier .set) :
      ∃ n, mem_l n D ∧ f n = y := by
    obtain ⟨n, hn⟩ := SecondOrderMemberStructure.surjective_l hℳ A a ha y
    exact ⟨n, hD n, hn⟩
  obtain ⟨E, hE⟩ := SecondOrderBinaryPowers.exists_l hℳ
  obtain ⟨T, hT, _⟩ := SecondOrderEvaluationFixedPoint.exists_l hℳ E D Q R
  obtain ⟨F, hF, _⟩ := SecondOrderDefinableFamily.exists_l hℳ E D T
  refine ⟨F, ?_, ?_⟩
  · intro i n m h
    have h₃ : relation_l Q n m := (hQ n m).mpr (Subtype.ext ((SecondOrderQuotient.eq_iff_l hℳ _ _).mpr h))
    exact SecondOrderDefinableRespect.row_l hℳ hE D Q R T F h₀ h₁ h₂ hT hF i n m (hD n) (hD m) h₃
  · intro Γ Δ η φ
    obtain ⟨l, c, hc, hη⟩ := SecondOrderSourceAssignment.exists_l hℳ hE D f hS η
    refine ⟨SecondOrderDefinableFamily.index_l (SecondOrderFormulaCompilation.formula_l ℳ φ) l c, ?_⟩
    intro n
    exact (SecondOrderDefinableCoverage.formula_l hℳ hE D Q R T F hT hF f hS
      (fun x y _ _ => hQ x y) (fun x y _ _ => hR x y) φ η l c hc hη n).trans (and_iff_right (hD n))

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberFamily
