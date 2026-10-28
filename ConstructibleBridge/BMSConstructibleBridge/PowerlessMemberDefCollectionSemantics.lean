import BMSConstructibleBridge.PowerlessMemberDefFormulaSemantics

/-! # Def 的精确值域公式

输出成员由合法公式索引和整条切片刻画。该刻画不允许输出集合夹带多余
成员，也不把候选子集限制为固定图的外部标准代表。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberDefCollectionSemantics

open Logic FirstOrder PowerlessBMSQuotientCoding

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

theorem formula_l (C : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (w z Y f V E F : Term ℒ Γ Δ .set)
    (A B G : PowerlessArithmetic.set_l (ℳ := SecondOrderQuotient.structure_l hℳ) C.omega)
    (v e g : SecondOrderModel.set_l ℳ)
    (hw : w.eval η = C.omega) (hz : z.eval η = (numberCode_l C (SecondOrderModel.zero_l ℳ)).val)
    (hV : V.eval η = A.val) (hE : E.eval η = B.val) (hF : F.eval η = G.val)
    (hA : setRel_l C A v) (hB : setRel_l C B e) (hG : setRel_l C G g) :
    (PowerlessMemberDefSyntax.collection_m w z Y f V E F).satisfies η ↔
      ∀ Z, SecondOrderQuotient.mem_l hℳ Z (Y.eval η) ↔
        ∃ i, SecondOrderLegalFormulaIndex.spec_l v e i ∧
          ∀ x, SecondOrderQuotient.mem_l hℳ x Z ↔
            ∃ n, SecondOrderPairing.relation_l g i n ∧
              SecondOrderFunctionObjects.value_l hℳ (f.eval η) (numberCode_l C n).val x := by
  have hLegal Z i := PowerlessMemberDefArithmeticSemantics.legal_read_l C
    ((η.pushBound Z).pushBound (numberCode_l C i).val)
    (up (up w)) (up (up z)) (up (up V)) (up (up E)) (.bvar .here) A B v e i
    (by simpa only [up, Term.eval_weakenBound] using hw)
    (by simpa only [up, Term.eval_weakenBound] using hz)
    (by simpa only [up, Term.eval_weakenBound] using hV)
    (by simpa only [up, Term.eval_weakenBound] using hE) rfl hA hB
  have hSlice Z i x := PowerlessMemberDefSliceSemantics.formula_l C
    (((η.pushBound Z).pushBound (numberCode_l C i).val).pushBound x)
    (up (up (up w))) (up (up (up z))) (up (up (up f))) (up (up (up F)))
    (.bvar (.there .here)) (.bvar .here) G g i
    (by simpa only [up, Term.eval_weakenBound] using hw)
    (by simpa only [up, Term.eval_weakenBound] using hz)
    (by simpa only [up, Term.eval_weakenBound] using hF) rfl hG
  simp only [PowerlessMemberDefSyntax.collection_m, Formula.satisfies,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound, Term.eval]
  rw [hw]
  apply forall_congr'
  intro Z
  apply iff_congr Iff.rfl
  refine (PowerlessBMSQuotientNumberQuantifiers.exists_l C _).trans ?_
  apply exists_congr
  intro i
  apply and_congr (hLegal Z i)
  apply forall_congr'
  intro x
  apply iff_congr Iff.rfl
  simpa only [up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here] using hSlice Z i x

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberDefCollectionSemantics
