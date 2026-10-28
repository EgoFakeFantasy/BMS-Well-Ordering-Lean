import BMSConstructibleBridge.PowerlessMemberDefEnumerationSemantics

/-! # 相对 Def 的纯语言存在关系

把八个显式集合见证的存在块与原全域 Def 对应。证书只在 Prop 中消去，
没有从模型内定义关系提取 Type 层选择函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberDefSemantics

open Logic FirstOrder PowerlessBMSQuotientCoding
open Automation.RelationalTranslation (weakenTerm existsBlock pushBlock weakenTerm_eval existsBlock_satisfies)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem nonempty_formula_l (C : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (w z X Y : Term ℒ Γ Δ .set)
    (hw : w.eval η = C.omega) (hz : z.eval η = (numberCode_l C (SecondOrderModel.zero_l ℳ)).val) :
    (PowerlessMemberDefSyntax.nonempty_m w z X Y).satisfies η ↔
      SecondOrderMemberDef.nonempty_l hℳ (X.eval η) (Y.eval η) := by
  let Ξ : SortContext ℒ := [.set, .set, .set, .set, .set, .set, .set, .set]
  rw [PowerlessMemberDefSyntax.nonempty_m, existsBlock_satisfies]
  constructor
  · rintro ⟨b, hb⟩
    have h := PowerlessMemberDefEnumerationSemantics.represents_l C (pushBlock η b)
      (weakenTerm Ξ w) (weakenTerm Ξ z) (weakenTerm Ξ X) (weakenTerm Ξ Y)
      (.bvar .here) (.bvar (.there .here)) (.bvar (.there (.there .here)))
      (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there (.there (.there .here)))))
      (.bvar (.there (.there (.there (.there (.there .here))))))
      (.bvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.bvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
      ((weakenTerm_eval η b w).trans hw) ((weakenTerm_eval η b z).trans hz) hb
    rw [weakenTerm_eval η b X, weakenTerm_eval η b Y] at h
    exact h
  · intro h
    have hOriginal := h
    obtain ⟨A, a, ha, _, _, _, _, _, _, _, _, hAX, _, _⟩ := h
    obtain ⟨Z, f, v, e, d, q, r, t, g, P, hZ⟩ := SecondOrderEnumeratedMemberDef.exists_l C A a ha
    have hOriginal' : SecondOrderMemberDef.nonempty_l hℳ (SecondOrderQuotient.mk_l hℳ A) (Y.eval η) := by
      rw [hAX]
      exact hOriginal
    have hZY := SecondOrderMemberDef.unique_l hℳ (Or.inr hZ) (Or.inr hOriginal')
    have hP : SecondOrderEnumeratedMemberDef.presentation_l C (X.eval η) (Y.eval η) f v e d q r t g :=
      by simpa only [hAX, hZY] using P
    obtain ⟨aV, hv⟩ := representative_exists_l C v
    obtain ⟨aE, he⟩ := representative_exists_l C e
    obtain ⟨aD, hd⟩ := representative_exists_l C d
    obtain ⟨aQ, hq⟩ := representative_exists_l C q
    obtain ⟨aR, hr⟩ := representative_exists_l C r
    obtain ⟨aT, ht⟩ := representative_exists_l C t
    obtain ⟨aF, hg⟩ := representative_exists_l C g
    let b : Values (SecondOrderQuotient.structure_l hℳ).Carrier Ξ :=
      .cons f (.cons aV.val (.cons aE.val (.cons aD.val (.cons aQ.val (.cons aR.val
        (.cons aT.val (.cons aF.val .nil)))))))
    refine ⟨b, ?_⟩
    apply (PowerlessMemberDefEnumerationSemantics.formula_l C (pushBlock η b)
      (weakenTerm Ξ w) (weakenTerm Ξ z) (weakenTerm Ξ X) (weakenTerm Ξ Y)
      (.bvar .here) (.bvar (.there .here)) (.bvar (.there (.there .here)))
      (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there (.there (.there .here)))))
      (.bvar (.there (.there (.there (.there (.there .here))))))
      (.bvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.bvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
      aV aE aD aQ aR aT aF v e d q r t g
      ((weakenTerm_eval η b w).trans hw) ((weakenTerm_eval η b z).trans hz)
      rfl rfl rfl rfl rfl rfl rfl hv he hd hq hr ht hg).mpr
    change SecondOrderEnumeratedMemberDef.presentation_l C
      ((weakenTerm Ξ X).eval (pushBlock η b)) ((weakenTerm Ξ Y).eval (pushBlock η b)) f v e d q r t g
    rw [weakenTerm_eval η b X, weakenTerm_eval η b Y]
    exact hP

theorem formula_l (C : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (w z X Y : Term ℒ Γ Δ .set)
    (hw : w.eval η = C.omega) (hz : z.eval η = (numberCode_l C (SecondOrderModel.zero_l ℳ)).val) :
    (PowerlessMemberDefSyntax.formula_m w z X Y).satisfies η ↔
      SecondOrderMemberDef.spec_l hℳ (X.eval η) (Y.eval η) := by
  rw [PowerlessMemberDefSyntax.formula_m, Formula.satisfies,
    nonempty_formula_l C η w z X Y hw hz]
  apply or_congr _ Iff.rfl
  apply and_congr _ (SecondOrderObjectSyntax.pair_l hℳ η X X Y)
  simp only [Formula.satisfies, SecondOrderObjectSyntax.member_m, Arguments.eval,
    Term.eval, Term.eval_weakenBound]
  rfl

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberDefSemantics
