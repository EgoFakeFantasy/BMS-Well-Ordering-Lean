import BMSConstructibleBridge.SecondOrderCanonicalMemberDefFormula

/-! # 原图 Def 操作公式的完整语义

异质存在块与实际模型证书双向对应；见证只在 Prop 中绑定。全域原图
关系不预先要求输入图良基，输入域和商 Def 的连接由独立模块证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalMemberDefFormulaSemantics

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderCanonicalMemberDefFormula
open Automation.RelationalTranslation (weakenTerm existsBlock_satisfies pushBlock weakenTerm_eval)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem default_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (A : Term signature_m Γ Δ .set) (r a : Term signature_m Γ Δ .num) :
    (SecondOrderFormulaArguments.formula_m SecondOrderMemberDefault.formula_m
      (.cons a (.cons r (.cons A .nil)))).satisfies η ↔
      SecondOrderMemberDefault.spec_l (A.eval η) (r.eval η) (a.eval η) := by
  simp only [SecondOrderFormulaArguments.formula_l, SecondOrderMemberDefault.formula_m,
    Formula.satisfies, SecondOrderPairing.edge_l, SecondOrderOrder.formula_l]
  rfl

theorem instance_formula_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext signature_m}
    (η : Env ℳ Γ Δ) (A : Term signature_m Γ Δ .set) (r a : Term signature_m Γ Δ .num)
    (V E D Q R T F G P W : Term signature_m Γ Δ .set) : (instance_m A r a V E D Q R T F G P W).satisfies η ↔
      SecondOrderCanonicalMemberDefGraph.spec_l (A.eval η) (r.eval η) (a.eval η)
        (V.eval η) (E.eval η) (D.eval η) (Q.eval η) (R.eval η) (T.eval η) (F.eval η)
        (G.eval η) (P.eval η) (W.eval η) := by
  simp only [instance_m, SecondOrderFormulaArguments.formula_l, certificate_m, Formula.satisfies,
    SecondOrderMemberDefPacketFormula.formula_m, SecondOrderMemberDefPacketFormula.packet_formula_l,
    SecondOrderMemberDefGraphFormula.layer_formula_l, SecondOrderMemberDefGraphFormula.selection_formula_l,
    SecondOrderMemberDefGraphFormula.graft_formula_l hℳ]
  constructor
  · rintro ⟨hPacket, hLayer, hSelection, hGraft⟩
    exact ⟨hPacket, hLayer, hSelection, hGraft⟩
  · intro h
    exact ⟨h.packet, h.layer, h.selection, h.graft⟩

theorem formula_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext signature_m}
    (η : Env ℳ Γ Δ) (A : Term signature_m Γ Δ .set) (r : Term signature_m Γ Δ .num)
    (W : Term signature_m Γ Δ .set) : (formula_m A r W).satisfies η ↔
      SecondOrderCanonicalMemberDefGraph.canonical_l (A.eval η) (r.eval η) (W.eval η) := by
  rw [formula_m, existsBlock_satisfies]
  constructor
  · rintro ⟨b, ha, h⟩
    have hDefault := (default_formula_l (pushBlock η b) (weakenTerm witnesses_m A)
      (weakenTerm witnesses_m r) (.bvar .here)).mp ha
    have hSpec := (instance_formula_l hℳ (pushBlock η b)
      (weakenTerm witnesses_m A) (weakenTerm witnesses_m r) (.bvar .here)
      (.bvar (.there .here)) (.bvar (.there (.there .here))) (.bvar (.there (.there (.there .here))))
      (.bvar (.there (.there (.there (.there .here))))) (.bvar (.there (.there (.there (.there (.there .here))))))
      (.bvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.bvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
      (.bvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
      (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
      (weakenTerm witnesses_m W)).mp h
    rw [weakenTerm_eval η b A, weakenTerm_eval η b r] at hDefault
    rw [weakenTerm_eval η b A, weakenTerm_eval η b r, weakenTerm_eval η b W] at hSpec
    exact ⟨_, hDefault, _, _, _, _, _, _, _, _, _, hSpec⟩
  · rintro ⟨a, ha, V, E, D, Q, R, T, F, G, P, h⟩
    let b : Values ℳ.Carrier witnesses_m := .cons a (.cons V (.cons E (.cons D (.cons Q
      (.cons R (.cons T (.cons F (.cons G (.cons P .nil)))))))))
    refine ⟨b, ?_, ?_⟩
    · apply (default_formula_l (pushBlock η b) (weakenTerm witnesses_m A)
        (weakenTerm witnesses_m r) (.bvar .here)).mpr
      rw [weakenTerm_eval η b A, weakenTerm_eval η b r]
      exact ha
    · apply (instance_formula_l hℳ (pushBlock η b)
        (weakenTerm witnesses_m A) (weakenTerm witnesses_m r) (.bvar .here)
        (.bvar (.there .here)) (.bvar (.there (.there .here))) (.bvar (.there (.there (.there .here))))
        (.bvar (.there (.there (.there (.there .here))))) (.bvar (.there (.there (.there (.there (.there .here))))))
        (.bvar (.there (.there (.there (.there (.there (.there .here)))))))
        (.bvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
        (.bvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
        (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
        (weakenTerm witnesses_m W)).mpr
      rw [weakenTerm_eval η b A, weakenTerm_eval η b r, weakenTerm_eval η b W]
      exact h

#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalMemberDefFormulaSemantics
