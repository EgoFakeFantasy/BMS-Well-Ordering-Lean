import BMSConstructibleBridge.PowerlessFiniteSupport
import BMSConstructibleBridge.PowerlessEvaluationOperator
import YesMetaZFC.Automation.ModelClosure

/-!
# 原求值子集算子存在闭句的有限核心支持

正文保留完整 operator_m，不把其见证或函数性加入背景。
有限支持经原推导取得；实际跨层解释由有限闭包另证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessOperatorFiniteSupport

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

def formula_m : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set] :=
  .imp (SecondOrderOmegaSyntax.omega_m (.fvar .here)) (.existsE .set
    (PowerlessEvaluationOperator.operator_m (.fvar .here) (.fvar (.there .here))
      (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here))))))) (.bvar .here)))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close formula_m

theorem sentence_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) : sentence_m.TrueIn ℳ := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff formula_m).mpr
  intro η
  simp only [formula_m, Formula.satisfies, omega_formula_l, PowerlessEvaluationOperator.operator_formula_l hℳ]
  intro hω
  obtain ⟨D, hD⟩ := PowerlessEvaluationOperator.exists_l hℳ hω
    (η.freeVal (.there .here)) (η.freeVal (.there (.there .here)))
    (η.freeVal (.there (.there (.there .here))))
    (η.freeVal (.there (.there (.there (.there .here)))))
    (η.freeVal (.there (.there (.there (.there (.there .here))))))
    (η.freeVal (.there (.there (.there (.there (.there (.there .here)))))))
  exact ⟨D, hD⟩

theorem finite_m : Nonempty (Derives.FiniteTheorySupport PowerlessTheory.theory_m [] sentence_m) :=
  PowerlessFiniteSupport.finite_m (fun _ hℳ => sentence_l hℳ)

noncomputable def support_m : Derives.FiniteTheorySupport PowerlessTheory.theory_m [] sentence_m :=
  Classical.choice finite_m

def theory_m : Theory ℒ := Theory.ofList support_m.sentences

theorem core_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) : Theory.Models ℳ theory_m :=
  fun φ hφ => hℳ φ (support_m.subset φ hφ)

theorem satisfies_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} (hℳ : Theory.Models ℳ theory_m)
    (η : Env ℳ [] [.set, .set, .set, .set, .set, .set, .set]) : formula_m.satisfies η :=
  (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff formula_m).mp
    (support_m.derivation.semantically_entails ℳ hℳ) η

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessOperatorFiniteSupport
