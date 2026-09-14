import BMSConstructibleBridge.PowerlessFiniteSupport
import BMSConstructibleBridge.PowerlessEvaluationPresentation

/-!
# 原求值图存在闭句的有限核心支持

使用原 evaluation_m 的八个输入参数和完整量词正文。
有限理论只保证原源公式的存在见证；跨成员结构解释另由绝对性定理提供。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationFiniteSupport

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

def formula_m : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] :=
  .imp (SecondOrderOmegaSyntax.omega_m (.fvar .here)) (.existsE .set
    (PowerlessEvaluationPresentation.evaluation_m (.fvar .here) (.fvar (.there .here))
      (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.bvar .here)))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close formula_m

theorem sentence_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) : sentence_m.TrueIn ℳ := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff formula_m).mpr
  intro η
  simp only [formula_m, Formula.satisfies, omega_formula_l,
    PowerlessEvaluationPresentation.evaluation_formula_l hℳ]
  intro hω
  obtain ⟨F, hF, _⟩ := PowerlessEvaluationRecursion.exists_unique_l hℳ hω
    (η.freeVal (.there .here)) (η.freeVal (.there (.there .here)))
    (η.freeVal (.there (.there (.there .here))))
    (η.freeVal (.there (.there (.there (.there .here)))))
    (η.freeVal (.there (.there (.there (.there (.there .here))))))
    (η.freeVal (.there (.there (.there (.there (.there (.there .here)))))))
    (η.freeVal (.there (.there (.there (.there (.there (.there (.there .here))))))))
  exact ⟨F, hF⟩

theorem finite_m : Nonempty (Derives.FiniteTheorySupport PowerlessTheory.theory_m [] sentence_m) :=
  PowerlessFiniteSupport.finite_m (fun _ hℳ => sentence_l hℳ)

noncomputable def support_m : Derives.FiniteTheorySupport PowerlessTheory.theory_m [] sentence_m :=
  Classical.choice finite_m

def theory_m : Theory ℒ := Theory.ofList support_m.sentences

theorem core_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) : Theory.Models ℳ theory_m :=
  fun φ hφ => hℳ φ (support_m.subset φ hφ)

theorem satisfies_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} (hℳ : Theory.Models ℳ theory_m)
    (η : Env ℳ [] [.set, .set, .set, .set, .set, .set, .set, .set]) : formula_m.satisfies η :=
  (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff formula_m).mp
    (support_m.derivation.semantically_entails ℳ hℳ) η

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationFiniteSupport
