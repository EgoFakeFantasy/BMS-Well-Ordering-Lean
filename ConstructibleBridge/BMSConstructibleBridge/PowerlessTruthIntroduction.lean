import BMSConstructibleBridge.PowerlessTruthClosure
import BMSConstructibleBridge.PowerlessTruthOracle
import BMSConstructibleBridge.PowerlessFiniteSupport
import YesMetaZFC.Automation.ModelClosure

/-!
# 有界真值进入原证书的有限核心支持

原有界识别及有符号真值给出实际接受证书。把这一原公式蕴含闭合，
从真正的 Hilbert 推导提取有限支持，使小层无需满足完整核心。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthIntroduction

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

def introduction_m {Γ Δ : SortContext ℒ}
    (ω e T t₁ t₂ t₃ p c f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .imp (.conj (SecondOrderObjectSyntax.member_m c ω)
    (.conj (PowerlessBoundedCertificate.recognizes_m ω e T t₁ t₂ t₃ c)
      (PowerlessTruthBase.rule_m ω e T t₁ t₂ t₃ p c f)))
    (PowerlessTruthCertificate.accepts_m ω e T t₁ t₂ t₃ p c f)

theorem introduction_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ)
    (ω e T t₁ t₂ t₃ p c f : Term ℒ Γ Δ .set) :
    (introduction_m ω e T t₁ t₂ t₃ p c f).satisfies η := by
  simp only [introduction_m, Formula.satisfies, SecondOrderObjectSyntax.member_m,
    Arguments.eval, PowerlessBoundedCertificate.recognizes_formula_l,
    PowerlessTruthBase.rule_m, PowerlessAmbientAssignments.finite_formula_l,
    PowerlessBoundedTruth.truth_formula_l hℳ, PowerlessTruthClosure.accepts_formula_l hℳ]
  exact fun ⟨hc, hB, hf, h⟩ => PowerlessTruthClosure.base_l hℳ hc hB hf h

abbrev context_m : SortContext ℒ := PowerlessTruthOracle.context_m

def formula_m : Formula ℒ [] context_m :=
  introduction_m (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here))))) (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close formula_m

theorem sentence_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) : sentence_m.TrueIn ℳ := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff formula_m).mpr
  intro η
  exact introduction_l hℳ η _ _ _ _ _ _ _ _ _

noncomputable def support_m :
    Derives.FiniteTheorySupport PowerlessTheory.theory_m [] sentence_m :=
  Classical.choice (PowerlessFiniteSupport.finite_m (fun _ hℳ => sentence_l hℳ))

def theory_m : Theory ℒ := Theory.ofList support_m.sentences

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ theory_m) : sentence_m.TrueIn ℳ :=
  support_m.derivation.semantically_entails ℳ hℳ

theorem satisfies_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ theory_m) (η : Env ℳ [] context_m) :
    formula_m.satisfies η :=
  (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff formula_m).mp (models_l hℳ) η

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthIntroduction
