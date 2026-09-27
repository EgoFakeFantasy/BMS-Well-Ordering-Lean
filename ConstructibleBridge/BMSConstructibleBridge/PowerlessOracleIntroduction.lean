import BMSConstructibleBridge.PowerlessOracleRules
import BMSConstructibleBridge.PowerlessFiniteSupport
import YesMetaZFC.Automation.ModelClosure

/-!
# 全部局部接受构造的实际有限支持

低层调用、原证书、与非、正无界存在及有界两种极性共享一个原闭句。
从其真实推导提取有限核心列表；小结构满足列表即可生成父接受证书，
不再向要求完整核心的环境构造定理传入小结构。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessOracleIntroduction

open Logic FirstOrder ThirdOrderSemantics PowerlessTruthOracle

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

def introduction_m (B : Formula ℒ [] context_m) {Γ Δ : SortContext ℒ}
    (ω e T t₁ t₂ t₃ n p c f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .imp (SecondOrderObjectSyntax.member_m c ω)
    (.imp (PowerlessOracleRules.step_m B ω e T t₁ t₂ t₃ n p c f)
      (accepts_m B ω e T t₁ t₂ t₃ n p c f))

theorem introduction_l (B : Formula ℒ [] context_m)
    {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ)
    (ω e T t₁ t₂ t₃ n p c f : Term ℒ Γ Δ .set) :
    (introduction_m B ω e T t₁ t₂ t₃ n p c f).satisfies η :=
  fun hc h => PowerlessOracleRules.step_l B hℳ η ω e T t₁ t₂ t₃ n p c f hc h

def formula_m (B : Formula ℒ [] context_m) : Formula ℒ [] context_m :=
  introduction_m B (.fvar .here) (.fvar (.there .here))
    (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))

def sentence_m (B : Formula ℒ [] context_m) : Sentence ℒ :=
  Metatheory.Formula.forall_close (formula_m B)

attribute [local irreducible] formula_m Metatheory.Formula.forall_close

theorem sentence_l (B : Formula ℒ [] context_m)
    {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) : (sentence_m B).TrueIn ℳ := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff (formula_m B)).mpr
  intro η
  unfold formula_m
  exact introduction_l B hℳ η _ _ _ _ _ _ _ _ _ _

noncomputable def support_m (B : Formula ℒ [] context_m) :
    Derives.FiniteTheorySupport PowerlessTheory.theory_m [] (sentence_m B) :=
  Classical.choice (PowerlessFiniteSupport.finite_m (fun _ hℳ => sentence_l B hℳ))

def theory_m (B : Formula ℒ [] context_m) : Theory ℒ := Theory.ofList (support_m B).sentences

theorem models_l (B : Formula ℒ [] context_m)
    {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ (theory_m B)) : (sentence_m B).TrueIn ℳ :=
  (support_m B).derivation.semantically_entails ℳ hℳ

theorem satisfies_l (B : Formula ℒ [] context_m)
    {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ (theory_m B)) (η : Env ℳ [] context_m) :
    (formula_m B).satisfies η :=
  (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff (formula_m B)).mp (models_l B hℳ) η

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessOracleIntroduction
