import BMSConstructibleBridge.PowerlessRelativeCofinalMemberDefClosure
import BMSConstructibleBridge.PowerlessRelativeCutoffInnerLimits
import BMSConstructibleBridge.PowerlessRelativeCutoffLimit
import BMSConstructibleBridge.PowerlessMemberDefDerives
import BMSConstructibleBridge.SecondOrderAxioms

/-! # 首个类内不可数截止层的原 Def 闭包：原 Z₂ 推导

对象语言是纯隶属 ℒ，句子仍使用原 PowerlessMemberDefSyntax.global_m；
背景及正式推导核是原 num/set 的 SecondOrderArithmetic.theory_m。
基集传递、实际 ω、首个类内不可数 Ω 和实际 W=LΩ 是明确守卫。
极限、极限共尾和 ω∈W 的证书在证明内恢复，不附加类内可数性、
枚举图、Sat 见证、求值保持性或统一前史假设。

结论针对环境原商中的 Def(A,H) 和全部 raw 对象，给出 H∈W。
它不是 member-W 中原 global_m 的存在证明：后者的非空分支还要求
枚举图实际属于 W。完整源 Separation／Collection 和固定高度 BMS
的无条件对象推导仍须另外完成，不能以本条件式闭句替代。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffMemberDefClosure

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

/-- 截断分支提供共尾层守卫；原 Def 及其结果不缩成层内量词。 -/
theorem member_l (K : source_coding_l hℳ) {B ω Ω W A H : SecondOrderQuotient.type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B ω Ω)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W)
    (hAW : mem_l hℳ A W) (hDef : SecondOrderMemberDef.spec_l hℳ A H) :
    mem_l hℳ H W := by
  have hωW := PowerlessRelativeOrdinalCoverage.covered_l hℳ K hBase Ω W hW ω
    (PowerlessRelativeCutoffBelow.omega_below_l (hBase := hBase) K hω hΩ)
  have hKωW : mem_l hℳ K.omega W :=
    (SecondOrderOmega.unique_l hℳ hω K.omega_spec) ▸ hωW
  exact PowerlessRelativeCofinalMemberDefClosure.member_l hBase K
    (PowerlessRelativeCutoffLimit.limit_l K hBase hω hΩ) hW
    (PowerlessRelativeCutoffInnerLimits.cofinal_l K hBase hω hΩ) hKωW hAW hDef

/-- 六个自由参数依次是 H、A、W、Ω、ω、B。 -/
def schema_m : Formula ℒ [] [.set, .set, .set, .set, .set, .set] :=
  let H : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar .here
  let A := .fvar (.there .here)
  let W := .fvar (.there (.there .here))
  let Ω := .fvar (.there (.there (.there .here)))
  let ω := .fvar (.there (.there (.there (.there .here))))
  let B := .fvar (.there (.there (.there (.there (.there .here)))))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeOrdinalCutoff.first_m B ω Ω) <|
        .imp (PowerlessRelativeHierarchySyntax.level_m B Ω W) <|
          .imp (SecondOrderObjectSyntax.member_m A W) <|
            .imp (PowerlessMemberDefSyntax.global_m A H) (SecondOrderObjectSyntax.member_m H W)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeOrdinalCutoff.first_formula_l K,
    PowerlessRelativeHierarchySemantics.level_formula_l K, PowerlessMemberDefDerives.formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval]
  intro η hBase hω hΩ hW hAW hDef
  exact member_l K hBase hω hΩ hW hAW hDef

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms member_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffMemberDefClosure
