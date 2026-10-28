import BMSConstructibleBridge.PowerlessRelativeCofinalDefFunction
import BMSConstructibleBridge.PowerlessRelativeCutoffInnerLimits
import BMSConstructibleBridge.PowerlessRelativeCutoffLimit
import BMSConstructibleBridge.PowerlessMemberDefDerives

/-! # 截断分支的实际统一 Def 函数：原 Z₂ 推导

纯隶属 ℒ 对象句仍使用原 global_m 及原函数规格；正式出口在原
num/set 语言的 SecondOrderArithmetic.theory_m 推导核中。所有编码、
完整 Sat 及精确行像的守卫在实际装配中消去，只保留基集传递、实际
ω、首个类内不可数 Ω 和 W=LΩ。输出图属于实际 Class，不要求图属于 W。

原 Def 与读数对全部 raw A、H 成立，不把参数限到类内枚举域。
该函数不是长前史，不能以此假定源 Collection、枚举图∈W 或
无条件固定高度 BMS 证明已经完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffDefFunction

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

/-- 实际图的全域／陪域均为 W，图自身只声明 Class 成员性。 -/
theorem exists_l (K : source_coding_l hℳ) {B ω Ω W : SecondOrderQuotient.type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B ω Ω)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W) :
    ∃ D : type_l hℳ B, map_l (ℳ := SecondOrderQuotient.structure_l hℳ) D.val W W ∧
      ∀ A H : SecondOrderQuotient.type_l hℳ,
        value_l (ℳ := SecondOrderQuotient.structure_l hℳ) D.val A H ↔
          mem_l hℳ A W ∧ SecondOrderMemberDef.spec_l hℳ A H := by
  have hωW := PowerlessRelativeOrdinalCoverage.covered_l hℳ K hBase Ω W hW ω
    (PowerlessRelativeCutoffBelow.omega_below_l (hBase := hBase) K hω hΩ)
  have hKωW : mem_l hℳ K.omega W :=
    (SecondOrderOmega.unique_l hℳ hω K.omega_spec) ▸ hωW
  exact PowerlessRelativeCofinalDefFunction.exists_l hBase K
    (PowerlessRelativeCutoffLimit.limit_l K hBase hω hΩ) hW
    (PowerlessRelativeCutoffInnerLimits.cofinal_l K hBase hω hΩ) hKωW

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

/-- 四个自由参数依次为 W、Ω、ω、B；不加入编码或枚举守卫。 -/
def schema_m : Formula ℒ [] [.set, .set, .set, .set] :=
  let W : Term ℒ [] [.set, .set, .set, .set] .set := .fvar .here
  let Ω := .fvar (.there .here)
  let ω := .fvar (.there (.there .here))
  let B := .fvar (.there (.there (.there .here)))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeOrdinalCutoff.first_m B ω Ω) <|
        .imp (PowerlessRelativeHierarchySyntax.level_m B Ω W) <|
          .existsE .set <| .conj (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here)) <|
            .conj (SecondOrderObjectSyntax.map_m (.bvar .here) (up W) (up W)) <|
              .forallE .set <| .forallE .set <|
                .iff (SecondOrderObjectSyntax.value_m (.bvar (.there (.there .here)))
                  (.bvar (.there .here)) (.bvar .here))
                  (.conj (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (up (up (up W))))
                    (PowerlessMemberDefSyntax.global_m (.bvar (.there .here)) (.bvar .here)))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeOrdinalCutoff.first_formula_l K,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeHierarchySemantics.class_formula_l K, map_formula_l, value_formula_l,
    PowerlessMemberDefDerives.formula_l K, SecondOrderObjectSyntax.member_m,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  intro η hBase hω hΩ hW
  obtain ⟨D, hMap, hRead⟩ := exists_l K hBase hω hΩ hW
  exact ⟨D.val, D.property, hMap, hRead⟩

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffDefFunction
