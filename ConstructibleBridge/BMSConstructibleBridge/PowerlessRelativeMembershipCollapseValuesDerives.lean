import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseValues

/-! # 原推导核中的指定图值坍缩运输

对象语言为纯隶属 ℒ，背景为原 Z₂，推导关系为原 Derives。
闭句显式保留传递外层、外层真实闭包、同域四公式反射和实际坍缩守卫。
I 的真实闭包由这些守卫证明，而不是追加为假设。结论只保持给定相关
端点的原图值，不断言完整源模型存在或最终 BMS 良序性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseValuesDerives

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderObjectSyntax (member_m value_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

/-- 参数是实际原项；反射族没有自由参数，不需额外的 I 内参数资格。 -/
def schema_m {Δ : SortContext ℒ} (I W T H f a b g x y : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  let guard := .conj (PowerlessRelativeHierarchyDerives.transitive_m W) <|
    .conj (PowerlessRelativeFiniteHullAssignments.closed_m W) <|
      .conj (ThirdOrderTheory.subset_m I W) <|
        .conj (PowerlessRelativeFiniteElementarity.form_m
          (PowerlessRelativeFiniteHullClosure.family_m []) I W (fun v => nomatch v)) <|
          .conj (PowerlessRelativeMembershipCollapse.spec_m I T H) <|
            .conj (member_m f I) <| .conj (member_m a I) <| .conj (member_m b I) <|
              .conj (member_m g T) <| .conj (member_m x T) <| .conj (member_m y T) <|
                .conj (value_m H f g) <| .conj (value_m H a x) (value_m H b y)
  .imp guard (.iff (PowerlessValueBounded.formula_m f a b) (PowerlessValueBounded.formula_m g x y))

def sentence_m {Δ : SortContext ℒ} (I W T H f a b g x y : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m I W T H f a b g x y)

theorem models_l
    {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} (I W T H f a b g x y : Term ℒ [] Δ .set) :
    (sentence_m I W T H f a b g x y).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro ζ
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeFiniteHullAssignments.closed_formula_l,
    ThirdOrderSemantics.subset_formula_l,
    PowerlessRelativeMembershipCollapse.spec_formula_l,
    ThirdOrderSemantics.value_formula_l, PowerlessValueBounded.formula_l,
    member_m, Arguments.eval]
  rintro ⟨hTrans, hClosed, hIW, hReflection, hH, hf, ha, hb, hg, hx, hy, hfg, hax, hby⟩
  have hW : PowerlessNaturalOrder.transitive_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) (W.eval ζ) :=
    fun x y hx hy => hTrans x hx y hy
  have hRead := (PowerlessRelativeFiniteHullClosure.family_formula_l
    ζ I W (fun v : Variable ([] : SortContext ℒ) .set => nomatch v)).mp hReflection
  have hClosedI := PowerlessRelativeFiniteHullClosure.closure_l
    ζ I W (fun v : Variable ([] : SortContext ℒ) .set => nomatch v)
    (fun a b => SecondOrderPairObjects.pair_exists_l hℳ a b)
    (PowerlessRelativeFiniteHullClosure.binary_exists_l hℳ)
    (fun a b hz => SecondOrderQuotient.ext_l hℳ a b hz)
    hW hClosed hIW rfl rfl hReflection
  exact PowerlessRelativeMembershipCollapseValues.model_l
    ⟨f.eval ζ, hf⟩ ⟨g.eval ζ, hg⟩ hH hW hIW hRead.2.1 hClosedI.1
    ⟨f.eval ζ, hf⟩ ⟨a.eval ζ, ha⟩ ⟨b.eval ζ, hb⟩
    ⟨g.eval ζ, hg⟩ ⟨x.eval ζ, hx⟩ ⟨y.eval ζ, hy⟩ hfg hax hby

/-- 每个原项实例的普通对象推导；不是仅对原商作宿主真值断言。 -/
theorem derives_m {Δ : SortContext ℒ} (I W T H f a b g x y : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m I W T H f a b g x y)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ I W T H f a b g x y)

#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseValuesDerives
