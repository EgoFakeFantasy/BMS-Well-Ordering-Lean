import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseClosure

/-! # 原局部母域在同一实际坍缩下的传递性与真实闭包

对象语言为纯成员语言 ℒ，背景与正式推导关系均为原 Z₂。原局部母域
U∈I 的像 V 是 H[U∩I]，不假定 U⊆I 或 H(U)=U。U 的传递性保证 V
传递；U 和 I 的真实操作闭包一起保证 V 的真实配对／二元并闭包。
这给原 Def 检查器的局部母界使用，不以整个目标 T 替换指定母界。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseSubdomain

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeMembershipCollapseInjectivity (recursive_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 局部母界的成员像资格来自原递归方程，不来自全域满射的模糊覆盖。 -/
theorem member_l {I U V H x y : type_l hℳ}
    (hRec : recursive_l hℳ I H) (hUI : mem_l hℳ U I)
    (hUV : SecondOrderFunctionObjects.value_l hℳ H U V)
    (hxI : mem_l hℳ x I) (hxU : mem_l hℳ x U)
    (hxy : SecondOrderFunctionObjects.value_l hℳ H x y) : mem_l hℳ y V :=
  (hRec U V hUI hUV y).mpr ⟨x, hxI, hxU, hxy⟩

/-- 不要求 I 传递；U 的真实传递性与同一 H 的递归方程已经足够。 -/
theorem transitive_l {I U V H : type_l hℳ}
    (hRec : recursive_l hℳ I H) (hUI : mem_l hℳ U I)
    (hUV : SecondOrderFunctionObjects.value_l hℳ H U V)
    (hU : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) U) :
    PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) V := by
  intro x y hx hy
  obtain ⟨a, haI, haU, hax⟩ := (hRec U V hUI hUV x).mp hx
  obtain ⟨b, hbI, hba, hby⟩ := (hRec a x haI hax y).mp hy
  exact member_l hRec hUI hUV hbI (hU a b haU hba) hby

/-- 两侧真实闭包同时回收源操作输出，因此输出像仍在指定局部母界。 -/
theorem closed_l {I T H U V : type_l hℳ}
    (hH : PowerlessRelativeMembershipCollapse.spec_l I T H)
    (hI : PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) I)
    (hU : PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) U)
    (hUI : mem_l hℳ U I) (hUV : SecondOrderFunctionObjects.value_l hℳ H U V) :
    PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) V := by
  constructor
  · intro x y p hx hy hp
    obtain ⟨a, haI, haU, hax⟩ := (hH.2.2.2.1 U V hUI hUV x).mp hx
    obtain ⟨b, hbI, hbU, hby⟩ := (hH.2.2.2.1 U V hUI hUV y).mp hy
    obtain ⟨c, hc⟩ := SecondOrderPairObjects.pair_exists_l hℳ a b
    have hcI := hI.1 a b c haI hbI hc
    have hcU := hU.1 a b c haU hbU hc
    obtain ⟨q, hq, _⟩ := hH.2.1.2 c hcI
    have hqPair := PowerlessRelativeMembershipCollapseClosure.pair_l
      hH.2.1 hH.2.2.2.1 haI hbI hcI hax hby hq.2 hc
    have hpEq : p = q := SecondOrderQuotient.ext_l hℳ p q
      (fun z => (hp z).trans (hqPair z).symm)
    exact hpEq.symm ▸ member_l hH.2.2.2.1 hUI hUV hcI hcU hq.2
  · intro x y p hx hy hp
    obtain ⟨a, haI, haU, hax⟩ := (hH.2.2.2.1 U V hUI hUV x).mp hx
    obtain ⟨b, hbI, hbU, hby⟩ := (hH.2.2.2.1 U V hUI hUV y).mp hy
    obtain ⟨c, hc⟩ := PowerlessRelativeFiniteHullClosure.binary_exists_l hℳ a b
    have hcI := hI.2 a b c haI hbI hc
    have hcU := hU.2 a b c haU hbU hc
    obtain ⟨q, hq, _⟩ := hH.2.1.2 c hcI
    have hqBinary := PowerlessRelativeMembershipCollapseClosure.binary_l
      hH.2.2.2.1 haI hbI hcI hax hby hq.2 hc
    have hpEq : p = q := SecondOrderQuotient.ext_l hℳ p q
      (fun z => (hp z).trans (hqBinary z).symm)
    exact hpEq.symm ▸ member_l hH.2.2.2.1 hUI hUV hcI hcU hq.2

/-- 整个真实 ω 对象进入局部像；成员固定不能单独替代此对象资格。 -/
theorem omega_l (K : source_coding_l hℳ) {I T H U V : type_l hℳ}
    (hH : PowerlessRelativeMembershipCollapse.spec_l I T H)
    (hUI : mem_l hℳ U I) (hUV : SecondOrderFunctionObjects.value_l hℳ H U V)
    (hωI : ∀ x, mem_l hℳ x K.omega → mem_l hℳ x I)
    (hω : mem_l hℳ K.omega I) (hωU : mem_l hℳ K.omega U) : mem_l hℳ K.omega V := by
  have hFixed := PowerlessRelativeMembershipCollapseBase.base_l hℳ K.omega I T H
    (fun _ hx _ hy => SecondOrderOmegaTransitive.member_l hℳ K.omega_spec hx hy)
    hωI hH.2.1 hH.2.2.2.1 hω
  exact member_l hH.2.2.2.1 hUI hUV hω hωU hFixed

/-- 局部母域闭包运输的原纯对象模式，不声称目标是某个可构造层。 -/
def schema_m {Δ : SortContext ℒ} (I T H U V : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m U) <|
    .imp (PowerlessRelativeFiniteHullAssignments.closed_m I) <|
      .imp (PowerlessRelativeFiniteHullAssignments.closed_m U) <|
        .imp (PowerlessRelativeMembershipCollapse.spec_m I T H) <|
          .imp (SecondOrderObjectSyntax.member_m U I) <|
            .imp (SecondOrderObjectSyntax.value_m H U V) <|
              .conj (PowerlessRelativeHierarchyDerives.transitive_m V)
                (PowerlessRelativeFiniteHullAssignments.closed_m V)

def sentence_m {Δ : SortContext ℒ} (I T H U V : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m I T H U V)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} (I T H U V : Term ℒ [] Δ .set) :
    (sentence_m I T H U V).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro ζ
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeFiniteHullAssignments.closed_formula_l,
    PowerlessRelativeMembershipCollapse.spec_formula_l,
    ThirdOrderSemantics.value_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval]
  intro hTrans hI hU hH hUI hUV
  have hTransU : PowerlessNaturalOrder.transitive_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) (U.eval ζ) :=
    fun x y hx hy => hTrans x hx y hy
  have hTransV := transitive_l hH.2.2.2.1 hUI hUV hTransU
  exact ⟨fun x hx y hy => hTransV x y hx hy, closed_l hH hI hU hUI hUV⟩

theorem derives_m {Δ : SortContext ℒ} (I T H U V : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m I T H U V)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ I T H U V)

#print axioms member_l
#print axioms transitive_l
#print axioms closed_l
#print axioms omega_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseSubdomain
