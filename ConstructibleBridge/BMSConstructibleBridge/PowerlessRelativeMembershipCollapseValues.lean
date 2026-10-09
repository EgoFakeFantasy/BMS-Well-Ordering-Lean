import BMSConstructibleBridge.PowerlessRelativeFiniteHullMemberValues
import BMSConstructibleBridge.PowerlessRelativeMembershipCollapse
import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseBase
import BMSConstructibleBridge.PowerlessMemberCollapseTransport
import BMSConstructibleBridge.PowerlessMemberBounded
import BMSConstructibleBridge.PowerlessFormulaValidityReading
import BMSConstructibleBridge.SecondOrderOmegaTransitive

/-! # 实际成员坍缩保持原图的指定坐标取值

先由同一 I/W 的真实配对反射和闭包读取 MemberI 图值，再沿实际 H
运输同一个纯 Δ₀ 求值公式，最后只对传递目标 T 使用绝对性。
原图无需是函数或具有无垃圾成员规格，也不声称整图被 H 固定。
全部内部数码属于 ω；ω⊆I 和递归坍缩已给出的固定性保持每个数字
坐标。这是识别原 Def 查询的中间步骤，不是完整源 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseValues

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)
open PowerlessBMSQuotientCoding
open PowerlessFormulaValidityReading (code_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l PowerlessMemberStructure.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 给定相关的三项参数即可双向运输原关系值，不抽取整个 H 的值函数。 -/
theorem model_l {I W T H : type_l hℳ}
    (hI : ∃ x, mem_l hℳ x I) (hT : ∃ x, mem_l hℳ x T)
    (hH : PowerlessRelativeMembershipCollapse.spec_l I T H)
    (hW : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) W)
    (hIW : subset_l (ℳ := 𝒱) I W)
    (h : PowerlessRelativeFiniteHullClosure.pair_matrix_reflection_l (ℳ := 𝒱) I W)
    (hPair : ∀ a b p, mem_l hℳ a I → mem_l hℳ b I →
      ThirdOrderSemantics.pair_l (ℳ := 𝒱) a b p → mem_l hℳ p I)
    (f a b : PowerlessMemberStructure.type_l (ℳ := 𝒱) I)
    (g x y : PowerlessMemberStructure.type_l (ℳ := 𝒱) T)
    (hfg : PowerlessMemberCollapseTransport.relation_l H f g)
    (hax : PowerlessMemberCollapseTransport.relation_l H a x)
    (hby : PowerlessMemberCollapseTransport.relation_l H b y) :
    value_l (ℳ := 𝒱) f.val a.val b.val ↔ value_l (ℳ := 𝒱) g.val x.val y.val := by
  let η : Env (PowerlessMemberStructure.structure_l (ℳ := 𝒱) I hI) [] [.set, .set, .set] :=
    ((Env.empty.pushFree f).pushFree a).pushFree b
  let ξ : Env (PowerlessMemberStructure.structure_l (ℳ := 𝒱) T hT) [] [.set, .set, .set] :=
    ((Env.empty.pushFree g).pushFree x).pushFree y
  let φ : Formula ℒ [] [.set, .set, .set] := PowerlessValueBounded.formula_m
    (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)
  have hEnv : PowerlessMemberCollapseTransport.environments_related_l
      (PowerlessMemberCollapseTransport.relation_l H) η ξ := by
    constructor
    · intro v
      nomatch v
    · intro v
      cases v with
      | here => exact hby
      | there v => cases v with
        | here => exact hax
        | there v => cases v with
          | here => exact hfg
          | there v => nomatch v
  have hTransport := PowerlessMemberCollapseTransport.member_l
    (hI := hI) (hT := hT) H hH.2.1 hH.2.2.1 hH.2.2.2.2.1 hH.2.2.2.2.2 φ η ξ hEnv
  have hReadI := (PowerlessRelativeFiniteHullMemberValues.value_l
    (hI := hI) hW hIW h hPair f a b).trans
      (PowerlessValueBounded.formula_l η
        (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)).symm
  have hReadT := (PowerlessMemberBounded.formula_l hH.1
    (PowerlessValueBounded.delta_l
      (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)) ξ).trans
        (PowerlessValueBounded.formula_l (PowerlessRelativization.env_l ξ)
          (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here))
  exact hReadI.trans (hTransport.trans hReadT)

/-- 原 Z₂ 模型的全部内部数码坐标保持；不是只证明标准 numeral 的情形。 -/
theorem numeric_l (K : source_coding_l hℳ) {I W T H : type_l hℳ}
    (hI : ∃ x, mem_l hℳ x I) (hT : ∃ x, mem_l hℳ x T)
    (hH : PowerlessRelativeMembershipCollapse.spec_l I T H)
    (hW : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) W)
    (hIW : subset_l (ℳ := 𝒱) I W)
    (h : PowerlessRelativeFiniteHullClosure.pair_matrix_reflection_l (ℳ := 𝒱) I W)
    (hPair : ∀ a b p, mem_l hℳ a I → mem_l hℳ b I →
      ThirdOrderSemantics.pair_l (ℳ := 𝒱) a b p → mem_l hℳ p I)
    (hωI : ∀ x, mem_l hℳ x K.omega → mem_l hℳ x I)
    (f : PowerlessMemberStructure.type_l (ℳ := 𝒱) I)
    (g : PowerlessMemberStructure.type_l (ℳ := 𝒱) T)
    (hfg : PowerlessMemberCollapseTransport.relation_l H f g) :
    ∀ n s : SecondOrderModel.num_l ℳ,
      value_l (ℳ := 𝒱) f.val (code_l K n) (code_l K s) ↔
        value_l (ℳ := 𝒱) g.val (code_l K n) (code_l K s) := by
  have hFixed := PowerlessRelativeMembershipCollapseBase.fixed_l hℳ K.omega I T H
    (fun _ hx _ hy => SecondOrderOmegaTransitive.member_l hℳ K.omega_spec hx hy)
    hωI hH.2.1 hH.2.2.2.1
  have hCodeI (n : SecondOrderModel.num_l ℳ) : mem_l hℳ (code_l K n) I :=
    hωI _ (numberCode_l K n).property
  have hCodeH (n : SecondOrderModel.num_l ℳ) :
      SecondOrderFunctionObjects.value_l hℳ H (code_l K n) (code_l K n) :=
    hFixed _ (numberCode_l K n).property
  have hCodeT (n : SecondOrderModel.num_l ℳ) : mem_l hℳ (code_l K n) T := by
    obtain ⟨z, hz, _⟩ := hH.2.1.2 _ (hCodeI n)
    have hzEq := SecondOrderFunctionProperties.value_unique_l hℳ hH.2.1 hz.2 (hCodeH n)
    exact hzEq ▸ hz.1
  intro n s
  exact model_l hI hT hH hW hIW h hPair f
    ⟨code_l K n, hCodeI n⟩ ⟨code_l K s, hCodeI s⟩
    g ⟨code_l K n, hCodeT n⟩ ⟨code_l K s, hCodeT s⟩ hfg (hCodeH n) (hCodeH s)

#print axioms model_l
#print axioms numeric_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseValues
