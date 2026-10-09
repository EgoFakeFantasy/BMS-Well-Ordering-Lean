import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseEvaluation
import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseValues

/-! # 实际统一满足函数的全部输出沿同一坍缩读回

源 MemberI 的完整静态包和同一个 G₀ 的全部真实输出规格沿实际 H
运输。目标 G 的任意真实图值先由传递性取得输出成员资格，再由 H
满射在 Prop 中回溯到源输出；原图值双向保持识别同一 G₀/A₀/R₀。
不另选满足函数，不把目标域预设为 Class、可构造层或完整源模型。
原源历史装配在后续模块提供；这里不是最终无条件 Z₂ 对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseSatisfactionFunctionReading

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)
open PowerlessMemberCollapseTransport (relation_l environments_related_l push_free_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l PowerlessMemberStructure.type_l

universe u

/-- 同一十槽公式的实际环境；没有从图中抽取 Type 层坐标函数。 -/
def env_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω A e t₁ t₂ t₃ P N F R : carrier_l 𝒩) :
    Env 𝒩 [] PowerlessRelativeMembershipCollapseEvaluation.context_m :=
  let η₀ := ((Env.empty.pushFree ω).pushFree A).pushFree e
  let η₁ := ((η₀.pushFree t₁).pushFree t₂).pushFree t₃
  (((η₁.pushFree P).pushFree N).pushFree F).pushFree R

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

/-- 目标原商中实际 G 的每个输出满足原完整 Sat；源输出在 Prop 中逐次取得。 -/
theorem reading_l {I W T H : type_l hℳ}
    (hI : ∃ x, mem_l hℳ x I) (hT : ∃ x, mem_l hℳ x T)
    (hH : PowerlessRelativeMembershipCollapse.spec_l I T H)
    (hW : PowerlessNaturalOrder.transitive_l (ℳ := SecondOrderQuotient.structure_l hℳ) W)
    (hIW : subset_l (ℳ := SecondOrderQuotient.structure_l hℳ) I W)
    (hReflect : PowerlessRelativeFiniteHullClosure.pair_matrix_reflection_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) I W)
    (hClosed : PowerlessRelativeFiniteHullAssignments.closed_l
      (𝒩 := SecondOrderQuotient.structure_l hℳ) I)
    (ω₀ A₀ e₀ t₁₀ t₂₀ t₃₀ P₀ N₀ F₀ G₀ :
      PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I)
    (ω A e t₁ t₂ t₃ P N F G :
      PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) T)
    (hω : relation_l H ω₀ ω) (hA : relation_l H A₀ A)
    (he : relation_l H e₀ e) (ht₁ : relation_l H t₁₀ t₁)
    (ht₂ : relation_l H t₂₀ t₂) (ht₃ : relation_l H t₃₀ t₃)
    (hP : relation_l H P₀ P) (hN : relation_l H N₀ N)
    (hF : relation_l H F₀ F) (hG : relation_l H G₀ G)
    (hω₀ : SecondOrderOmega.omega_l hℳ ω₀.val)
    (hωI : ∀ x, mem_l hℳ x ω₀.val → mem_l hℳ x I)
    (hStatic : PowerlessSatisfactionExistenceSyntax.static_l
      (𝒩 := PowerlessMemberStructure.structure_l
        (ℳ := SecondOrderQuotient.structure_l hℳ) I hI) ω₀ e₀ t₁₀ t₂₀ t₃₀ P₀ N₀ F₀)
    (hSat : ∀ R₀ : PowerlessMemberStructure.type_l
        (ℳ := SecondOrderQuotient.structure_l hℳ) I,
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) G₀.val A₀.val R₀.val →
        PowerlessSatisfactionSpecification.spec_l
          (𝒩 := PowerlessMemberStructure.structure_l
            (ℳ := SecondOrderQuotient.structure_l hℳ) I hI)
          ω₀ A₀ e₀ t₁₀ t₂₀ t₃₀ P₀ F₀ R₀) :
    ∀ R, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) G.val A.val R →
      PowerlessRelativeMembershipCollapseEvaluation.data_l
        (𝒩 := SecondOrderQuotient.structure_l hℳ)
        ω.val A.val e.val t₁.val t₂.val t₃.val P.val N.val F.val R := by
  intro R hValue
  have hTrans : PowerlessNaturalOrder.transitive_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) T := fun x y hx hy => hH.1 x hx y hy
  have hRT := (PowerlessRelativeMemberSatisfactionReading.coordinates_l
    (hℳ := hℳ) (R := G) hTrans hValue).2
  obtain ⟨R₀, hR₀, hR⟩ := hH.2.2.1 R hRT
  let R₁ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I :=
    ⟨R₀, hR₀⟩
  let R₂ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) T :=
    ⟨R, hRT⟩
  have hRR : relation_l H R₁ R₂ := hR
  have hValue₀ := (PowerlessRelativeMembershipCollapseValues.model_l
    hI hT hH hW hIW hReflect hClosed.1 G₀ A₀ R₁ G A R₂ hG hA hR).mpr hValue
  let η := env_l (𝒩 := PowerlessMemberStructure.structure_l
    (ℳ := SecondOrderQuotient.structure_l hℳ) I hI) ω₀ A₀ e₀ t₁₀ t₂₀ t₃₀ P₀ N₀ F₀ R₁
  let ξ := env_l (𝒩 := PowerlessMemberStructure.structure_l
    (ℳ := SecondOrderQuotient.structure_l hℳ) T hT) ω A e t₁ t₂ t₃ P N F R₂
  have hEmpty : environments_related_l (relation_l H)
      (Env.empty (M := PowerlessMemberStructure.structure_l
        (ℳ := SecondOrderQuotient.structure_l hℳ) I hI))
      (Env.empty (M := PowerlessMemberStructure.structure_l
        (ℳ := SecondOrderQuotient.structure_l hℳ) T hT)) := by
    constructor <;> intro v <;> nomatch v
  have hEnv : environments_related_l (relation_l H) η ξ :=
    push_free_l (push_free_l (push_free_l (push_free_l (push_free_l
      (push_free_l (push_free_l (push_free_l (push_free_l (push_free_l
        hEmpty hω) hA) he) ht₁) ht₂) ht₃) hP) hN) hF) hRR
  have hData : PowerlessRelativeMembershipCollapseEvaluation.data_m.satisfies η :=
    (PowerlessRelativeMembershipCollapseEvaluation.formula_l η).mpr
      ⟨hStatic, hSat R₁ hValue₀⟩
  have hRaw := PowerlessRelativeMembershipCollapseEvaluation.raw_l
    hH hClosed η ξ hEnv hω₀ hωI hData
  exact (PowerlessRelativeMembershipCollapseEvaluation.formula_l
    (PowerlessRelativization.env_l ξ)).mp hRaw

#print axioms env_l
#print axioms reading_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseSatisfactionFunctionReading
