import BMSConstructibleBridge.PowerlessRelativeSourceFamilyHistory
import BMSConstructibleBridge.PowerlessMemberCollapseTransport

/-! # 同一源共同族与坍缩映射的完整函数图读取

原完整 map 矩阵由同一共同族反射到非传递 MemberI，随后沿实际 H
运输到 MemberT。仅在传递 T 上使用纯 Δ₀ 绝对性，读回全部 raw 图
成员、总性与唯一性。既不假定 I 传递，也不从 H 抽取 Type 值函数。
这是完整 Def 图及前史运输的语义接口，不替代最终 Z₂ 对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceMapReading

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l PowerlessMemberStructure.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

/-- 消费同一共同族的 map 反射，保留实际图、定义域和陪域。 -/
theorem map_l {I₀ W₀ T H : type_l hℳ} {Δ Ε : SortContext ℒ}
    (ζ : Env (SecondOrderQuotient.structure_l hℳ) [] Ε) (I W : Term ℒ [] Ε .set)
    (τ : Variable (PowerlessRelativeSourceFamilyHistory.context_m Δ) .set → Term ℒ [] Ε .set)
    (hI : ∃ x, mem_l hℳ x I₀) (hT : ∃ x, mem_l hℳ x T)
    (ν : Env (PowerlessMemberStructure.structure_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ hI)
      [] (PowerlessRelativeSourceFamilyHistory.context_m Δ))
    (hτ : ∀ v, (τ v).eval ζ = (ν.freeVal v).val)
    (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hW : ∀ x, mem_l hℳ x W₀ → ∀ y, mem_l hℳ y x → mem_l hℳ y W₀)
    (hIW : subset_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ W₀)
    (h : (PowerlessRelativeFiniteElementarity.form_m
      (PowerlessRelativeSourceFamilyHistory.family_m Δ) I W τ).satisfies ζ)
    (hH : PowerlessRelativeMembershipCollapse.spec_l I₀ T H)
    (f A D : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀)
    (g C E : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) T)
    (hfg : PowerlessMemberCollapseTransport.relation_l H f g)
    (hAC : PowerlessMemberCollapseTransport.relation_l H A C)
    (hDE : PowerlessMemberCollapseTransport.relation_l H D E)
    (hMap : SecondOrderFunctionObjects.map_l hℳ f.val A.val D.val) :
    SecondOrderFunctionObjects.map_l hℳ g.val C.val E.val := by
  have hMember := (PowerlessRelativeFiniteHullMaps.model_l hI ζ I W τ ν hτ
    hI₀ hW₀ hW hIW (PowerlessRelativeSourceFamilyHistory.maps_l ζ I W τ h) f A D).mp hMap
  let η : Env (PowerlessMemberStructure.structure_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ hI) [] [.set, .set, .set] :=
    ((Env.empty.pushFree f).pushFree A).pushFree D
  let ξ : Env (PowerlessMemberStructure.structure_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) T hT) [] [.set, .set, .set] :=
    ((Env.empty.pushFree g).pushFree C).pushFree E
  let φ : Formula ℒ [] [.set, .set, .set] := PowerlessMapBounded.formula_m
    (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)
  have hEnv : PowerlessMemberCollapseTransport.environments_related_l
      (PowerlessMemberCollapseTransport.relation_l H) η ξ := by
    constructor
    · intro v
      nomatch v
    · intro v
      cases v with
      | here => exact hDE
      | there v => cases v with
        | here => exact hAC
        | there v => cases v with
          | here => exact hfg
          | there v => nomatch v
  have hSource : φ.satisfies η := (PowerlessMapBounded.formula_l η
    (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)).mpr hMember
  have hTarget := (PowerlessMemberCollapseTransport.member_l (hI := hI) (hT := hT)
    H hH.2.1 hH.2.2.1 hH.2.2.2.2.1 hH.2.2.2.2.2 φ η ξ hEnv).mp hSource
  have hRaw := (PowerlessMemberBounded.formula_l hH.1
    (PowerlessMapBounded.delta_l
      (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)) ξ).mp hTarget
  exact (PowerlessMapBounded.formula_l (PowerlessRelativization.env_l ξ)
    (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)).mp hRaw

#print axioms map_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceMapReading
