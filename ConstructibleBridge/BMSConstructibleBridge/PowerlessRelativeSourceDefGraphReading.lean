import BMSConstructibleBridge.PowerlessRelativeSourceDefReading
import BMSConstructibleBridge.PowerlessRelativeSourceMapReading

/-! # 原共同源历史的完整 Def 函数图像

局部原 Def 截迹现在用于同一原 D:U→U 的全部真实图值。先由共同族
的完整 map 反射运输干净图、总性与唯一性，再对实际输出沿同一 H
回溯源参数。原图规格给出源 Def，局部截迹读回目标的完整原 Def。
反向先由目标 map 取真实输出，再用原 Def 唯一性识别任意 raw 候选；
因此不预设候选属于 T，不把有界检查器误称完整图，也不另选 Def 图。
原编码包、共同族及成员资格仍保留。本模块尚未完成弱凝聚或 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceDefGraphReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l PowerlessMemberStructure.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

/-- 指定原 Def 图的同一坍缩像满足全部 raw 坐标上的原完整图规格。 -/
theorem graph_l {B β U I₀ W₀ Ω T H : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (K : source_coding_l hℳ)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hU : PowerlessRelativeHierarchySemantics.level_l hℳ B β U)
    {ω e t₁ t₂ t₃ P N F Q G : PowerlessRelativeClassStructure.type_l hℳ B}
    {C : SecondOrderModel.set_l ℳ}
    (hCoding : PowerlessRelativeCofinalDefCoding.spec_l
      (W := U) hBase K ω e t₁ t₂ t₃ P N F Q G C)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B ω.val Ω)
    (hLevel : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W₀)
    {Δ Ε : SortContext ℒ} (ζ : Env (SecondOrderQuotient.structure_l hℳ) [] Ε)
    (I W : Term ℒ [] Ε .set)
    (τ : Variable (PowerlessRelativeSourceFamilyHistory.context_m Δ) .set → Term ℒ [] Ε .set)
    (hI : ∃ x, mem_l hℳ x I₀) (hT : ∃ x, mem_l hℳ x T)
    (ν : Env (PowerlessMemberStructure.structure_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ hI)
      [] (PowerlessRelativeSourceFamilyHistory.context_m Δ))
    (hτ : ∀ v, (τ v).eval ζ = (ν.freeVal v).val)
    (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hIW : subset_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ W₀)
    (h : (PowerlessRelativeFiniteElementarity.form_m
      (PowerlessRelativeSourceFamilyHistory.family_m Δ) I W τ).satisfies ζ)
    (hH : PowerlessRelativeMembershipCollapse.spec_l I₀ T H)
    (hBound : ∀ v : Variable PowerlessRelativeFiniteHullStatic.context_m .set,
      mem_l hℳ ((PowerlessRelativeFiniteHullStatic.env_l (PowerlessRelativization.env_l ν)
        ω.val e.val t₁.val t₂.val t₃.val P.val N.val F.val).boundVal v) I₀)
    (hUI : mem_l hℳ U I₀) (hGI : mem_l hℳ G.val I₀) (hQI : mem_l hℳ Q.val I₀)
    (hωU : mem_l hℳ ω.val U)
    (hωI : ∀ x, mem_l hℳ x K.omega → mem_l hℳ x I₀)
    (D₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀)
    (D₁ V e₁ t₁₁ t₂₁ t₃₁ P₁ N₁ F₁ Q₁ G₁ : PowerlessMemberStructure.type_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) T)
    (hGraph : PowerlessRelativeCofinalDefGraph.graph_l (hℳ := hℳ) U D₀.val)
    (hD : SecondOrderFunctionObjects.value_l hℳ H D₀.val D₁.val)
    (hUV : SecondOrderFunctionObjects.value_l hℳ H U V.val)
    (he : SecondOrderFunctionObjects.value_l hℳ H e.val e₁.val)
    (ht₁ : SecondOrderFunctionObjects.value_l hℳ H t₁.val t₁₁.val)
    (ht₂ : SecondOrderFunctionObjects.value_l hℳ H t₂.val t₂₁.val)
    (ht₃ : SecondOrderFunctionObjects.value_l hℳ H t₃.val t₃₁.val)
    (hP : SecondOrderFunctionObjects.value_l hℳ H P.val P₁.val)
    (hN : SecondOrderFunctionObjects.value_l hℳ H N.val N₁.val)
    (hF : SecondOrderFunctionObjects.value_l hℳ H F.val F₁.val)
    (hQ : SecondOrderFunctionObjects.value_l hℳ H Q.val Q₁.val)
    (hG : SecondOrderFunctionObjects.value_l hℳ H G.val G₁.val) :
    PowerlessRelativeCofinalDefGraph.graph_l (hℳ := hℳ) V.val D₁.val := by
  let U₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
    ⟨U, hUI⟩
  have hTransW := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hLevel
  have hW : PowerlessNaturalOrder.transitive_l (ℳ := SecondOrderQuotient.structure_l hℳ) W₀ :=
    fun x y hx hy => hTransW x hx y hy
  have hMap := PowerlessRelativeSourceMapReading.map_l ζ I W τ hI hT ν hτ hI₀ hW₀
    hTransW hIW h hH D₀ U₀ U₀ D₁ V V hD hUV hUV hGraph.1
  have hω : SecondOrderOmega.omega_l hℳ ω.val := hCoding.omega_eq.symm ▸ K.omega_spec
  have hClosedW := PowerlessRelativeFiniteHullClosure.limit_closed_l hℳ hBase
    (PowerlessRelativeCutoffLimit.limit_l K hBase hω hΩ) hLevel
  obtain ⟨hReflect, hClosed⟩ := PowerlessRelativeSourceFamilyHistory.closure_member_l
    ζ I W τ hI₀ hW₀ hW hClosedW hIW h
  have hRead (A R : type_l hℳ) (hValue : SecondOrderFunctionObjects.value_l hℳ D₁.val A R) :
      mem_l hℳ A V.val ∧ SecondOrderMemberDef.spec_l hℳ A R := by
    obtain ⟨hAV, hRV⟩ := SecondOrderFunctionProperties.value_mem_l hℳ hMap hValue
    have hAT : mem_l hℳ A T := hH.1 V.val V.property A hAV
    have hRT : mem_l hℳ R T := hH.1 V.val V.property R hRV
    obtain ⟨A₀, hAI, hA⟩ := hH.2.2.1 A hAT
    obtain ⟨R₀, hRI, hR⟩ := hH.2.2.1 R hRT
    let A₀' : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
      ⟨A₀, hAI⟩
    let R₀' : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
      ⟨R₀, hRI⟩
    let A₁ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) T :=
      ⟨A, hAT⟩
    let R₁ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) T :=
      ⟨R, hRT⟩
    have hDA : PowerlessMemberCollapseTransport.relation_l H A₀' A₁ := hA
    have hDR : PowerlessMemberCollapseTransport.relation_l H R₀' R₁ := hR
    have hSource := (PowerlessRelativeMembershipCollapseValues.model_l
      hI hT hH hW hIW hReflect hClosed.1 D₀ A₀' R₀' D₁ A₁ R₁ hD hDA hDR).mpr hValue
    obtain ⟨hAU, hDef⟩ := (hGraph.2 A₀ R₀).mp hSource
    have hTarget := PowerlessRelativeSourceDefReading.trace_l
      hBase K hLimit hU hCoding hΩ hLevel ζ I W τ hI hT ν hτ hI₀ hW₀ hIW h hH
      hBound hUI hGI hQI hωU hωI A₀' R₀' A₁ R₁ V e₁ t₁₁ t₂₁ t₃₁ P₁ N₁ F₁ Q₁ G₁
      hAU hDef hA hR hUV he ht₁ ht₂ ht₃ hP hN hF hQ hG
    exact ⟨hAV, hTarget.1⟩
  refine ⟨hMap, fun A R => ⟨hRead A R, ?_⟩⟩
  rintro ⟨hAV, hDef⟩
  obtain ⟨S, ⟨_, hAS⟩, _⟩ := hMap.2 A hAV
  have hEq : S = R := SecondOrderMemberDef.unique_l hℳ (hRead A S hAS).2 hDef
  exact hEq ▸ hAS

#print axioms graph_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceDefGraphReading
