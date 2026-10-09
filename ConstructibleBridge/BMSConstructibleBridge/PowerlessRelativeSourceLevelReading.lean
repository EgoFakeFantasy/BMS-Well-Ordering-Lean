import BMSConstructibleBridge.PowerlessRelativeSourceHierarchyReading
import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseOrdinals

/-! # 实际源前史点的原构造层与精确成员像

同一 H 下的原完整历史已经成立；源母序数的像仍是原内部序数，
指定阶段的成员性与原图值共同运输。因此实际输出的像由同一目标
历史见证原 level_l，全部成员仍恰是源输出与 I 交集的像。
不预供目标层或 Class 资格，不假定阶段编号固定，不使用外部序数
归纳。本接口是逐历史点的凝聚步骤，尚未覆盖完整源 Collection、
无首 Ω 分支或最终 hSources；不是最终无条件对象良序推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceLevelReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l PowerlessMemberStructure.type_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

/-- 原实际历史中的指定点读回同一基集像上的原层，保留精确成员截迹。 -/
theorem level_l {B β U I₀ W₀ Ω T H : type_l hℳ}
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
    (hG : SecondOrderFunctionObjects.value_l hℳ H G.val G₁.val)
    (hBI : mem_l hℳ B I₀)
    (A₀ f : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀)
    (B₁ A₁ g : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) T)
    (hB : SecondOrderFunctionObjects.value_l hℳ H B B₁.val)
    (hA : PowerlessMemberCollapseTransport.relation_l H A₀ A₁)
    (hfg : PowerlessMemberCollapseTransport.relation_l H f g)
    (hf : PowerlessRelativeHierarchySemantics.history_l hℳ B A₀.val f.val U)
    (hα : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)) A₀.val)
    (a b : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀)
    (c d : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) T)
    (ha : mem_l hℳ a.val A₀.val)
    (hValue : SecondOrderFunctionObjects.value_l hℳ f.val a.val b.val)
    (hac : PowerlessMemberCollapseTransport.relation_l H a c)
    (hbd : PowerlessMemberCollapseTransport.relation_l H b d) :
    PowerlessRelativeHierarchySemantics.level_l hℳ B₁.val c.val d.val ∧
      ∀ Z, mem_l hℳ Z d.val ↔ ∃ Y, mem_l hℳ Y I₀ ∧ mem_l hℳ Y b.val ∧
        SecondOrderFunctionObjects.value_l hℳ H Y Z := by
  have hHistory := PowerlessRelativeSourceHierarchyReading.history_l
    hBase K hLimit hU hCoding hΩ hLevel ζ I W τ hI hT ν hτ hI₀ hW₀ hIW h hH
    hBound hUI hGI hQI hωU hωI D₀ D₁ V e₁ t₁₁ t₂₁ t₃₁ P₁ N₁ F₁ Q₁ G₁
    hGraph hD hUV he ht₁ ht₂ ht₃ hP hN hF hQ hG hBI A₀ f B₁ A₁ g hB hA hfg hf
  have hOrdinal := PowerlessRelativeMembershipCollapseOrdinals.ordinal_l
    (hℳ := hℳ) (α := A₀.val) (β := A₁.val) hH A₀.property hA hα
  have hDom := (hH.2.2.2.2.2 a.val A₀.val c.val A₁.val
    a.property A₀.property hac hA).mp ha
  have hω : SecondOrderOmega.omega_l hℳ ω.val := hCoding.omega_eq.symm ▸ K.omega_spec
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hLevel
  have hClosed := PowerlessRelativeFiniteHullClosure.limit_closed_l hℳ hBase
    (PowerlessRelativeCutoffLimit.limit_l K hBase hω hΩ) hLevel
  have hPoint : SecondOrderFunctionObjects.value_l hℳ g.val c.val d.val :=
    (PowerlessRelativeSourceFamilyHistory.value_image_l ζ I W τ hI₀ hW₀
      (fun x y hx hy => hTrans x hx y hy) hClosed hIW h hI hT hH f a b g c d hfg hac hbd).mp hValue
  exact ⟨⟨A₁.val, g.val, V.val, hOrdinal, hDom, hHistory, hPoint⟩,
    hH.2.2.2.1 b.val d.val b.property hbd⟩

#print axioms level_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceLevelReading
