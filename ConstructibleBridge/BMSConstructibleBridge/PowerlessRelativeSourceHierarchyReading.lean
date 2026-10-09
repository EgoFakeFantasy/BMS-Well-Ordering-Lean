import BMSConstructibleBridge.PowerlessRelativeSourceDefGraphReading
import BMSConstructibleBridge.PowerlessRelativeSourceLightHistoryReading

/-! # 同一原源前史的完整构造历史运输

原 D 的完整 Def 图像与同一 f 的完整轻量历史在同一个 H 下装配，
后继分支恢复原 Def，极限分支保留所有成员的精确并，零分支保留
同一基集的像。目标是原 history_l，不是另一套有界后继检查器。
原源前史、原共尾编码包和共同族的真实资格仍显式保留；未假定
目标属于 Class、是某个层或满足完整源理论。本模块尚不证明
弱凝聚、完整 Collection 或最终无额外前提的 Derives Z₂。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceHierarchyReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l PowerlessMemberStructure.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

/-- 指定实际前史的同一像满足原零、Def 后继与极限并方程。 -/
theorem history_l {B β U I₀ W₀ Ω T H : type_l hℳ}
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
    (hf : PowerlessRelativeHierarchySemantics.history_l hℳ B A₀.val f.val U) :
    PowerlessRelativeHierarchySemantics.history_l hℳ B₁.val A₁.val g.val V.val := by
  let B₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
    ⟨B, hBI⟩
  let U₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
    ⟨U, hUI⟩
  have hTargetGraph := PowerlessRelativeSourceDefGraphReading.graph_l
    hBase K hLimit hU hCoding hΩ hLevel ζ I W τ hI hT ν hτ hI₀ hW₀ hIW h hH
    hBound hUI hGI hQI hωU hωI D₀ D₁ V e₁ t₁₁ t₂₁ t₃₁ P₁ N₁ F₁ Q₁ G₁
    hGraph hD hUV he ht₁ ht₂ ht₃ hP hN hF hQ hG
  have hLight := PowerlessHierarchyLightHistoryUnique.from_original_l hℳ
    (B := B) (D := D₀.val) (W := U) (α := A₀.val) (C := U) (f := f.val)
    hGraph.2 (fun _ hx => hx) hf
  have hTarget := PowerlessRelativeSourceLightHistoryReading.history_l ζ I W τ hI hT ν hτ
    hI₀ hW₀ (PowerlessRelativeLevelClosure.transitive_l hℳ hBase hLevel) hIW h hH
    B₀ D₀ A₀ U₀ f B₁ D₁ A₁ V g hB hD hA hUV hfg hLight
  exact PowerlessHierarchyLightHistoryUnique.to_original_l hℳ
    (B := B₁.val) (D := D₁.val) (W := V.val) (α := A₁.val) (C := V.val) (f := g.val)
    hTargetGraph.2 hTarget

#print axioms history_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceHierarchyReading
