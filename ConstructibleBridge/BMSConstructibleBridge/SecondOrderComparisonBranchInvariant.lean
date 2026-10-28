import BMSConstructibleBridge.SecondOrderComparisonLimitInvariant
import BMSConstructibleBridge.PowerlessRelativeLevelClosure
import BMSConstructibleBridge.SecondOrderComparisonCanonicalSyntax

/-! # 原比较正文三分支的实际归纳步

读取原层次方程并消去不相容分类。后继旧层的传递性由已证明的实际层
性质取得，先排除缺省输出，再组合前驱初段；极限相容性来自归纳假设。
这里证明行不变量，尚须将同一递归历史的每行接入它。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonBranchInvariant

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderWellOrderCoherentUnion (stage_l extension_l)
open SecondOrderComparisonNativeRow (parameters_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "v" => SecondOrderQuotient.mk_l hℳ
private abbrev zero_l (K : source_coding_l hℳ) := (numberCode_l K (SecondOrderModel.zero_l ℳ)).val

private theorem extension_trans_l {A R D S X P : type_l hℳ}
    (hAD : extension_l (ℳ₀ := 𝒱) A R D S) (hDX : extension_l (ℳ₀ := 𝒱) D S X P) :
    extension_l (ℳ₀ := 𝒱) A R X P := by
  refine ⟨fun x hx => hDX.1 x (hAD.1 x hx), ?_, ?_⟩
  · intro x y hx hy
    exact (hDX.2.1 x y (hAD.1 x hx) (hAD.1 y hy)).trans (hAD.2.1 x y hx hy)
  · intro x y hx hy hyx
    have hyD := hDX.2.2 x y (hAD.1 x hx) hy hyx
    exact hAD.2.2 x y hx hyD ((hDX.2.1 y x hyD (hAD.1 x hx)).mp hyx)

set_option maxHeartbeats 1000000 in
theorem row_l (K : source_coding_l hℳ) (p : parameters_l ℳ)
    {A : SecondOrderGraph.code_l ℳ} {B F r G q a i X Q : type_l hℳ}
    {Root Index Prec : SecondOrderModel.set_l ℳ}
    (hConfig : SecondOrderComparisonNativeConfiguration.configuration_l K p A B F r Root Index Prec)
    (hSupport : SecondOrderComparisonStaticSupport.support_l K B r (v p.C) (v p.f) (v p.P₀))
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hG : map_l (ℳ := 𝒱) G K.omega q)
    (ha : mem_l hℳ a (v A)) (hi : stage_l (ℳ₀ := 𝒱) (v p.I) (v p.T) G i X Q)
    (hia : value_l (ℳ := 𝒱) (v p.J) i a)
    (hIH : ∀ b, mem_l hℳ b a →
      SecondOrderComparisonInvariant.at_l (𝒩 := 𝒱) (v p.I) (v p.J) (v p.T) G b)
    (U : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega) (W : SecondOrderModel.set_l ℳ)
    (hU : setRel_l K U W)
    (hBranch : SecondOrderComparisonStageSyntax.branch_l K.omega (zero_l K)
      (v p.t₁) (v p.t₂) (v p.t₃) (v p.Pair) (v p.Valid) (v p.J) (v p.T) G
      (v p.P₀) (v p.f) a X U.val)
    (hQ : SecondOrderComparisonDecode.graph_l K (v p.C) (v p.f) W Q) :
    wellOrder_l (ℳ := 𝒱) X Q ∧ (∀ j Y R,
      stage_l (ℳ₀ := 𝒱) (v p.I) (v p.T) G j Y R →
      (∃ b, value_l (ℳ := 𝒱) (v p.J) j b ∧ mem_l hℳ b a) →
      extension_l (ℳ₀ := 𝒱) Y R X Q) ∧
      SecondOrderComparisonCanonicalSyntax.branch_l K.omega (zero_l K)
        (v p.t₁) (v p.t₂) (v p.t₃) (v p.Pair) (v p.Valid) (v p.J) (v p.T) G (v p.P₀) a X Q := by
  obtain ⟨a', hia', ha'X⟩ := (hConfig.layerRead i X).mp hi.2.1
  have hEq := SecondOrderFunctionLaws.value_unique_l hℳ hConfig.indexMap hia' hia
  have haX : value_l (ℳ := 𝒱) F a X := hEq ▸ ha'X
  have hStep := hConfig.hierarchy.2 a X ⟨ha, haX⟩
  have hα : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) a := by
    apply SetTheory.Structure.IsOrdinal.mem hConfig.ordinal
    exact ha
  rcases hBranch with ⟨hEmpty, hEncoded⟩ | ⟨b, j, Y, hSucc, hjb, hjY, hSuccessor⟩ | ⟨hLimit, D, hD, hOutput⟩
  · have hXB : X = B := by
      rcases hStep with ⟨_, hXB⟩ | ⟨b, _, hb, _, _⟩ | ⟨hLimit, _⟩
      · exact hXB
      · exact False.elim (hEmpty b (PowerlessRelativeHierarchyStep.successor_member_l hℳ hb))
      · obtain ⟨b, hb⟩ := hLimit.1
        exact False.elim (hEmpty b hb)
    subst X
    refine ⟨SecondOrderComparisonStagePreservation.zero_order_l K hSupport U W hU hEncoded hQ, ?_,
      Or.inl ⟨hEmpty, SecondOrderComparisonStagePreservation.zero_graph_l K hSupport U W hU hEncoded hQ⟩⟩
    rintro j Y R _ ⟨b, _, hb⟩
    exact False.elim (hEmpty b hb)
  · have hb := PowerlessRelativeHierarchyStep.successor_member_l hℳ hSucc
    have hjI := (SecondOrderFunctionLaws.value_mem_l hℳ hConfig.indexMap hjb).1
    obtain ⟨b', hjb', hb'Y⟩ := (hConfig.layerRead j Y).mp hjY
    have hbb' := SecondOrderFunctionLaws.value_unique_l hℳ hConfig.indexMap hjb' hjb
    have hbY : value_l (ℳ := 𝒱) F b Y := hbb' ▸ hb'Y
    have hDef : SecondOrderMemberDef.spec_l hℳ Y X := by
      rcases hStep with ⟨hEmpty, _⟩ | ⟨c, Z, hc, hcZ, hDef⟩ | ⟨hLimit, _⟩
      · exact False.elim (hEmpty b hb)
      · have hcb := PowerlessRelativeHierarchyStep.successor_unique_l hℳ hα hc hSucc
        subst c
        have hZY := SecondOrderFunctionLaws.value_unique_l hℳ hConfig.hierarchy.1 hcZ hbY
        exact hZY ▸ hDef
      · exact False.elim (PowerlessRelativeHierarchyStep.successor_not_limit_l hℳ hα hSucc hLimit)
    obtain ⟨P, hjP, hOutput⟩ := hSuccessor
    have hOld := hIH b hb j Y P ⟨⟨hjI, hjY, hjP⟩, hjb⟩
    have hbA : mem_l hℳ b (v A) := hConfig.ordinal.transitive a ha b hb
    have hYTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase
      (show PowerlessRelativeHierarchySemantics.level_l hℳ B b Y from
        ⟨v A, F, r, hConfig.ordinal, hbA, hConfig.hierarchy, hbY⟩)
    have hXC := hSupport.layers X (SecondOrderFunctionLaws.value_mem_l hℳ hConfig.hierarchy.1 haX).2
    obtain ⟨hOrder, hExtension, hCanonical⟩ := SecondOrderComparisonStagePreservation.successor_order_l K
      (hℳ := hℳ) (C := v p.C) (f := v p.f) (A := Y) (P := P) (D := X) (Q := Q)
      hConfig.coding hSupport.enumeration hSupport.onto hXC hOld.1
      (fun x y hx hy => hYTrans x hx y hy) hDef U W hU hOutput hQ
    refine ⟨hOrder, ?_, Or.inr (Or.inl ⟨b, j, Y, P, hSucc, hjb, hjY, hjP, hCanonical⟩)⟩
    rintro k Z R hk ⟨c, hkc, hc⟩
    rcases (hSucc c).mp hc with hcb | hcb
    · exact extension_trans_l (hℳ := hℳ) (hOld.2 k Z R ⟨hk, c, hkc, hcb⟩) hExtension
    · subst c
      have hkj := hConfig.indexInjective k j b hkc hjb
      subst k
      have hZY := SecondOrderFunctionLaws.value_unique_l hℳ hConfig.layerMap hk.2.1 hjY
      subst Z
      have hRP := SecondOrderFunctionLaws.value_unique_l hℳ hG hk.2.2 hjP
      subst R
      exact hExtension
  · have hUnion : PowerlessRelativeHierarchySemantics.union_l hℳ F a X := by
      rcases hStep with ⟨hEmpty, _⟩ | ⟨b, _, hb, _, _⟩ | ⟨_, hUnion⟩
      · obtain ⟨b, hb⟩ := hLimit.1
        exact False.elim (hEmpty b hb)
      · exact False.elim (PowerlessRelativeHierarchyStep.successor_not_limit_l hℳ hα hb hLimit)
      · exact hUnion
    have hSubset : subset_l (ℳ := 𝒱) a (v A) := fun b hb => hConfig.ordinal.transitive a ha b hb
    obtain ⟨hOrder, hInitial⟩ := SecondOrderComparisonLimitInvariant.order_l K p hConfig hSupport hG
      hSubset hD hUnion hIH U W hU hOutput hQ
    have hCover := SecondOrderStageLayerFunction.limit_cover_l hConfig.indexMap hConfig.indexOnto
      hSubset hD hConfig.layerRead hUnion
    have hXC := hSupport.layers X (SecondOrderFunctionLaws.value_mem_l hℳ hConfig.hierarchy.1 haX).2
    have hGraph := SecondOrderComparisonStagePreservation.limit_graph_l K hSupport.enumeration
      hSupport.onto hXC hCover U W hU hOutput hQ
    exact ⟨hOrder, hInitial, Or.inr (Or.inr ⟨hLimit, D, hD, hGraph⟩)⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonBranchInvariant
