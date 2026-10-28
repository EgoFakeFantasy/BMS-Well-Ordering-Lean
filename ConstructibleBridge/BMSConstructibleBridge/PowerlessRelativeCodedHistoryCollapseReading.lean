import BMSConstructibleBridge.PowerlessRawCodedHistoryReading
import BMSConstructibleBridge.PowerlessMemberCodedHistoryReading
import BMSConstructibleBridge.PowerlessRelativeMemberCodedCoverage
import BMSConstructibleBridge.PowerlessRelativeFiniteHullCodedCoverage
import BMSConstructibleBridge.PowerlessMemberCollapseTransport
import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseClosure

/-! # 同一实际坍缩目标的原前史覆盖

对象语言为纯隶属 ℒ，背景为原 num/set Z₂。首 Ω 母层的实际覆盖先由
已有定理构造；真实共同族把覆盖 AST 捕获到同一个 MemberI。沿同一
H 运输完整原公式后，目标 T 的真实传递性和操作闭包读回同一批见证。
原基集及内部 ω 的完整成员包含保证它们被 H 固定，不重新选择基集。

不预供目标点资格、ClassT、实际层、完整源模型或 Collection。这里取得
全部目标成员的原类资格和原 Def 闭包，供已证弱凝聚消费；完整源公理
及最终良序仍待完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCodedHistoryCollapseReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l PowerlessMemberStructure.type_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ

/-- 见证全部属于同一个 T，资格则覆盖原商的全部量词。 -/
def packet_l (T B ω x : Raw) : Prop :=
  ∃ a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G :
      PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) T,
    PowerlessCodedHistoryCoverageSyntax.point_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      B ω x a.val y.val A.val U.val D.val f.val e.val
      t₁.val t₂.val t₃.val t₄.val P.val N.val F.val V.val Q.val G.val

/-- 成员域外延性直接来自真实传递性与原商外延性。 -/
theorem ext_l {T : Raw} (hT : ∃ x, mem_l hℳ x T)
    (hTrans : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) T) :
    SetTheory.Extensional (SetTheory.Definitional.Project.FirstOrderSemantics.reduct
      (PowerlessMemberStructure.structure_l (ℳ := 𝒱) T hT)) := by
  refine ⟨?_⟩
  intro a b h
  apply Subtype.ext
  apply SecondOrderQuotient.ext_l hℳ
  intro z
  constructor
  · intro hz
    exact (h ⟨z, hTrans a.val z a.property hz⟩).mp hz
  · intro hz
    exact (h ⟨z, hTrans b.val z b.property hz⟩).mpr hz

/-- 同一 raw 图固定基对象，并由实际陪域读数回收其成员资格。 -/
private theorem fixed_member_l {I T H B : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hBI : ∀ x, mem_l hℳ x B → mem_l hℳ x I)
    (hH : PowerlessRelativeMembershipCollapse.spec_l I T H) (hB : mem_l hℳ B I) :
    mem_l hℳ B T ∧ SecondOrderFunctionObjects.value_l hℳ H B B := by
  have hFixed := PowerlessRelativeMembershipCollapseBase.base_l hℳ B I T H
    hBase hBI hH.2.1 hH.2.2.2.1 hB
  obtain ⟨b, ⟨hb, hValue⟩, _⟩ := hH.2.1.2 B hB
  have hEq := SecondOrderFunctionProperties.value_unique_l hℳ hH.2.1 hValue hFixed
  exact ⟨hEq ▸ hb, hFixed⟩

/-- 泛化共同族消费；源覆盖从首 Ω 层构造，不把完整资格列为新前提。 -/
theorem coverage_l (K : source_coding_l hℳ)
    {I₀ W₀ T H Ω : Raw} {hI : ∃ x, mem_l hℳ x I₀}
    {hW : ∃ x, mem_l hℳ x W₀} {hT : ∃ x, mem_l hℳ x T}
    {Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (ζ : Env 𝒱 [] Ε) (I W : Term ℒ [] Ε .set)
    (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (ν : Env (PowerlessMemberStructure.structure_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ hI) [] Δ)
    (hτ : ∀ v, (τ v).eval ζ = (ν.freeVal v).val)
    (hIW : subset_l (ℳ := 𝒱) I₀ W₀) (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (B ω : PowerlessMemberStructure.type_l (ℳ := 𝒱) I₀)
    (hBase : ∀ x, mem_l hℳ x B.val → ∀ y, mem_l hℳ y x → mem_l hℳ y B.val)
    (hω : SecondOrderOmega.omega_l hℳ ω.val)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B.val ω.val Ω)
    (hLevel : PowerlessRelativeHierarchySemantics.level_l hℳ B.val Ω W₀)
    (hBI : ∀ x, mem_l hℳ x B.val → mem_l hℳ x I₀)
    (hωI : ∀ x, mem_l hℳ x ω.val → mem_l hℳ x I₀)
    (hClosed : PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) I₀)
    (hH : PowerlessRelativeMembershipCollapse.spec_l I₀ T H)
    (hElem : (PowerlessRelativeFiniteElementarity.form_m Φ I W τ).satisfies ζ) :
    ∀ x : PowerlessMemberStructure.type_l (ℳ := 𝒱) T,
      packet_l T B.val K.omega x.val := by
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  have hTransW : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) W₀ :=
    fun x y hx hy => PowerlessRelativeLevelClosure.transitive_l hℳ hBase hLevel x hx y hy
  have hTransT : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) T :=
    fun x y hx hy => hH.1 x hx y hy
  have hTargetClosed := PowerlessRelativeMembershipCollapseClosure.closed_l hH hClosed
  obtain ⟨hBT, hFixedB⟩ := fixed_member_l hBase hBI hH B.property
  obtain ⟨hωT, hFixedω⟩ := fixed_member_l
    (fun x hx y hy => SecondOrderOmegaTransitive.member_l hℳ hω hx hy)
    hωI hH ω.property
  let B₁ : PowerlessMemberStructure.type_l (ℳ := 𝒱) T := ⟨B.val, hBT⟩
  let ω₁ : PowerlessMemberStructure.type_l (ℳ := 𝒱) T := ⟨ω.val, hωT⟩
  have hR := PowerlessMemberCollapseTransport.graph_l (hI := hI) (hT := hT)
    H hH.2.1 hH.2.2.1 hH.2.2.2.2.1 hH.2.2.2.2.2
  obtain ⟨ξ, hξ⟩ := PowerlessMemberCollapseTransport.env_exists_l hR.left_total_l ν
  have hCoverElem := PowerlessRelativeFiniteElementarity.subfamily_formula_l
    (PowerlessRelativeFiniteHullCodedCoverage.family_m Δ) Φ hΦ ζ I W τ hElem
  intro x
  obtain ⟨z, hz, hzx⟩ := hH.2.2.1 x.val x.property
  let z₀ : PowerlessMemberStructure.type_l (ℳ := 𝒱) I₀ := ⟨z, hz⟩
  have hCover := PowerlessRelativeMemberCodedCoverage.exists_l (hW₀ := hW) K
    (PowerlessSourceInclusion.inclusion_l hIW B)
    (PowerlessSourceInclusion.inclusion_l hIW ω)
    (PowerlessSourceInclusion.inclusion_l hIW z₀) hBase hω hΩ hLevel
  have hInside := PowerlessRelativeFiniteHullCodedCoverage.capture_formula_l
    (hI := hI) (hW := hW) ζ I W τ ν hτ hIW hI₀ hW₀
    (ext_l hW hTransW) B ω z₀ hCoverElem hCover
  let η₀ := ν |>.pushBound (sort := SetTheory.SetSort.set) B
    |>.pushBound (sort := SetTheory.SetSort.set) ω |>.pushBound (sort := SetTheory.SetSort.set) z₀
  let η₁ := ξ |>.pushBound (sort := SetTheory.SetSort.set) B₁
    |>.pushBound (sort := SetTheory.SetSort.set) ω₁ |>.pushBound (sort := SetTheory.SetSort.set) x
  have hRelated : PowerlessMemberCollapseTransport.environments_related_l
      (PowerlessMemberCollapseTransport.relation_l H) η₀ η₁ :=
    PowerlessMemberCollapseTransport.push_l (x := z₀) (y := x)
      (PowerlessMemberCollapseTransport.push_l (x := ω) (y := ω₁)
        (PowerlessMemberCollapseTransport.push_l (x := B) (y := B₁) hξ hFixedB) hFixedω) hzx
  have hTarget := (PowerlessMemberCollapseTransport.formula_l hR
    (PowerlessRelativeFiniteHullCodedCoverage.exists_m Δ) η₀ η₁ hRelated).mp hInside
  have hPoint := (PowerlessRelativeFiniteHullCodedCoverage.exists_formula_l
    (ext_l hT hTransT) η₁).mp hTarget
  obtain ⟨a, y, A, U, D, f, e, t₁, t₂, t₃, t₄, P, N, F, V, Q, G, h⟩ := hPoint
  have hRaw := PowerlessMemberCodedHistoryReading.point_l (hW₀ := hT) K
    hTransT hTargetClosed B₁ ω₁ x a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G hω h
  exact ⟨a, y, A, U, D, f, e, t₁, t₂, t₃, t₄, P, N, F, V, Q, G, hωEq ▸ hRaw⟩

/-- 目标包中的同一原历史给出该成员的原相对类资格。 -/
theorem class_l (K : source_coding_l hℳ) {T B x : Raw}
    (h : packet_l T B K.omega x) : PowerlessRelativeClassCorrespondence.member_l hℳ B x := by
  obtain ⟨a, y, A, U, D, f, e, t₁, t₂, t₃, t₄, P, N, F, V, Q, G, hPoint⟩ := h
  exact (PowerlessRawCodedHistoryReading.level_l K rfl hPoint).2

/-- 原阶段与同一实际层对象都属于 T，供后续弱凝聚构造阶段集。 -/
theorem stage_l (K : source_coding_l hℳ) {T B x : Raw}
    (h : packet_l T B K.omega x) :
    ∃ a y, mem_l hℳ a T ∧ mem_l hℳ y T ∧
      PowerlessRelativeHierarchySemantics.level_l hℳ B a y ∧ mem_l hℳ x y := by
  obtain ⟨a, y, A, U, D, f, e, t₁, t₂, t₃, t₄, P, N, F, V, Q, G, hPoint⟩ := h
  exact ⟨a.val, y.val, a.property, y.property,
    (PowerlessRawCodedHistoryReading.level_l K rfl hPoint).1, hPoint.2.2.1⟩

/-- 原 Def 的候选输出没有成员前提；同一 D 的全域图将它回收进 T。 -/
theorem def_l (K : source_coding_l hℳ) {T B x r : Raw}
    (hTrans : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) T)
    (h : packet_l T B K.omega x) (hDef : SecondOrderMemberDef.spec_l hℳ x r) :
    mem_l hℳ r T := by
  obtain ⟨a, y, A, U, D, f, e, t₁, t₂, t₃, t₄, P, N, F, V, Q, G, hPoint⟩ := h
  have hHistory := PowerlessRawCodedHistoryReading.history_l K rfl hPoint
  have hGraph := PowerlessRawCodedHistoryReading.graph_l K rfl hPoint
  rcases hPoint with ⟨_ha, hf, hx, _hB, _hω, _hStatic, _hG, _hD, _hNumeric,
    _hA, _hLight, _hFinite, hUTrans, _hUClosed⟩
  have hyU := (SecondOrderFunctionProperties.value_mem_l hℳ hHistory.1 hf).2
  have hxU := hUTrans y.val x hyU hx
  have hValue := (hGraph.2 x r).mpr ⟨hxU, hDef⟩
  have hrU := (SecondOrderFunctionProperties.value_mem_l hℳ hGraph.1 hValue).2
  exact hTrans U.val r U.property hrU

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCodedHistoryCollapseReading
