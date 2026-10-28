import BMSConstructibleBridge.PowerlessCodedHistoryCoverageSyntax
import BMSConstructibleBridge.PowerlessRelativeMemberSatisfactionReading
import BMSConstructibleBridge.PowerlessMemberLegacyNumericAbsolute
import BMSConstructibleBridge.PowerlessRelativeFiniteHullHistory
import BMSConstructibleBridge.SecondOrderFoundation
import BMSConstructibleBridge.PowerlessMemberOperationClosure

/-! # 任意捕获整包在原商中的完整资格读回

对象语言为纯成员 ℒ，背景为原 Z₂。只要求实际外层 W 传递、对配对与
二元并闭合，以及给定 ω 是原内部 ω。全部参数仍是同一 W 中的给定
见证；母界 U 不预设为可构造层，I 不参与传递性假设。
完整 Sat／Def 检查器函数图、旧数字资格、真实序数和轻量前史均读回
原商；全部内部有限赋值由 W 的实际闭包回收，再使用同一 U 的覆盖。
这还不是原 Def／构造历史认同，不证明完整源模型或最终 BMS 推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberCodedHistoryReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l PowerlessMemberStructure.type_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {W : SecondOrderQuotient.type_l hℳ} {hW₀ : ∃ x, mem_l hℳ x W}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => PowerlessMemberStructure.structure_l (ℳ := 𝒱) W hW₀
local notation "M" => PowerlessMemberStructure.type_l (ℳ := 𝒱) W

/-- 完整图的原商读数，量词范围不缩为 W 中已经给出的输入／输出。 -/
private theorem graph_l (hTrans : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) W)
    (G U : M) (P : M → M → Prop)
    (Q : SecondOrderQuotient.type_l hℳ → SecondOrderQuotient.type_l hℳ → Prop)
    (hMatrix : ∀ a r, P a r ↔ Q a.val r.val)
    (h : map_l (ℳ := 𝒩₀) G U U ∧ ∀ a r, value_l (ℳ := 𝒩₀) G a r ↔
      member_l 𝒩₀ a U ∧ member_l 𝒩₀ r U ∧ P a r) :
    map_l (ℳ := 𝒱) G.val U.val U.val ∧ ∀ a r, value_l (ℳ := 𝒱) G.val a r ↔
      member_l 𝒱 a U.val ∧ member_l 𝒱 r U.val ∧ Q a r := by
  have hMap := (PowerlessSourceGraphAbsolute.map_l hTrans).mp h.1
  refine ⟨hMap, ?_⟩
  intro a r
  constructor
  · intro hValue
    obtain ⟨ha, hr⟩ := SecondOrderFunctionProperties.value_mem_l hℳ hMap hValue
    let a₀ : M := ⟨a, hTrans U.val a U.property ha⟩
    let r₀ : M := ⟨r, hTrans U.val r U.property hr⟩
    have hRow := (h.2 a₀ r₀).mp ((PowerlessSourceGraphAbsolute.value_l hTrans).mpr hValue)
    exact ⟨hRow.1, hRow.2.1, (hMatrix a₀ r₀).mp hRow.2.2⟩
  · rintro ⟨ha, hr, hRow⟩
    let a₀ : M := ⟨a, hTrans U.val a U.property ha⟩
    let r₀ : M := ⟨r, hTrans U.val r U.property hr⟩
    exact (PowerlessSourceGraphAbsolute.value_l hTrans).mp
      ((h.2 a₀ r₀).mpr ⟨ha, hr, (hMatrix a₀ r₀).mpr hRow⟩)

private theorem satisfaction_matrix_l
    (hTrans : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) W)
    (ω e t₁ t₂ t₃ P N F U a r : M) :
    PowerlessSatisfactionNormalizedMatrix.holds_l (𝒩 := 𝒩₀) ω a e N P U U t₁ t₂ t₃ F r ↔
      PowerlessSatisfactionNormalizedMatrix.holds_l (𝒩 := 𝒱)
        ω.val a.val e.val N.val P.val U.val U.val t₁.val t₂.val t₃.val F.val r.val := by
  let η : Env 𝒩₀ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set] :=
    Env.empty |>.pushFree r |>.pushFree F |>.pushFree t₃ |>.pushFree t₂ |>.pushFree t₁
      |>.pushFree U |>.pushFree U |>.pushFree P |>.pushFree N |>.pushFree e
      |>.pushFree a |>.pushFree ω
  have hMatrix : PowerlessSatisfactionNormalizedMatrix.holds_l (𝒩 := 𝒩₀)
      ω a e N P U U t₁ t₂ t₃ F r ↔
      PowerlessSatisfactionNormalizedMatrix.holds_l (𝒩 := 𝒱)
        ω.val a.val e.val N.val P.val U.val U.val t₁.val t₂.val t₃.val F.val r.val := by
    let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set] :=
      PowerlessSatisfactionNormalizedMatrix.formula_m
        (.fvar .here)
        (.fvar (.there .here))
        (.fvar (.there (.there .here)))
        (.fvar (.there (.there (.there .here))))
        (.fvar (.there (.there (.there (.there .here)))))
        (.fvar (.there (.there (.there (.there (.there .here))))))
        (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
        (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
        (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
        (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
        (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
        (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))
    have hφ : Formula.IsDelta0 StabilityFrame.membershipLevyBound φ :=
      PowerlessSatisfactionNormalizedMatrix.delta_l _ _ _ _ _ _ _ _ _ _ _ _
    have h := PowerlessMemberBounded.formula_l
      (fun x hx y hy => hTrans x y hx hy) hφ η
    simpa only [φ, PowerlessSatisfactionNormalizedMatrix.formula_l, Term.eval,
      Env.pushFree_here, Env.pushFree_there, PowerlessRelativization.env_l, η] using h
  exact hMatrix

/-- 同一 G 的完整规范函数图，包括全部 raw 候选。 -/
theorem satisfaction_l (hTrans : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) W)
    (ω e t₁ t₂ t₃ P N F U G : M)
    (h : PowerlessMemberSatisfactionFunctionAbsolute.spec_l (𝒩 := 𝒩₀) ω e t₁ t₂ t₃ P N F U G) :
    PowerlessMemberSatisfactionFunctionAbsolute.spec_l (𝒩 := 𝒱)
      ω.val e.val t₁.val t₂.val t₃.val P.val N.val F.val U.val G.val :=
  graph_l hTrans G U
    (fun a r => PowerlessSatisfactionNormalizedMatrix.holds_l (𝒩 := 𝒩₀) ω a e N P U U t₁ t₂ t₃ F r)
    (fun a r => PowerlessSatisfactionNormalizedMatrix.holds_l (𝒩 := 𝒱)
      ω.val a e.val N.val P.val U.val U.val t₁.val t₂.val t₃.val F.val r)
    (fun a r => satisfaction_matrix_l hTrans ω e t₁ t₂ t₃ P N F U a r) h

private theorem def_matrix_l (hTrans : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) W)
    (ω e N Q U G a r : M) :
    PowerlessMemberDefImageBounded.holds_l (𝒩 := 𝒩₀) ω e N Q U G a r ↔
      PowerlessMemberDefImageBounded.holds_l (𝒩 := 𝒱)
        ω.val e.val N.val Q.val U.val G.val a.val r.val := by
  let η : Env 𝒩₀ [] [.set, .set, .set, .set, .set, .set, .set, .set] :=
    Env.empty |>.pushFree r |>.pushFree a |>.pushFree G |>.pushFree U
      |>.pushFree Q |>.pushFree N |>.pushFree e |>.pushFree ω
  have hMatrix : PowerlessMemberDefImageBounded.holds_l (𝒩 := 𝒩₀) ω e N Q U G a r ↔
      PowerlessMemberDefImageBounded.holds_l (𝒩 := 𝒱)
        ω.val e.val N.val Q.val U.val G.val a.val r.val := by
    let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] :=
      PowerlessMemberDefImageBounded.formula_m
        (.fvar .here)
        (.fvar (.there .here))
        (.fvar (.there (.there .here)))
        (.fvar (.there (.there (.there .here))))
        (.fvar (.there (.there (.there (.there .here)))))
        (.fvar (.there (.there (.there (.there (.there .here))))))
        (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
        (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
    have hφ : Formula.IsDelta0 StabilityFrame.membershipLevyBound φ :=
      PowerlessMemberDefImageBounded.delta_l _ _ _ _ _ _ _ _
    have h := PowerlessMemberBounded.formula_l
      (fun x hx y hy => hTrans x y hx hy) hφ η
    simpa only [φ, PowerlessMemberDefImageBounded.formula_l, Term.eval,
      Env.pushFree_here, Env.pushFree_there, PowerlessRelativization.env_l, η] using h
  exact hMatrix

/-- 同一 D 的完整检查器函数图；尚未把有界检查器认同为原 Def。 -/
theorem def_l (hTrans : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) W)
    (ω e N Q U G D : M)
    (h : PowerlessMemberDefFunctionAbsolute.spec_l (𝒩 := 𝒩₀) ω e N Q U G D) :
    PowerlessMemberDefFunctionAbsolute.spec_l (𝒩 := 𝒱)
      ω.val e.val N.val Q.val U.val G.val D.val :=
  graph_l hTrans D U
    (fun a r => PowerlessMemberDefImageBounded.holds_l (𝒩 := 𝒩₀) ω e N Q U G a r)
    (fun a r => PowerlessMemberDefImageBounded.holds_l (𝒩 := 𝒱)
      ω.val e.val N.val Q.val U.val G.val a r)
    (fun a r => def_matrix_l hTrans ω e N Q U G a r) h

private theorem light_l (hTrans : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) W)
    (B D A U f : M) :
    PowerlessHierarchyLightHistory.holds_l (𝒩 := 𝒩₀) B D A U f ↔
      PowerlessHierarchyLightHistory.holds_l (𝒩 := 𝒱) B.val D.val A.val U.val f.val := by
  let η : Env 𝒩₀ [.set, .set, .set, .set, .set] [] :=
    (Env.empty : Env 𝒩₀ [] []) |>.pushBound (sort := SetTheory.SetSort.set) B
      |>.pushBound (sort := SetTheory.SetSort.set) D |>.pushBound (sort := SetTheory.SetSort.set) A
      |>.pushBound (sort := SetTheory.SetSort.set) U |>.pushBound (sort := SetTheory.SetSort.set) f
  have h := PowerlessMemberBounded.formula_l
    (fun x hx y hy => hTrans x y hx hy) (PowerlessRelativeFiniteHullHistory.matrix_delta_l []) η
  simpa only [PowerlessRelativeFiniteHullHistory.matrix_m, PowerlessHierarchyLightHistory.formula_l,
    Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there,
    PowerlessRelativization.env_l, η] using h

/-- 覆盖全部内部有限长度，先从外层 W 的真实闭包回收同一个函数图。 -/
theorem finite_l (K : source_coding_l hℳ)
    (hTrans : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) W)
    (hClosed : PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) W)
    (ω U : M) (hω : ω.val = K.omega)
    (h : PowerlessCodedHistoryCoverageSyntax.finite_l (𝒩 := 𝒩₀) ω U) :
    PowerlessCodedHistoryCoverageSyntax.finite_l (𝒩 := 𝒱) ω.val U.val := by
  intro a ha f hf
  obtain ⟨n, hn, hMap⟩ := hf
  let a₀ : M := ⟨a, hTrans U.val a U.property ha⟩
  let n₀ : M := ⟨n, hTrans ω.val n ω.property hn⟩
  let f₀ : M := ⟨f, PowerlessRelativeMemberSatisfactionReading.assignment_l K hTrans hClosed
    (ω := ω) (A := a₀) hω hn hMap⟩
  exact h a₀ ha f₀ ⟨n₀, hn, (PowerlessSourceGraphAbsolute.map_l hTrans).mpr hMap⟩

/-- 原包逐对象读回，不要求 U 是层、I 传递或 W 满足完整源理论。 -/
theorem point_l (K : source_coding_l hℳ)
    (hTrans : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) W)
    (hClosed : PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) W)
    (B ω x a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G : M)
    (hω : SecondOrderOmega.omega_l hℳ ω.val)
    (h : PowerlessCodedHistoryCoverageSyntax.point_l (𝒩 := 𝒩₀)
      B ω x a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G) :
    PowerlessCodedHistoryCoverageSyntax.point_l (𝒩 := 𝒱)
      B.val ω.val x.val a.val y.val A.val U.val D.val f.val e.val
      t₁.val t₂.val t₃.val t₄.val P.val N.val F.val V.val Q.val G.val := by
  rcases h with ⟨ha, hf, hx, hB, hωU, hStatic, hG, hD, hNumeric, hA, hHistory,
    hFinite, hUTrans, hUClosed⟩
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  have heRaw := (PowerlessSourceNaturalAbsolute.zero_l hTrans).mp hStatic.1.1
  have he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val :=
    SecondOrderQuotient.ext_l hℳ _ _ (fun z => iff_of_false (heRaw z)
      (PowerlessBMSQuotientSuccessor.zero_l K z))
  have hStaticRaw := PowerlessRelativeMemberSatisfactionReading.static_raw_l
    K hTrans hClosed hωEq he hStatic
  have hFoundation := SecondOrderFoundation.models_l hℳ
  change ∀ S : SecondOrderQuotient.type_l hℳ, (∃ z, mem_l hℳ z S) →
    ∃ z, mem_l hℳ z S ∧ ∀ t, mem_l hℳ t z → ¬mem_l hℳ t S at hFoundation
  have hOrdinal := PowerlessMemberOrdinalAbsolute.source_l hTrans (fun S hS => by
    obtain ⟨z, hz, hMinimal⟩ := hFoundation S hS
    exact ⟨z, hz, fun t ht htz => hMinimal t htz ht⟩) A hA
  exact ⟨ha, (PowerlessSourceGraphAbsolute.value_l hTrans).mp hf, hx, hB, hωU,
    hStaticRaw, satisfaction_l hTrans ω e t₁ t₂ t₃ P N F U G hG,
    def_l hTrans ω e N Q U G D hD,
    (PowerlessMemberLegacyNumericAbsolute.spec_l hTrans ω e t₁ t₂ t₃ t₄ P N V Q).mp hNumeric,
    hOrdinal, (light_l hTrans B D A U f).mp hHistory,
    finite_l K hTrans hClosed ω U hωEq hFinite,
    (PowerlessMemberOperationClosure.transitive_l hTrans U).mp hUTrans,
    (PowerlessMemberOperationClosure.closed_l hTrans hClosed U).mp hUClosed⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberCodedHistoryReading
