import BMSConstructibleBridge.PowerlessRelativeClassGraphSpecificationAbsolute
import BMSConstructibleBridge.PowerlessRelativeClassStaticAmbient
import BMSConstructibleBridge.PowerlessRelativeClassOrdinalAbsolute
import BMSConstructibleBridge.PowerlessRelativeClassFiniteMapLift
import BMSConstructibleBridge.PowerlessRawCodedHistoryReading

/-! # 给定完整 Class 编码包的原历史读数

原 Z₂、纯隶属 ℒ。全部内部有限赋值先实际取得 Class 资格；原二元
操作输出由配对和并集闭包取得资格，然后才消费类内闭包。完整
Sat／Def 检查器及轻量前史读回同一 raw 包，由原认同定理恢复原 Def
和原历史。不给待验母界预供可构造层、内部枚举或完整类理论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCodedHistoryReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => structure_l hℳ B hBase
local notation "M" => type_l hℳ B

/-- 量化全部 raw 有限图；不把待证 Class 资格藏入量词域。 -/
theorem finite_l (ω U : M) (hω : SecondOrderOmega.omega_l hℳ ω.val)
    (h : PowerlessCodedHistoryCoverageSyntax.finite_l (𝒩 := 𝒩₀) ω U) :
    PowerlessCodedHistoryCoverageSyntax.finite_l (𝒩 := 𝒱) ω.val U.val := by
  intro z hz f hf
  obtain ⟨n, hn, hMap⟩ := hf
  let z₀ : M := ⟨z, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase U.property hz⟩
  let n₀ : M := ⟨n, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property hn⟩
  let f₀ : M := ⟨f, PowerlessRelativeClassFiniteMapLift.member_l hBase ω.property z₀.property hω hn hMap⟩
  exact h z₀ hz f₀ ⟨n₀, hn, (PowerlessRelativeClassFunctionAbsolute.map_l f₀ n₀ z₀).mpr hMap⟩

/-- 任意原操作输出先证明属于 Class，再使用给定 U 的类内闭包。 -/
theorem closed_l (U : M)
    (h : PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒩₀) U) :
    PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) U.val := by
  constructor
  · intro a b p ha hb hp
    let a₀ : M := ⟨a, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase U.property ha⟩
    let b₀ : M := ⟨b, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase U.property hb⟩
    let p₀ : M := ⟨p, PowerlessRelativeClassPair.pair_l hℳ hBase a₀.property b₀.property hp⟩
    exact h.1 a₀ b₀ p₀ ha hb ((PowerlessRelativeClassFunctionAbsolute.pair_l (hBase := hBase) a₀ b₀ p₀).mpr hp)
  · intro a b c ha hb hc
    let a₀ : M := ⟨a, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase U.property ha⟩
    let b₀ : M := ⟨b, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase U.property hb⟩
    obtain ⟨p, hp⟩ := SecondOrderPairObjects.pair_exists_l hℳ a b
    have hpClass := PowerlessRelativeClassPair.pair_l hℳ hBase a₀.property b₀.property hp
    have hcClass := PowerlessRelativeClassBasicClosure.union_l hℳ hBase hpClass (by
      intro z
      constructor
      · intro hz
        rcases (hc z).mp hz with hza | hzb
        · exact ⟨a, (hp a).mpr (Or.inl rfl), hza⟩
        · exact ⟨b, (hp b).mpr (Or.inr rfl), hzb⟩
      · rintro ⟨v, hv, hzv⟩
        rcases (hp v).mp hv with rfl | rfl
        · exact (hc z).mpr (Or.inl hzv)
        · exact (hc z).mpr (Or.inr hzv))
    let c₀ : M := ⟨c, hcClass⟩
    exact h.2 a₀ b₀ c₀ ha hb (fun z => hc z.val)

/-- 原十七见证完整矩阵的全部 raw 读数，不替换任何见证。 -/
theorem point_l (K : source_coding_l hℳ)
    (B₀ ω x a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G : M)
    (hω : ω.val = K.omega)
    (h : PowerlessCodedHistoryCoverageSyntax.point_l (𝒩 := 𝒩₀)
      B₀ ω x a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G) :
    PowerlessCodedHistoryCoverageSyntax.point_l (𝒩 := 𝒱)
      B₀.val ω.val x.val a.val y.val A.val U.val D.val f.val e.val
        t₁.val t₂.val t₃.val t₄.val P.val N.val F.val V.val Q.val G.val := by
  obtain ⟨ha, hf, hx, hB, hωU, hStatic, hG, hD, hNumeric, hA, hLight,
    hFinite, hTrans, hClosed⟩ := h
  have hRawTrans : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) U.val := by
    intro z t hz ht
    let z₀ : M := ⟨z, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase U.property hz⟩
    let t₀ : M := ⟨t, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase z₀.property ht⟩
    exact hTrans z₀ t₀ hz ht
  exact ⟨ha, (PowerlessRelativeClassFunctionAbsolute.value_l f a y).mp hf, hx, hB, hωU,
    PowerlessRelativeClassStaticAmbient.reading_l K hω hStatic,
    (PowerlessRelativeClassGraphSpecificationAbsolute.satisfaction_l ω e t₁ t₂ t₃ P N F U G).mp hG,
    (PowerlessRelativeClassGraphSpecificationAbsolute.def_l ω e N Q U G D).mp hD,
    (PowerlessRelativeClassCoverageAbsolute.numeric_l ω e t₁ t₂ t₃ t₄ P N V Q).mp hNumeric,
    PowerlessRelativeClassOrdinalAbsolute.source_l (hBase := hBase) A hA,
    (PowerlessRelativeClassCoverageAbsolute.history_l B₀ D A U f).mp hLight,
    finite_l ω U (hω.symm ▸ K.omega_spec) hFinite, hRawTrans, closed_l U hClosed⟩

#print axioms finite_l
#print axioms closed_l
#print axioms point_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCodedHistoryReading
