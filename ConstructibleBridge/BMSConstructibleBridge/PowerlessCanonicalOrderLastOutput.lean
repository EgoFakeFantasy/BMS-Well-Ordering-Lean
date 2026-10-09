import BMSConstructibleBridge.PowerlessCanonicalOrderLightHistoryOriginal
import BMSConstructibleBridge.PowerlessRelativeLimitFunctionRange

/-! # 实际前缀母界中的下一规范比较输出

给定 b 之前的真实完整前缀图 p∈C，原比较方程在 b 的值也实际属于 C。
零步读取种子，后继从 p 的精确值域取得父序界，再读取同一 Sat 函数；
极限把原成员并认同 p 的全部输出并。旧 raw 陪域 q 始终不需是 Class。

这是内部预算归纳的局部延拓步骤；p∈C 和全部原方程由调用端的实际
归纳／限制证明提供，不作为最终 BMS 句的新增假设。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalOrderLastOutput

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "Ordinal" => SetTheory.Structure.IsOrdinal
  (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱)

variable (hBase)

theorem member_l (K : source_coding_l hℳ)
    {ξ C W δ F g q P₀ b p X E : Raw}
    (ω e t₁ t₂ t₃ Pair N Valid Translation G : type_l hℳ B)
    {L : SecondOrderModel.set_l ℳ}
    (hCode : PowerlessRelativeCofinalDefCoding.spec_l (W := W)
      hBase K ω e t₁ t₂ t₃ Pair N Valid Translation G L)
    (hLimit : limit_l hℳ ξ) (hC : level_l hℳ B ξ C)
    (hωC : mem_l hℳ ω.val C) (hWC : ∀ x, mem_l hℳ x W → mem_l hℳ x C)
    (hP₀C : mem_l hℳ P₀ C) (hbC : mem_l hℳ b C) (hpC : mem_l hℳ p C)
    (hδ : Ordinal δ) (hF : PowerlessRelativeHierarchySemantics.history_l hℳ B δ F W)
    (hp : map_l (ℳ := 𝒱) p b q)
    (hRead : ∀ a P, value_l (ℳ := 𝒱) p a P ↔ mem_l hℳ a b ∧ value_l (ℳ := 𝒱) g a P)
    (hEquations : PowerlessCanonicalOrderOrdinalRestriction.equations_l K
      t₁.val t₂.val t₃.val Pair.val Valid.val B P₀ F g)
    (hOrder : ∀ a A P, value_l (ℳ := 𝒱) F a A → value_l (ℳ := 𝒱) g a P →
      wellOrder_l (ℳ := 𝒱) A P)
    (hX : value_l (ℳ := 𝒱) F b X) (hE : value_l (ℳ := 𝒱) g b E) : mem_l hℳ E C := by
  rcases hEquations b X E hX hE with hZero | hSuccessor | hUnion
  · exact hZero.2.2.symm ▸ hP₀C
  · obtain ⟨a, A, P, hSucc, hA, hP, hStep⟩ := hSuccessor
    have hab := PowerlessRelativeHierarchyStep.successor_member_l hℳ hSucc
    have hPC := PowerlessRelativeLimitFunctionRange.value_member_l hBase hLimit hC
      hbC hpC hp ((hRead a P).mpr ⟨hab, hP⟩)
    have hAW := (SecondOrderFunctionProperties.value_mem_l hℳ hF.1 hA).2
    have hXW := (SecondOrderFunctionProperties.value_mem_l hℳ hF.1 hX).2
    have hDef := PowerlessCanonicalOrderLightHistoryOriginal.hierarchy_def_l hδ hF hA hX hSucc
    obtain ⟨he, _ht₁, _ht₂, _ht₃, _hN, hPairMap, hPair, hValid⟩ :=
      PowerlessRelativeClassStaticCodingReading.reading_l K hCode.omega_eq hCode.static
    obtain ⟨V, hV, _⟩ := SecondOrderTriangularFormulaSyntax.exists_l hℳ
    obtain ⟨Sat, hSat, _⟩ := hCode.sat_map.2 A hAW
    obtain ⟨_hSatW, Seq, _Idx, _I, _Query, _hSeqW, _hIdxW, _hIW, _hQueryW,
      hSeq, _⟩ := hCode.witnesses A Sat hAW hSat.2
    have hCClass := PowerlessRelativeLevelClosure.class_l hℳ hBase hC
    have inClass : ∀ x, mem_l hℳ x C → PowerlessRelativeClassCorrespondence.member_l hℳ B x :=
      fun x hx => PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hCClass hx
    let A' : type_l hℳ B := ⟨A, inClass A (hWC A hAW)⟩
    let X' : type_l hℳ B := ⟨X, inClass X (hWC X hXW)⟩
    let P' : type_l hℳ B := ⟨P, inClass P hPC⟩
    let Sat' : type_l hℳ B := ⟨Sat, inClass Sat (hWC Sat hSat.1)⟩
    have hSatSpec := hCode.sat_class A' Seq Sat' hAW hSeq hSat.2
    have hStep' : SecondOrderCanonicalOrderUniform.step_l (ℳ₀ := 𝒱)
        ω.val A P e.val t₁.val t₂.val t₃.val Pair.val Valid.val X E := by
      rw [hCode.omega_eq, he]
      exact hStep
    exact (PowerlessRelativeLimitCanonicalOrderSuccessor.member_l hBase K hLimit hC
      ω A' P' e t₁ t₂ t₃ Pair Valid Sat' X' hCode.omega_eq he hCode.static.1
      hPairMap hPair hV (hValid V hV) hSatSpec hDef hωC (hWC A hAW) hPC
      (hWC Sat hSat.1) (hWC X hXW) (hOrder a A P hA hP) hStep').1
  · have hUnionP : PowerlessRelativeHierarchySemantics.union_l hℳ p b E := by
      intro y
      refine (hUnion.2.2 y).trans ?_
      constructor
      · rintro ⟨a, P, ha, hP, hy⟩
        exact ⟨a, P, ha, (hRead a P).mpr ⟨ha, hP⟩, hy⟩
      · rintro ⟨a, P, ha, hP, hy⟩
        exact ⟨a, P, ha, ((hRead a P).mp hP).2, hy⟩
    exact PowerlessRelativeLimitFunctionRange.union_member_l hBase hLimit hC hbC hpC hp hUnionP

#print axioms member_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalOrderLastOutput
