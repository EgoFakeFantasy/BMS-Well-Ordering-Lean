import BMSConstructibleBridge.PowerlessCanonicalOrderLightHistory
import BMSConstructibleBridge.PowerlessCanonicalOrderOrdinalRestriction
import BMSConstructibleBridge.PowerlessRelativeLimitCanonicalOrderSuccessor
import BMSConstructibleBridge.PowerlessRelativeCofinalDefCoding

/-! # 原规范递归初段在实际母界中的轻量读数

固定同一 K 与已经构造的共尾编码包。Sat 从原真实 Class 函数 G 读取，
其完整规格由原包的 witnesses/sat_class 提供，不重新选择编码。
原层图的后继方程实际给出 Def，原比较方程给出同一 raw 输出。

本模块只把已在 C 中的前缀读成 Δ₀ 检查器；输出界、原父序及方程仍
明确列为局部归纳输入，必须在预算归纳中逐项消去，不是终局新假设。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalOrderLightHistoryOriginal

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

theorem hierarchy_def_l {δ F W a b A D : Raw}
    (hδ : Ordinal δ) (hF : PowerlessRelativeHierarchySemantics.history_l hℳ B δ F W)
    (hA : value_l (ℳ := 𝒱) F b A) (hD : value_l (ℳ := 𝒱) F a D)
    (hSucc : PowerlessRelativeHierarchySemantics.successor_l hℳ b a) :
    SecondOrderMemberDef.spec_l hℳ A D := by
  have haδ := (SecondOrderFunctionProperties.value_mem_l hℳ hF.1 hD).1
  have ha : Ordinal a := SetTheory.Structure.IsOrdinal.mem hδ haδ
  rcases hF.2 a D ⟨haδ, hD⟩ with ⟨hEmpty, _⟩ | ⟨c, Y, hSucc', hY, hDef⟩ | ⟨hLimit, _⟩
  · exact False.elim (hEmpty b (PowerlessRelativeHierarchyStep.successor_member_l hℳ hSucc))
  · have hEq := PowerlessRelativeHierarchyStep.successor_unique_l hℳ ha hSucc hSucc'
    subst c
    have hAEq := SecondOrderFunctionProperties.value_unique_l hℳ hF.1 hA hY
    exact hAEq.symm ▸ hDef
  · exact False.elim (PowerlessRelativeHierarchyStep.successor_not_limit_l hℳ ha hSucc hLimit)

variable (hBase)

/-- 实际 Sat 函数的同一输出填入后继证书，不以 Sat 存在作新前提。 -/
theorem from_equations_l (K : source_coding_l hℳ)
    {ξ C W δ β F f g r P₀ : Raw}
    (ω e t₁ t₂ t₃ Pair N Valid Translation G : type_l hℳ B)
    {L : SecondOrderModel.set_l ℳ}
    (hCode : PowerlessRelativeCofinalDefCoding.spec_l (W := W)
      hBase K ω e t₁ t₂ t₃ Pair N Valid Translation G L)
    (hLimit : limit_l hℳ ξ) (hC : level_l hℳ B ξ C)
    (hωC : mem_l hℳ ω.val C) (hWC : ∀ x, mem_l hℳ x W → mem_l hℳ x C)
    (hδ : Ordinal δ) (hF : PowerlessRelativeHierarchySemantics.history_l hℳ B δ F W)
    (hf : map_l (ℳ := 𝒱) f β r)
    (hReadF : ∀ a X, value_l (ℳ := 𝒱) f a X → value_l (ℳ := 𝒱) F a X)
    (hg : map_l (ℳ := 𝒱) g β C)
    (hEquations : PowerlessCanonicalOrderOrdinalRestriction.equations_l K
      t₁.val t₂.val t₃.val Pair.val Valid.val B P₀ f g)
    (hOrder : ∀ a A P, value_l (ℳ := 𝒱) f a A → value_l (ℳ := 𝒱) g a P →
      wellOrder_l (ℳ := 𝒱) A P) :
    PowerlessCanonicalOrderLightHistory.holds_l (𝒩 := 𝒱)
      C W ω.val F G.val P₀ β g := by
  obtain ⟨he, _ht₁, _ht₂, _ht₃, _hN, hPairMap, hPair, hValid⟩ :=
    PowerlessRelativeClassStaticCodingReading.reading_l K hCode.omega_eq hCode.static
  obtain ⟨V, hV, _⟩ := SecondOrderTriangularFormulaSyntax.exists_l hℳ
  have hCClass := PowerlessRelativeLevelClosure.class_l hℳ hBase hC
  have inClass : ∀ x, mem_l hℳ x C → PowerlessRelativeClassCorrespondence.member_l hℳ B x :=
    fun x hx => PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hCClass hx
  refine ⟨hg, ?_⟩
  intro a ha E _hEC hE
  obtain ⟨X, hX, _⟩ := hf.2 a ha
  rcases hEquations a X E hX.2 hE with hZero | hSuccessor | hUnion
  · exact Or.inl ⟨hZero.1, hZero.2.2⟩
  · obtain ⟨b, A, Q, hSucc, hA, hQ, hStep⟩ := hSuccessor
    have hFA := hReadF b A hA
    have hFX := hReadF a X hX.2
    have hAW := (SecondOrderFunctionProperties.value_mem_l hℳ hF.1 hFA).2
    have hXW := (SecondOrderFunctionProperties.value_mem_l hℳ hF.1 hFX).2
    have hQC := (SecondOrderFunctionProperties.value_mem_l hℳ hg hQ).2
    obtain ⟨Sat, hSat, _⟩ := hCode.sat_map.2 A hAW
    obtain ⟨_hSatW, Seq, _Idx, _I, _Query, _hSeqW, _hIdxW, _hIW, _hQueryW,
      hSeq, _⟩ := hCode.witnesses A Sat hAW hSat.2
    let A' : type_l hℳ B := ⟨A, inClass A (hWC A hAW)⟩
    let X' : type_l hℳ B := ⟨X, inClass X (hWC X hXW)⟩
    let Q' : type_l hℳ B := ⟨Q, inClass Q hQC⟩
    let Sat' : type_l hℳ B := ⟨Sat, inClass Sat (hWC Sat hSat.1)⟩
    have hSatSpec := hCode.sat_class A' Seq Sat' hAW hSeq hSat.2
    have hDef := hierarchy_def_l hδ hF hFA hFX hSucc
    have hStep' : SecondOrderCanonicalOrderUniform.step_l (ℳ₀ := 𝒱)
        ω.val A Q e.val t₁.val t₂.val t₃.val Pair.val Valid.val X E := by
      rw [hCode.omega_eq, he]
      exact hStep
    have hResult := PowerlessRelativeLimitCanonicalOrderSuccessor.member_l hBase K hLimit hC
      ω A' Q' e t₁ t₂ t₃ Pair Valid Sat' X' hCode.omega_eq he hCode.static.1
      hPairMap hPair hV (hValid V hV) hSatSpec hDef
      hωC (hWC A hAW) hQC (hWC Sat hSat.1) (hWC X hXW) (hOrder b A Q hA hQ) hStep'
    exact Or.inr (Or.inl ⟨b, PowerlessRelativeHierarchyStep.successor_member_l hℳ hSucc,
      A, hAW, X, hXW, Sat, hSat.1, Q, hQC, hSucc, hFA, hFX, hSat.2, hQ, hResult.2.1⟩)
  · exact Or.inr (Or.inr ⟨hUnion.1,
      (PowerlessHierarchyLightHistory.union_reading_l hℳ hg).mpr hUnion.2.2⟩)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalOrderLightHistoryOriginal
