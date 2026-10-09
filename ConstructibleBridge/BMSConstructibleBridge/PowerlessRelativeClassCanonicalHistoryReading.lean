import BMSConstructibleBridge.PowerlessRelativeClassHierarchyBranches
import BMSConstructibleBridge.PowerlessRelativeClassCanonicalStepOriginal
import BMSConstructibleBridge.PowerlessCanonicalOrderClassHistory

/-! # 同一实际层图与规范比较图的 Class 递归读数

原 Z₂ 背景下，原层历史提供真实 raw Def 和母集传递性，原规范层资格
提供母序良序。逐分支读入不重选图、编码、阶段或输出，也不把完整
计数式层次 AST 假定为绝对。存在出口实际消费原共尾编码整包；仍不
声称 raw 陪域或内部枚举图属于 Class。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalHistoryReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => structure_l hℳ B hBase
local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "M" => type_l hℳ B
local notation "Ordinal" => SetTheory.Structure.IsOrdinal
  (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱)

/-- 由给定原历史识别实际后继输出，不重新构造另一份层证书。 -/
theorem successor_def_l {δ F r b a Y X : Raw}
    (hδ : Ordinal δ) (hF : PowerlessRelativeHierarchySemantics.history_l hℳ B δ F r)
    (hSucc : PowerlessRelativeHierarchySemantics.successor_l hℳ b a)
    (hY : value_l (ℳ := 𝒱) F b Y) (hX : value_l (ℳ := 𝒱) F a X) :
    SecondOrderMemberDef.spec_l hℳ Y X := by
  have ha := (SecondOrderFunctionProperties.value_mem_l hℳ hF.1 hX).1
  have hα : Ordinal a := SetTheory.Structure.IsOrdinal.mem hδ ha
  rcases hF.2 a X ⟨ha, hX⟩ with ⟨hEmpty, _⟩ | ⟨c, Z, hSucc', hZ, hDef⟩ | ⟨hLimit, _⟩
  · exact False.elim (hEmpty b (PowerlessRelativeHierarchyStep.successor_member_l hℳ hSucc))
  · have hcb := PowerlessRelativeHierarchyStep.successor_unique_l hℳ hα hSucc' hSucc
    subst c
    have hZY := SecondOrderFunctionProperties.value_unique_l hℳ hF.1 hZ hY
    exact hZY ▸ hDef
  · exact False.elim (PowerlessRelativeHierarchyStep.successor_not_limit_l hℳ hα hSucc hLimit)

theorem reading_l (K : source_coding_l hℳ)
    (ω e t₁ t₂ t₃ Pair N Valid B₀ P₀ F g : M) {δ r : Raw}
    (hB₀ : B₀.val = B) (hω : ω.val = K.omega)
    (hStatic : PowerlessSatisfactionExistenceSyntax.static_l (𝒩 := 𝒩₀)
      ω e t₁ t₂ t₃ Pair N Valid)
    (hδ : Ordinal δ) (hF : PowerlessRelativeHierarchySemantics.history_l hℳ B δ F.val r)
    (hEquations : PowerlessCanonicalOrderOrdinalRestriction.equations_l K
      t₁.val t₂.val t₃.val Pair.val Valid.val B P₀.val F.val g.val)
    (hOrder : ∀ a X P, value_l (ℳ := 𝒱) F.val a X → value_l (ℳ := 𝒱) g.val a P →
      wellOrder_l (ℳ := 𝒱) X P) :
    PowerlessCanonicalOrderEquations.holds_l (𝒩 := 𝒩₀)
      ω e t₁ t₂ t₃ Pair Valid B₀ P₀ F g := by
  obtain ⟨he, _ht₁, _ht₂, _ht₃, _hN, hPairMap, hPair, hValid⟩ :=
    PowerlessRelativeClassStaticCodingReading.reading_l K hω hStatic
  obtain ⟨V, hV, _⟩ := SecondOrderTriangularFormulaSyntax.exists_l hℳ
  have he' : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val := he
  intro a X P hFX hGP
  have hX := (PowerlessRelativeClassFunctionAbsolute.value_l F a X).mp hFX
  have hP := (PowerlessRelativeClassFunctionAbsolute.value_l g a P).mp hGP
  rcases hEquations a.val X.val P.val hX hP with ⟨hEmpty, hXB, hPP₀⟩ |
    ⟨b, Y, Q, hSucc, hY, hQ, hStep⟩ | ⟨hLimit, hUnionF, hUnionG⟩
  · exact Or.inl ⟨(PowerlessRelativeClassOmegaAbsolute.empty_l (hBase := hBase) a).mpr hEmpty,
      Subtype.ext (hXB.trans hB₀.symm), Subtype.ext hPP₀⟩
  · have hCoordinates := PowerlessRelativeClassValueCoordinates.value_l hBase F hY
    have hQClass := (PowerlessRelativeClassValueCoordinates.value_l hBase g hQ).2
    let b₀ : M := ⟨b, hCoordinates.1⟩
    let Y₀ : M := ⟨Y, hCoordinates.2⟩
    let Q₀ : M := ⟨Q, hQClass⟩
    have hbδ := (SecondOrderFunctionProperties.value_mem_l hℳ hF.1 hY).1
    have hLevel : PowerlessRelativeHierarchySemantics.level_l hℳ B b Y :=
      ⟨δ, F.val, r, hδ, hbδ, hF, hY⟩
    have hDef := successor_def_l hδ hF hSucc hY hX
    have hStep' : SecondOrderCanonicalOrderUniform.step_l (ℳ₀ := 𝒱)
        ω.val Y Q e.val t₁.val t₂.val t₃.val Pair.val Valid.val X.val P.val := by
      rw [hω, he']
      exact hStep
    obtain ⟨E₀, hSame, hClassStep⟩ := PowerlessRelativeClassCanonicalStepOriginal.original_l
      K ω Y₀ Q₀ e t₁ t₂ t₃ Pair Valid X P.val hω he hStatic.1 hPairMap hPair
        hV (hValid V hV) (hOrder b Y Q hY hQ)
        (fun x y hx hy => PowerlessRelativeLevelClosure.transitive_l hℳ hBase hLevel x hx y hy) hDef hStep'
    have hEP : E₀ = P := Subtype.ext hSame
    refine Or.inr (Or.inl ⟨b₀, Y₀, Q₀,
      (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) b₀ a).mpr hSucc,
      (PowerlessRelativeClassFunctionAbsolute.value_l F b₀ Y₀).mpr hY,
      (PowerlessRelativeClassFunctionAbsolute.value_l g b₀ Q₀).mpr hQ, ?_⟩)
    exact hEP ▸ hClassStep
  · exact Or.inr (Or.inr ⟨(PowerlessRelativeClassHierarchyBranches.limit_l (hBase := hBase) a).mpr hLimit,
      (PowerlessRelativeClassHierarchyBranches.union_l (hBase := hBase) F a X).mpr hUnionF,
      (PowerlessRelativeClassHierarchyBranches.union_l (hBase := hBase) g a P).mpr hUnionG⟩)

/-- 原构造产出的同一比较 Class 图满足真正类内的无枚举递归公式。 -/
theorem exists_l (K : source_coding_l hℳ) {δ : Raw}
    (W F P₀ ω e t₁ t₂ t₃ Pair N Valid Translation G : M)
    {L : SecondOrderModel.set_l ℳ}
    (hCode : PowerlessRelativeCofinalDefCoding.spec_l (W := W.val)
      hBase K ω e t₁ t₂ t₃ Pair N Valid Translation G L)
    (hδ : Ordinal δ) (hF : PowerlessRelativeHierarchySemantics.history_l hℳ B δ F.val W.val)
    (hB : ∃ b, mem_l hℳ b B) (hSeed : wellOrder_l (ℳ := 𝒱) B P₀.val)
    (hBound : ∀ p, mem_l hℳ p P₀.val → ∃ x y,
      mem_l hℳ x B ∧ mem_l hℳ y B ∧ SecondOrderPairObjects.ordered_l hℳ x y p) :
    ∃ g : M, ∃ q : Raw, map_l (ℳ := 𝒱) g.val δ q ∧
      PowerlessCanonicalOrderEquations.holds_l (𝒩 := 𝒩₀) ω e t₁ t₂ t₃ Pair Valid
        ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ P₀ F g ∧
      ∀ a X P, value_l (ℳ := 𝒱) F.val a X →
        (value_l (ℳ := 𝒱) g.val a P ↔ SecondOrderCanonicalLevelSyntax.level_l
          K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val
          t₁.val t₂.val t₃.val Pair.val Valid.val B P₀.val a X P) := by
  obtain ⟨g, q, hMap, hEq, hRead⟩ := PowerlessCanonicalOrderClassHistory.exists_l
    hBase K W F P₀ ω e t₁ t₂ t₃ Pair N Valid Translation G hCode hδ hF hB hSeed hBound
  refine ⟨g, q, hMap, ?_, hRead⟩
  apply reading_l K ω e t₁ t₂ t₃ Pair N Valid _ P₀ F g rfl
    hCode.omega_eq hCode.static hδ hF hEq
  intro a X P hX hP
  exact SecondOrderCanonicalLevel.order_l ((hRead a X P hX).mp hP)

#print axioms reading_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalHistoryReading
