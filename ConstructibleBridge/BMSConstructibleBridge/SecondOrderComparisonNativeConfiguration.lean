import BMSConstructibleBridge.SecondOrderComparisonNativeRecursion
import BMSConstructibleBridge.SecondOrderFunctionGraphComposition

/-! # 实际层次与固定参数的原比较递归配置

将真实序数、规范根表示、指标双射和层函数复合的证明收为 Prop 配置。
配置确实由已构造的原对象取得；参数码均在 Prop 存在证明中逐个取得，
不定义选码函数。载体、枚举及初始比较图在历史量词之前固定；它们的合法
良序／满射规格仍由后续不变量证明消费，不是本文件新增假设或结论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonNativeConfiguration

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderComparisonNativeRow (parameters_l environment_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "v" => SecondOrderQuotient.mk_l hℳ

structure configuration_l (K : source_coding_l hℳ) (p : parameters_l ℳ)
    (A : SecondOrderGraph.code_l ℳ) (B F r : type_l hℳ) (Q D R : SecondOrderModel.set_l ℳ) : Prop where
  ordinal : SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) (v A)
  presentation : SecondOrderOrdinalHierarchy.presentation_l A Q D R
  omega : v p.ω = K.omega
  zero : v p.e = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val
  coding : SecondOrderComparisonStageTotal.coding_l K (v p.t₁) (v p.t₂) (v p.t₃) (v p.Pair) (v p.Valid)
  indexMap : map_l (ℳ := 𝒱) (v p.J) (v p.I) (v A)
  indexInjective : injective_l (ℳ := 𝒱) (v p.J)
  indexOnto : ∀ a, mem_l hℳ a (v A) → ∃ i, mem_l hℳ i (v p.I) ∧ value_l (ℳ := 𝒱) (v p.J) i a
  indexSubset : subset_l (ℳ := 𝒱) (v p.I) K.omega
  indexReal : setRel_l K ⟨v p.I, indexSubset⟩ D
  indexRead : ∀ x y, value_l (ℳ := 𝒱) (v p.J) x y ↔ ∃ n,
    ∃ hn : SecondOrderModel.mem_l n D, x = (numberCode_l K n).val ∧
      y = v (SecondOrderRootCorrespondence.member_code_l hℳ A presentation n hn)
  hierarchy : PowerlessRelativeHierarchySemantics.history_l hℳ B (v A) F r
  layerMap : map_l (ℳ := 𝒱) (v p.T) (v p.I) r
  layerRead : ∀ i X, value_l (ℳ := 𝒱) (v p.T) i X ↔
    ∃ a, value_l (ℳ := 𝒱) (v p.J) i a ∧ value_l (ℳ := 𝒱) F a X

/-- 真实配置来自规范根与函数复合；任意原历史共享该静态参数。 -/
theorem exists_l (K : source_coding_l hℳ)
    {t₁ t₂ t₃ Pair Valid : type_l hℳ}
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
    (A : SecondOrderGraph.code_l ℳ)
    (hα : SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) (v A))
    {B F r : type_l hℳ} (hF : PowerlessRelativeHierarchySemantics.history_l hℳ B (v A) F r)
    (P₀ f C : type_l hℳ) :
    ∃ Q D R p, configuration_l K p A B F r Q D R ∧ v p.P₀ = P₀ ∧ v p.f = f ∧ v p.C = C ∧
      v p.Pair = Pair ∧ v p.Valid = Valid := by
  obtain ⟨Q, D, R, h⟩ := SecondOrderOrdinalHierarchy.presentation_exists_l hℳ A
  obtain ⟨I, hI⟩ := representative_exists_l K D
  obtain ⟨J, hJ, hOnto, hInject, hJRead⟩ := SecondOrderStageIndexFunction.exists_l K A h I hI
  have hFMap : map_l (ℳ := 𝒱) F (v A) r := hF.1
  obtain ⟨T, hT, hTRead⟩ := SecondOrderFunctionGraphComposition.exists_l
    (hℳ := hℳ) (F := J) (G := F) (A := I.val) (D := v A) (E := r) hJ hFMap
  obtain ⟨PairCode, hPair⟩ := SecondOrderQuotient.surj_l hℳ Pair
  obtain ⟨ValidCode, hValid⟩ := SecondOrderQuotient.surj_l hℳ Valid
  obtain ⟨ICode, hICode⟩ := SecondOrderQuotient.surj_l hℳ I.val
  obtain ⟨JCode, hJCode⟩ := SecondOrderQuotient.surj_l hℳ J
  obtain ⟨TCode, hTCode⟩ := SecondOrderQuotient.surj_l hℳ T
  obtain ⟨PCode, hPCode⟩ := SecondOrderQuotient.surj_l hℳ P₀
  obtain ⟨fCode, hfCode⟩ := SecondOrderQuotient.surj_l hℳ f
  obtain ⟨CCode, hCCode⟩ := SecondOrderQuotient.surj_l hℳ C
  let numeral (n : Nat) := SecondOrderNaturalGraph.code_l hℳ K.less K.less_spec
    (SecondOrderEvaluationRule.numeral_l ℳ n)
  let p : parameters_l ℳ := ⟨K.omega_graph,
    SecondOrderNaturalGraph.code_l hℳ K.less K.less_spec (SecondOrderModel.zero_l ℳ),
    numeral 1, numeral 2, numeral 3, PairCode, ValidCode, ICode, JCode, TCode, PCode, fCode, CCode⟩
  refine ⟨Q, D, R, p, ?_, hPCode, hfCode, hCCode, hPair, hValid⟩
  refine ⟨hα, h, K.omega_eq.symm, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hF, ?_, ?_⟩
  · have hOne := hCoding.one
    have hTwo := hCoding.two
    have hThree := hCoding.three
    have hNumeral n : v (numeral n) = PowerlessFormulaValidityReading.code_l K
        (SecondOrderEvaluationRule.numeral_l ℳ n) := rfl
    simpa only [p, hNumeral, hPair, hValid, hOne, hTwo, hThree] using hCoding
  · simpa only [p, hJCode, hICode] using hJ
  · simpa only [p, hJCode] using hInject
  · simpa only [p, hJCode, hICode] using hOnto
  · simpa only [p, hICode] using I.property
  · have hEqual : (⟨v p.I, by simpa only [p, hICode] using I.property⟩ :
        PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega) = I := Subtype.ext hICode
    rw [hEqual]
    exact hI
  · simpa only [p, hJCode] using hJRead
  · simpa only [p, hTCode, hICode] using hT
  · intro i X
    rw [show v p.T = T from hTCode, show v p.J = J from hJCode]
    exact hTRead i X

/-- 配置填满之后，原模型中有唯一递归历史，且全部切片满足实际原正文。 -/
theorem history_exists_l (K : source_coding_l hℳ) (p : parameters_l ℳ)
    {A : SecondOrderGraph.code_l ℳ} {B F r : type_l hℳ} {Q D R : SecondOrderModel.set_l ℳ}
    (h : configuration_l K p A B F r Q D R) :
    ∃! S, SecondOrderComparisonNativeRecursion.relation_l K p S S ∧ ∀ n W,
      SecondOrderSections.spec_l S n W ↔ SecondOrderComparisonNativeRow.formula_m.satisfies
        ((((environment_l K p).pushFree S).pushFree n).pushFree W) := by
  obtain ⟨S, hS, hOnly⟩ := SecondOrderComparisonNativeRecursion.exists_l K p h.omega h.zero
    A h.ordinal h.presentation h.indexMap h.indexSubset h.indexRead
  have hRows n := SecondOrderComparisonNativeRow.exists_unique_l K p h.omega h.zero h.coding
    h.ordinal h.indexMap h.indexInjective h.indexOnto h.indexSubset h.layerMap h.hierarchy h.layerRead S n
  exact ⟨S, ⟨hS, SecondOrderComparisonNativeRecursion.rows_l K p hS hRows⟩,
    fun X hX => hOnly X hX.1⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonNativeConfiguration
