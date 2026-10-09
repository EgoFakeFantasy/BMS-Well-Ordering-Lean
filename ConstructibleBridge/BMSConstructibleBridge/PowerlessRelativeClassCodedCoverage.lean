import BMSConstructibleBridge.PowerlessRelativeClassHistory
import BMSConstructibleBridge.PowerlessRelativeClassCoverageAbsolute
import BMSConstructibleBridge.PowerlessRelativeCofinalLegacyNumericReading
import BMSConstructibleBridge.PowerlessRelativeLimitOperationClosure

/-! # 任意 Class 对象的同一完整局部编码覆盖包

不假定首不可数 Ω 或集合源 W。x 的实际相对层见证决定前史阶段；其
严格后继及有限参数进入新构造的共尾母层。原完整 Sat 和原 Def 图共用
同一编码包，预算归纳产生实际 Class 前史，原层唯一性识别覆盖 x 的值。

十七个实际 Class 见证满足原覆盖矩阵，不把 raw 存在性冒充 Class 存在。
仍须反射到同一虚拟域并沿同一 project 传到 T；这里不是弱凝聚或终局。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCodedCoverage

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ z, mem_l hℳ z B → ∀ t, mem_l hℳ t z → mem_l hℳ t B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => structure_l hℳ B hBase
local notation "Raw" => SecondOrderQuotient.type_l hℳ

/-- 保留实际构造的编码与原前史，供同一 Class 比较图继续消费。 -/
theorem witnesses_l (K : source_coding_l hℳ) (ω x : type_l hℳ B)
    (hω : SecondOrderOmega.omega_l hℳ ω.val) :
    ∃ C : SecondOrderModel.set_l ℳ,
    ∃ a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G : type_l hℳ B,
      PowerlessCodedHistoryCoverageSyntax.point_l (𝒩 := 𝒩₀)
        ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩
        ω x a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G ∧
      PowerlessRelativeCofinalDefCoding.spec_l (W := U.val)
        hBase K ω e t₁ t₂ t₃ P N F Q G C ∧
      SetTheory.Structure.IsOrdinal
        (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) A.val ∧
      PowerlessRelativeHierarchySemantics.history_l hℳ B A.val f.val U.val := by
  obtain ⟨a, c, hc, hxc⟩ := x.property
  obtain ⟨A, c₁, hSucc, hC₁, _hDef⟩ := PowerlessRelativeLevelClosure.successor_exists_l hℳ hBase hc
  have hA := PowerlessRelativeLevelClosure.ordinal_l hℳ hC₁
  have haA : mem_l hℳ a A := (hSucc a).mpr (Or.inr rfl)
  let a₀ : type_l hℳ B := ⟨a, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (PowerlessRelativeLevelClosure.ordinal_l hℳ hc)⟩
  let A₀ : type_l hℳ B := ⟨A, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase hA⟩
  let B₀ : type_l hℳ B := ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩
  let η : Env 𝒩₀ [] [.set, .set] := Env.empty |>.pushFree ω |>.pushFree B₀
  obtain ⟨β, U, hAβ, hLimit, hCofinal, hU, _hxU, hParams⟩ :=
    PowerlessRelativeClassCofinalParameterBounds.exists_l η x A hA
  have hBU : mem_l hℳ B U := hParams .set .here
  have hωU : mem_l hℳ ω.val U := hParams .set (.there .here)
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  let U₀ : type_l hℳ B := ⟨U, PowerlessRelativeLevelClosure.class_l hℳ hBase hU⟩
  obtain ⟨e, t₁, t₂, t₃, P, N, F, Q, G, C, hCoding⟩ :=
    PowerlessRelativeCofinalDefCoding.exists_l hBase K hLimit hU hCofinal ω hωU hωEq
  obtain ⟨t₄, V, _ht₄U, _hVU, hNumericRaw⟩ :=
    PowerlessRelativeCofinalLegacyNumericReading.exists_l hBase K hLimit hU hωU hCoding
  obtain ⟨D, hD, hRead⟩ := PowerlessRelativeCofinalDefFunction.exists_for_reading_l
    hBase K hLimit hU hCofinal (hωEq ▸ hωU) ω e N Q G
    (fun z hz r => PowerlessMemberDefImageBoundedReading.checkeriff_l hBase K hLimit hU hωU hCoding hz)
  have hβ := PowerlessRelativeLevelClosure.ordinal_l hℳ hU
  obtain ⟨f, hf⟩ := PowerlessRelativeCutoffClassHistory.class_exists_l hℳ K hBase D hRead hA hU
    (fun z hz => hβ.transitive A hAβ z hz)
  have hLight := PowerlessHierarchyLightHistoryUnique.from_original_l hℳ hRead (fun _ hz => hz) hf
  obtain ⟨y, ⟨hyU, hy⟩, _hUnique⟩ := hf.1.2 a haA
  have hyLevel : PowerlessRelativeHierarchySemantics.level_l hℳ B a y := ⟨A, f.val, U, hA, haA, hf, hy⟩
  have hxy : mem_l hℳ x.val y := (PowerlessRelativeHierarchyAgreement.level_unique_l hℳ hc hyLevel) ▸ hxc
  let y₀ : type_l hℳ B := ⟨y, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase U₀.property hyU⟩
  have hSat := PowerlessRelativeClassFunctionSpecifications.satisfaction_l (hBase := hBase)
    ω e t₁ t₂ t₃ P N F U₀ G hCoding.sat_map hCoding.sat_read
  have hDefRead (z r : Raw) : value_l (ℳ := 𝒱) D.val z r ↔ mem_l hℳ z U ∧ mem_l hℳ r U ∧
      PowerlessMemberDefImageBounded.holds_l (𝒩 := 𝒱) ω.val e.val N.val Q.val U G.val z r := by
    constructor
    · intro hz
      obtain ⟨hzU, hDef⟩ := (hRead z r).mp hz
      exact ⟨hzU, (SecondOrderFunctionProperties.value_mem_l hℳ hD hz).2,
        (PowerlessMemberDefImageBoundedReading.checkeriff_l hBase K hLimit hU hωU hCoding hzU).mpr hDef⟩
    · rintro ⟨hzU, _hrU, hCheck⟩
      exact (hRead z r).mpr ⟨hzU,
        (PowerlessMemberDefImageBoundedReading.checkeriff_l hBase K hLimit hU hωU hCoding hzU).mp hCheck⟩
  have hDef := PowerlessRelativeClassFunctionSpecifications.def_l (hBase := hBase)
    ω e N Q U₀ G D hD hDefRead
  have hNumeric := (PowerlessRelativeClassCoverageAbsolute.numeric_l (hBase := hBase)
    ω e t₁ t₂ t₃ t₄ P N V Q).mpr hNumericRaw
  have hAClass := PowerlessRelativeClassCoverageAbsolute.ordinal_l (hBase := hBase) A₀ hA
  have hLightClass := (PowerlessRelativeClassCoverageAbsolute.history_l (hBase := hBase) B₀ D A₀ U₀ f).mpr
    ((PowerlessHierarchyLightHistory.reading_l hℳ).mpr hLight)
  have hFinite := PowerlessRelativeClassFunctionSpecifications.coverage_l (hBase := hBase) ω U₀ hCoding.coverage
  have hTrans : PowerlessNaturalOrder.transitive_l (ℳ := 𝒩₀) U₀ :=
    fun z t hz ht => PowerlessRelativeLevelClosure.transitive_l hℳ hBase hU z.val hz t.val ht
  have hClosed := PowerlessRelativeClassCoverageAbsolute.closed_l (hBase := hBase) U₀
    (PowerlessRelativeLimitOperationClosure.closed_l hℳ hBase hLimit hU)
  exact ⟨C, a₀, y₀, A₀, U₀, D, f, e, t₁, t₂, t₃, t₄, P, N, F, V, Q, G,
    ⟨haA, (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) f a₀ y₀).mpr hy,
      hxy, hBU, hωU, hCoding.static, hSat, hDef, hNumeric, hAClass, hLightClass,
      hFinite, hTrans, hClosed⟩, hCoding, hA, hf⟩

/-- 原十七见证接口不变；额外构造证书只在证明内遗忘。 -/
theorem exists_l (K : source_coding_l hℳ) (ω x : type_l hℳ B)
    (hω : SecondOrderOmega.omega_l hℳ ω.val) :
    PowerlessCodedHistoryCoverageSyntax.statement_l (𝒩 := 𝒩₀)
      ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ ω x := by
  obtain ⟨_C, a, y, A, U, D, f, e, t₁, t₂, t₃, t₄, P, N, F, V, Q, G,
    hPoint, _hCoding, _hA, _hHistory⟩ := witnesses_l (hBase := hBase) K ω x hω
  exact ⟨a, y, A, U, D, f, e, t₁, t₂, t₃, t₄, P, N, F, V, Q, G, hPoint⟩

#print axioms witnesses_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCodedCoverage
