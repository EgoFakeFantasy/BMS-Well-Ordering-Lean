import BMSConstructibleBridge.PowerlessRelativeClassBoundedTotalization
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramBasicOperator
import BMSConstructibleBridge.PowerlessRelativeLimitSatisfactionRowOperator

/-! # 同一实际层的四张合法程序调用图

原 Z₂ 背景，纯 Δ₀ 正文。两种基础操作及原较短历史分别有界总化，
与同一 Sat 行图一起给出四张真实 Class 图，均映射 W→W。历史图只要求
属于 Class、原输出在 W，不要求历史图属于 W；原合法输出严格保留。

四图存在及其全 raw 保持性是程序像装配的中间接口。标签、可数种子及
同一个实际程序像还须构造；本文件不预供基础操作闭包或层成员覆盖。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCofinalProgramGraphs

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ

/-- 部分历史的同一实际值进入 W→W 总图，域外缺省不改变有效读数。 -/
theorem history_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    {α : Raw} (W e H : type_l hℳ B) (he : mem_l hℳ e.val W.val)
    (hH : map_l (ℳ := 𝒱) H.val α W.val) :
    ∃ J : type_l hℳ B, map_l (ℳ := 𝒱) J.val W.val W.val ∧
      ∀ a A : Raw, mem_l hℳ a W.val → value_l (ℳ := 𝒱) H.val a A → value_l (ℳ := 𝒱) J.val a A := by
  let η : Env (structure_l hℳ B hBase) [] [.set, .set, .set] :=
    Env.empty (M := structure_l hℳ B hBase) |>.pushFree W |>.pushFree e |>.pushFree H
  let X : Term ℒ [] [.set, .set, .set] .set := .fvar (.there (.there .here))
  let E : Term ℒ [] [.set, .set, .set] .set := .fvar (.there .here)
  let T : Term ℒ [] [.set, .set, .set] .set := .fvar .here
  let φ := PowerlessRelativeFiniteProgramGraphOperator.relation_m T
  have hUnique (x y z : Raw) (_hx : mem_l hℳ x W.val)
      (_hy : mem_l hℳ y W.val) (_hz : mem_l hℳ z W.val)
      (hxy : φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree x).pushFree y))
      (hxz : φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree x).pushFree z)) : y = z :=
    SecondOrderFunctionProperties.value_unique_l hℳ hH
      ((PowerlessRelativeFiniteProgramGraphOperator.relation_formula_l T
        (PowerlessRelativeClassRelativization.env_l η) x y).mp hxy)
      ((PowerlessRelativeFiniteProgramGraphOperator.relation_formula_l T
        (PowerlessRelativeClassRelativization.env_l η) x z).mp hxz)
  obtain ⟨J, hJ, hRead⟩ := PowerlessRelativeClassBoundedTotalization.exists_l
    (PowerlessRelativeFiniteProgramGraphOperator.delta_l T) η X E he hUnique
  refine ⟨J, hJ, fun a A ha hA => (hRead a A).mpr ⟨ha,
    (SecondOrderFunctionProperties.value_mem_l hℳ hH hA).2, Or.inl ?_⟩⟩
  exact (PowerlessRelativeFiniteProgramGraphOperator.relation_formula_l T
    (PowerlessRelativeClassRelativization.env_l η) a A).mpr hA

/-- 两种实际基础输出均进入真正 Class 调用图，而非仅给任意输出单值性。 -/
theorem operation_l (b : Bool)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    {β : Raw} (W e : type_l hℳ B)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B β W.val) (he : mem_l hℳ e.val W.val) :
    ∃ J : type_l hℳ B, map_l (ℳ := 𝒱) J.val W.val W.val ∧ ∀ s Z : Raw,
      mem_l hℳ s W.val → PowerlessRelativeFiniteProgramBasicOperator.call_l (𝒩 := 𝒱) b W.val s Z →
        value_l (ℳ := 𝒱) J.val s Z := by
  let η : Env (structure_l hℳ B hBase) [] [.set, .set] :=
    Env.empty (M := structure_l hℳ B hBase) |>.pushFree W |>.pushFree e
  let X : Term ℒ [] [.set, .set] .set := .fvar (.there .here)
  let E : Term ℒ [] [.set, .set] .set := .fvar .here
  let φ := PowerlessRelativeFiniteProgramBasicOperator.relation_m b X
  have hUnique (x y z : Raw) (_hx : mem_l hℳ x W.val)
      (_hy : mem_l hℳ y W.val) (_hz : mem_l hℳ z W.val)
      (hxy : φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree x).pushFree y))
      (hxz : φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree x).pushFree z)) : y = z :=
    PowerlessRelativeFiniteProgramBasicOperator.unique_l b
      ((PowerlessRelativeFiniteProgramBasicOperator.relation_formula_l b X
        (PowerlessRelativeClassRelativization.env_l η) x y).mp hxy)
      ((PowerlessRelativeFiniteProgramBasicOperator.relation_formula_l b X
        (PowerlessRelativeClassRelativization.env_l η) x z).mp hxz)
  obtain ⟨J, hJ, hRead⟩ := PowerlessRelativeClassBoundedTotalization.exists_l
    (PowerlessRelativeFiniteProgramBasicOperator.delta_l b X) η X E he hUnique
  refine ⟨J, hJ, fun s Z hs hZ => (hRead s Z).mpr ⟨hs,
    PowerlessRelativeFiniteProgramBasicOperator.member_l b hBase hLimit hW hZ, Or.inl ?_⟩⟩
  exact (PowerlessRelativeFiniteProgramBasicOperator.relation_formula_l b X
    (PowerlessRelativeClassRelativization.env_l η) s Z).mpr hZ

/-- 四图在同一 W 上联合构造，原历史、Sat 包及有效输出都保持不变。 -/
theorem exists_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (K : source_coding_l hℳ) {α β W : Raw}
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B β W)
    (H ω e t₁ t₂ t₃ Pair N Valid Translation G : type_l hℳ B)
    {L : SecondOrderModel.set_l ℳ}
    (hCode : PowerlessRelativeCofinalDefCoding.spec_l (W := W)
      hBase K ω e t₁ t₂ t₃ Pair N Valid Translation G L)
    (hωW : mem_l hℳ ω.val W)
    (hHistory : PowerlessRelativeHierarchySemantics.history_l hℳ B α H.val W) :
    ∃ P U J F : type_l hℳ B,
      map_l (ℳ := 𝒱) P.val W W ∧ map_l (ℳ := 𝒱) U.val W W ∧
      map_l (ℳ := 𝒱) J.val W W ∧ map_l (ℳ := 𝒱) F.val W W ∧
      (∀ s Z : Raw, mem_l hℳ s W →
        PowerlessRelativeFiniteProgramBasicOperator.call_l (𝒩 := 𝒱) true W s Z → value_l (ℳ := 𝒱) P.val s Z) ∧
      (∀ s Z : Raw, mem_l hℳ s W →
        PowerlessRelativeFiniteProgramBasicOperator.call_l (𝒩 := 𝒱) false W s Z → value_l (ℳ := 𝒱) U.val s Z) ∧
      (∀ a A : Raw, mem_l hℳ a W → value_l (ℳ := 𝒱) H.val a A → value_l (ℳ := 𝒱) J.val a A) ∧
      (∀ s Z : Raw, value_l (ℳ := 𝒱) F.val s Z ↔ mem_l hℳ s W ∧ mem_l hℳ Z W ∧
        PowerlessRelativeLimitSatisfactionRowOperator.total_l (𝒩 := 𝒱) ω.val W G.val e.val s Z) := by
  let C : type_l hℳ B := ⟨W, PowerlessRelativeLevelClosure.class_l hℳ hBase hW⟩
  obtain ⟨P, hP, hPair⟩ := operation_l true hBase C e hLimit hW hCode.e_mem
  obtain ⟨U, hU, hUnion⟩ := operation_l false hBase C e hLimit hW hCode.e_mem
  have hH : map_l (ℳ := 𝒱) H.val α C.val := hHistory.1
  obtain ⟨J, hJ, hJRead⟩ := history_l hBase (α := α) C e H hCode.e_mem hH
  obtain ⟨F, hF, hFRead⟩ := PowerlessRelativeLimitSatisfactionRowOperator.of_coding_l
    hBase K hLimit hW ω e t₁ t₂ t₃ Pair N Valid Translation G hCode hωW
  exact ⟨P, U, J, F, hP, hU, hJ, hF, hPair, hUnion, hJRead, hFRead⟩

#print axioms history_l
#print axioms operation_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCofinalProgramGraphs
