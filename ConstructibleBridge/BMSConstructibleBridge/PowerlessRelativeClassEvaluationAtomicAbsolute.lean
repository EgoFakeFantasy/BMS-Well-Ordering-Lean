import BMSConstructibleBridge.PowerlessRelativeClassFunctionProperties
import BMSConstructibleBridge.PowerlessEvaluationClause

/-! # 有限类内赋值的两个原子求值绝对性

见证由函数陪域的实际成员资格提升到类内。类内有序对与求值的既有
绝对性接回环境商，不使用宿主选择函数或完整无幂集理论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassEvaluationAtomicAbsolute

open Logic FirstOrder ThirdOrderSemantics
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
    ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B}

theorem equality_l {f L A i j : type_l hℳ B}
    (hMap : map_l (ℳ := structure_l hℳ B hBase) f L A) :
    PowerlessEvaluationClause.equal_l (ℳ := structure_l hℳ B hBase) f i j ↔
      PowerlessEvaluationClause.equal_l (ℳ := SecondOrderQuotient.structure_l hℳ) f.val i.val j.val := by
  constructor
  · rintro ⟨x, hx, hy⟩
    exact ⟨x.val, (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) f i x).mp hx,
      (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) f j x).mp hy⟩
  · rintro ⟨x, hx, hy⟩
    have hMapRaw := (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) f L A).mp hMap
    have hxA := (SecondOrderFunctionProperties.value_mem_l hℳ hMapRaw hx).2
    let x' : type_l hℳ B := ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase A.property hxA⟩
    exact ⟨x', (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) f i x').mpr hx,
      (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) f j x').mpr hy⟩

theorem membership_l {f L A i j : type_l hℳ B}
    (hMap : map_l (ℳ := structure_l hℳ B hBase) f L A) :
    PowerlessEvaluationClause.member_l (ℳ := structure_l hℳ B hBase) f i j ↔
      PowerlessEvaluationClause.member_l (ℳ := SecondOrderQuotient.structure_l hℳ) f.val i.val j.val := by
  constructor
  · rintro ⟨x, y, hx, hy, hxy⟩
    exact ⟨x.val, y.val,
      (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) f i x).mp hx,
      (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) f j y).mp hy, hxy⟩
  · rintro ⟨x, y, hx, hy, hxy⟩
    have hMapRaw := (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) f L A).mp hMap
    have hxA := (SecondOrderFunctionProperties.value_mem_l hℳ hMapRaw hx).2
    have hyA := (SecondOrderFunctionProperties.value_mem_l hℳ hMapRaw hy).2
    let x' : type_l hℳ B := ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase A.property hxA⟩
    let y' : type_l hℳ B := ⟨y, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase A.property hyA⟩
    exact ⟨x', y', (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) f i x').mpr hx,
      (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) f j y').mpr hy, hxy⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassEvaluationAtomicAbsolute
