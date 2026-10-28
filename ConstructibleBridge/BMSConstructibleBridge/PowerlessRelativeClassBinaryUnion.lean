import BMSConstructibleBridge.PowerlessRelativeClassEnumerationUnion
import BMSConstructibleBridge.PowerlessRelativeClassBasicAxioms

/-! # 实际类内二元并及其枚举接口

先构造无序对再取并集，保留精确成员关系，供有限多个可数包络组合。
集合存在和满射图都是类内见证，不使用任意可数族的收集。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassBinaryUnion

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

include hBase in
theorem exists_l (U V : type_l hℳ B) : ∃ W : type_l hℳ B, ∀ x : type_l hℳ B,
    mem_l hℳ x.val W.val ↔ mem_l hℳ x.val U.val ∨ mem_l hℳ x.val V.val := by
  obtain ⟨P, hP⟩ := SecondOrderPairObjects.pair_exists_l hℳ U.val V.val
  let P' : type_l hℳ B := ⟨P, PowerlessRelativeClassPair.pair_l hℳ hBase U.property V.property hP⟩
  have hPair := (PowerlessRelativeClassFunctionAbsolute.pair_l (hBase := hBase) U V P').mpr hP
  have hUnion := PowerlessRelativeClassBasicAxioms.union_l hℳ B hBase
  change ∀ A : type_l hℳ B, ∃ W : type_l hℳ B, ∀ x : type_l hℳ B,
    mem_l hℳ x.val W.val ↔ ∃ y : type_l hℳ B, mem_l hℳ y.val A.val ∧ mem_l hℳ x.val y.val at hUnion
  obtain ⟨W, hW⟩ := hUnion P'
  refine ⟨W, fun x => (hW x).trans ⟨?_, ?_⟩⟩
  · rintro ⟨y, hy, hxy⟩
    exact ((hPair y).mp hy).elim (fun h => Or.inl (h ▸ hxy)) (fun h => Or.inr (h ▸ hxy))
  · rintro (hx | hx)
    · exact ⟨U, (hPair U).mpr (Or.inl rfl), hx⟩
    · exact ⟨V, (hPair V).mpr (Or.inr rfl), hx⟩

theorem enumeration_l {ω U V G H : type_l hℳ B}
    (hω : omega_l (ℳ := structure_l hℳ B hBase) ω)
    (hG : map_l (ℳ := structure_l hℳ B hBase) G ω U)
    (hH : map_l (ℳ := structure_l hℳ B hBase) H ω V)
    (hGOnto : ∀ y : type_l hℳ B, mem_l hℳ y.val U.val → ∃ i : type_l hℳ B,
      mem_l hℳ i.val ω.val ∧ value_l (ℳ := structure_l hℳ B hBase) G i y)
    (hHOnto : ∀ y : type_l hℳ B, mem_l hℳ y.val V.val → ∃ i : type_l hℳ B,
      mem_l hℳ i.val ω.val ∧ value_l (ℳ := structure_l hℳ B hBase) H i y) :
    ∃ W : type_l hℳ B,
      (∀ x : type_l hℳ B, mem_l hℳ x.val W.val ↔ mem_l hℳ x.val U.val ∨ mem_l hℳ x.val V.val) ∧
      ∃ F : type_l hℳ B, map_l (ℳ := structure_l hℳ B hBase) F ω W ∧
        ∀ y : type_l hℳ B, mem_l hℳ y.val W.val → ∃ i : type_l hℳ B,
          mem_l hℳ i.val ω.val ∧ value_l (ℳ := structure_l hℳ B hBase) F i y := by
  obtain ⟨W, hW⟩ := exists_l (hBase := hBase) U V
  obtain ⟨F, hF, hOnto⟩ := PowerlessRelativeClassEnumerationUnion.exists_l hω hG hH hGOnto hHOnto hW
  exact ⟨W, hW, F, hF, hOnto⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassBinaryUnion
