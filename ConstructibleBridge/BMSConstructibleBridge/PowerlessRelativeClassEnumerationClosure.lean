import BMSConstructibleBridge.PowerlessRelativeClassEnumerationUnion
import BMSConstructibleBridge.PowerlessRelativeClassFunctionExtension
import BMSConstructibleBridge.PowerlessRelativeClassBasicClosure

/-! # 实际 Class 枚举的单集与有限添入闭包

单集及二元并由实际配对、并集回收进 Class；常值图和内部交错给出
实际满射。非空编号仅取自内部 ω 的归纳集公理，不抽取 Type 选择函数。
这些构造由具体字母表及常量种子的原 Z₂ 对象出口消费。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassEnumerationClosure

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒩" => structure_l hℳ B hBase

include hBase in
theorem singleton_l (t : type_l hℳ B) :
    ∃ T : type_l hℳ B, ∀ x : type_l hℳ B, mem_l hℳ x.val T.val ↔ x = t := by
  obtain ⟨T, hT⟩ := SecondOrderPairObjects.pair_exists_l hℳ t.val t.val
  refine ⟨⟨T, PowerlessRelativeClassPair.pair_l hℳ hBase t.property t.property hT⟩, ?_⟩
  intro x
  exact (hT x.val).trans ⟨fun h => Subtype.ext (h.elim id id),
    fun h => Or.inl (congrArg Subtype.val h)⟩

include hBase in
theorem union_l (X Y : type_l hℳ B) : ∃ W : type_l hℳ B,
    ∀ x : type_l hℳ B, mem_l hℳ x.val W.val ↔
      mem_l hℳ x.val X.val ∨ mem_l hℳ x.val Y.val := by
  obtain ⟨P, hP⟩ := SecondOrderPairObjects.pair_exists_l hℳ X.val Y.val
  have hUnion := SecondOrderUnion.models_l hℳ
  change ∀ P : SecondOrderQuotient.type_l hℳ, ∃ W, ∀ x,
    mem_l hℳ x W ↔ ∃ Y, mem_l hℳ Y P ∧ mem_l hℳ x Y at hUnion
  obtain ⟨W, hW⟩ := hUnion P
  refine ⟨⟨W, PowerlessRelativeClassBasicClosure.union_l hℳ hBase
    (PowerlessRelativeClassPair.pair_l hℳ hBase X.property Y.property hP) hW⟩, ?_⟩
  intro x
  apply (hW x.val).trans
  constructor
  · rintro ⟨Z, hZ, hx⟩
    rcases (hP Z).mp hZ with rfl | rfl
    · exact Or.inl hx
    · exact Or.inr hx
  · rintro (hx | hx)
    · exact ⟨X.val, (hP X.val).mpr (Or.inl rfl), hx⟩
    · exact ⟨Y.val, (hP Y.val).mpr (Or.inr rfl), hx⟩

theorem singleton_enumeration_l {ω : type_l hℳ B} (hω : omega_l (ℳ := 𝒩) ω)
    (t : type_l hℳ B) : ∃ T F : type_l hℳ B,
      (∀ x : type_l hℳ B, mem_l hℳ x.val T.val ↔ x = t) ∧
      map_l (ℳ := 𝒩) F ω T ∧ ∀ x : type_l hℳ B, mem_l hℳ x.val T.val →
        ∃ i : type_l hℳ B, mem_l hℳ i.val ω.val ∧ value_l (ℳ := 𝒩) F i x := by
  obtain ⟨T, hT⟩ := singleton_l (hBase := hBase) t
  obtain ⟨F, hF, hRead⟩ := PowerlessRelativeClassFunctionExtension.constant_l
    (hBase := hBase) ω T t ((hT t).mpr rfl)
  obtain ⟨i, _, hi⟩ := ((PowerlessNatural.inductive_iff_l (ℳ := 𝒩) ω).mp hω.1).1
  exact ⟨T, F, hT, hF, fun x hx =>
    ⟨i, hi, (hRead i x).mpr ⟨hi, (hT x).mp hx⟩⟩⟩

theorem adjoin_l {ω X G : type_l hℳ B} (hω : omega_l (ℳ := 𝒩) ω)
    (hG : map_l (ℳ := 𝒩) G ω X)
    (hOnto : ∀ x : type_l hℳ B, mem_l hℳ x.val X.val →
      ∃ i : type_l hℳ B, mem_l hℳ i.val ω.val ∧ value_l (ℳ := 𝒩) G i x)
    (t : type_l hℳ B) : ∃ Y F : type_l hℳ B,
      (∀ x : type_l hℳ B, mem_l hℳ x.val Y.val ↔ mem_l hℳ x.val X.val ∨ x = t) ∧
      map_l (ℳ := 𝒩) F ω Y ∧ ∀ x : type_l hℳ B, mem_l hℳ x.val Y.val →
        ∃ i : type_l hℳ B, mem_l hℳ i.val ω.val ∧ value_l (ℳ := 𝒩) F i x := by
  obtain ⟨T, J, hT, hJ, hJOnto⟩ := singleton_enumeration_l hω t
  obtain ⟨Y, hY⟩ := union_l (hBase := hBase) X T
  obtain ⟨F, hF, hFOnto⟩ := PowerlessRelativeClassEnumerationUnion.exists_l
    hω hG hJ hOnto hJOnto hY
  exact ⟨Y, F, fun x => (hY x).trans (or_congr Iff.rfl (hT x)), hF, hFOnto⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassEnumerationClosure
