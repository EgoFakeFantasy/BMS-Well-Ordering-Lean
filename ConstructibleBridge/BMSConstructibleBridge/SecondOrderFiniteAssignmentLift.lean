import BMSConstructibleBridge.SecondOrderFiniteAssignmentGraph
import BMSConstructibleBridge.SecondOrderFunctionGraphComposition
import BMSConstructibleBridge.PowerlessRelativeClassFiniteMapLift

/-! # 数值赋值沿实际母集枚举提升为类内赋值

枚举 U 只须是原商中的实际 ω→A 映射，不要求其图属于类。先在原商
复合有限数图，再将最终有限图提升入类。精确读数覆盖全部内部数和
所有类内输出；本模块是全内部 Sat 求值保持的中间接口。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteAssignmentLift

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open SecondOrderSequenceSyntax (read_l)
open SecondOrderAssignmentSyntax (valid_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem exists_ambient_l (K : source_coding_l hℳ) {E : SecondOrderModel.set_l ℳ}
    {c l : SecondOrderModel.num_l ℳ} (hc : valid_l E c l)
    {U A : SecondOrderQuotient.type_l hℳ}
    (hU : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) U K.omega A) :
    ∃ F : SecondOrderQuotient.type_l hℳ,
      map_l (ℳ := SecondOrderQuotient.structure_l hℳ) F (numberCode_l K l).val A ∧
      ∀ i : SecondOrderModel.num_l ℳ, ∀ y : SecondOrderQuotient.type_l hℳ,
        value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F (numberCode_l K i).val y ↔
          ∃ j, read_l E c i j ∧ value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U (numberCode_l K j).val y := by
  obtain ⟨G, hG, hNumber⟩ := SecondOrderFiniteAssignmentGraph.exists_l K hc
  obtain ⟨F, hF, hRead⟩ := SecondOrderFunctionGraphComposition.exists_l
    (F := G) (A := (numberCode_l K l).val) (D := K.omega) (E := A) hG hU
  refine ⟨F, hF, fun i y => (hRead _ y).trans ?_⟩
  constructor
  · rintro ⟨z, hiz, hzy⟩
    obtain ⟨j, hij, hz⟩ := (hNumber i z).mp hiz
    exact ⟨j, hij, hz ▸ hzy⟩
  · rintro ⟨j, hij, hjy⟩
    exact ⟨(numberCode_l K j).val, (hNumber i _).mpr ⟨j, hij, rfl⟩, hjy⟩

variable {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "ClassModel" => structure_l hℳ B hBase

/-- 显式 ω 对应下的类内数对象，不抽取自然数或模型的全局选择。 -/
def number_l (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (K : source_coding_l hℳ) (ω : type_l hℳ B) (hωEq : ω.val = K.omega)
    (i : SecondOrderModel.num_l ℳ) : type_l hℳ B :=
  ⟨(numberCode_l K i).val, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property
    (hωEq.symm ▸ (numberCode_l K i).property)⟩

theorem exists_l (K : source_coding_l hℳ) {ω A : type_l hℳ B}
    (hω : omega_l (ℳ := ClassModel) ω) (hωEq : ω.val = K.omega)
    {E : SecondOrderModel.set_l ℳ} {c l : SecondOrderModel.num_l ℳ} (hc : valid_l E c l)
    {U : SecondOrderQuotient.type_l hℳ}
    (hU : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) U K.omega A.val) :
    ∃ F : type_l hℳ B, map_l (ℳ := ClassModel) F (number_l hBase K ω hωEq l) A ∧
      ∀ i : SecondOrderModel.num_l ℳ, ∀ y : type_l hℳ B,
        value_l (ℳ := ClassModel) F (number_l hBase K ω hωEq i) y ↔
          ∃ j, read_l E c i j ∧ value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U (numberCode_l K j).val y.val := by
  obtain ⟨F, hF, hRead⟩ := exists_ambient_l K hc hU
  have hFClass := PowerlessRelativeClassFiniteMapLift.member_l hBase ω.property A.property
    ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mp hω)
    (hωEq.symm ▸ (numberCode_l K l).property) hF
  let F' : type_l hℳ B := ⟨F, hFClass⟩
  refine ⟨F', (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase)
    F' (number_l hBase K ω hωEq l) A).mpr hF, ?_⟩
  intro i y
  exact (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase)
    F' (number_l hBase K ω hωEq i) y).trans (hRead i y.val)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteAssignmentLift
