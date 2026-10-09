import BMSConstructibleBridge.PowerlessHereditaryMultiplicationAbsolute
import BMSConstructibleBridge.PowerlessBMSNonemptyTransfer

/-! # 实际遗传域的算术对应及逐候选源证书

数域沿既有原商数码双射对应，任意实际遗传域运算证书都满足已证的
算术值绝对性。源模型及运算的存在性只在 Prop 中消去；不导出
选择源模型的 Type 函数。完整源理论在此仍是显式前提，须由实际
遗传核心构造提供，不能把本模块当作无条件的 Z₂ 良序证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryArithmeticCandidate

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessBMSQuotientArithmetic (numberEquiv_numberCode_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessHereditaryStructure.type_l PowerlessHereditaryStructure.structure_l
  PowerlessArithmetic.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒩₁" => PowerlessHereditaryStructure.structure_l hℳ B hBase
local notation "HType" => PowerlessHereditaryStructure.type_l hℳ B

def real_relation_l (K : source_coding_l hℳ) {ω : HType}
    (A : PowerlessArithmetic.set_l (ℳ := 𝒩₁) ω) (X : ℳ.Carrier .set) : Prop :=
  ∀ n, mem_l hℳ (numberCode_l K n).val A.val.val ↔ SecondOrderModel.mem_l n X

theorem correspondence_exists_l (K : source_coding_l hℳ) {ω e : HType}
    (hω : ω.val = K.omega) (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hz : PowerlessNatural.zero_l (ℳ := 𝒩₁) e) (h₀ : member_l 𝒩₁ e ω)
    (F : PowerlessArithmetic.operations_l (ℳ := 𝒩₁) ω e) :
    ∃ C : SecondOrderPureTransfer.correspondence_l
      (M := PowerlessArithmetic.structure_l hz h₀ F) (N := ℳ),
      ∀ A X, C.setRel_l A X ↔ real_relation_l K A X := by
  let read : PowerlessArithmetic.num_l (ℳ := 𝒩₁) ω →
      PowerlessArithmetic.num_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega :=
    fun a => ⟨a.val.val, hω ▸ a.property⟩
  let write : SecondOrderModel.num_l ℳ → PowerlessArithmetic.num_l (ℳ := 𝒩₁) ω :=
    fun n => ⟨⟨(numberCode_l K n).val, PowerlessHereditaryClass.transitive_l hℳ
      ω.property (hω.symm ▸ (numberCode_l K n).property)⟩,
      by
        change mem_l hℳ (numberCode_l K n).val ω.val
        rw [hω]
        exact (numberCode_l K n).property⟩
  have hReadWrite n : read (write n) = numberCode_l K n := Subtype.ext rfl
  have hWriteRead a : write (numberEquiv_l K (read a)) = a := by
    apply Subtype.ext
    apply Subtype.ext
    change (numberCode_l K (numberEquiv_l K (read a))).val = a.val.val
    have hInv : numberCode_l K (numberEquiv_l K (read a)) = read a :=
      Equiv.symm_apply_apply (numberEquiv_l K) (read a)
    exact congrArg Subtype.val hInv
  let E : PowerlessArithmetic.num_l (ℳ := 𝒩₁) ω ≃ SecondOrderModel.num_l ℳ :=
    { toFun := fun a => numberEquiv_l K (read a)
      invFun := write
      left_inv := hWriteRead
      right_inv := fun n => by
        change numberEquiv_l K (read (write n)) = n
        rw [hReadWrite]
        exact numberEquiv_numberCode_l K n }
  have hCode a : (numberCode_l K (E a)).val = a.val.val :=
    congrArg Subtype.val (Equiv.symm_apply_apply (numberEquiv_l K) (read a))
  let C : SecondOrderPureTransfer.correspondence_l
      (M := PowerlessArithmetic.structure_l hz h₀ F) (N := ℳ) :=
    { numberEquiv_l := E
      setRel_l := real_relation_l K
      zero_l := by
        change E ⟨e, h₀⟩ = SecondOrderModel.zero_l ℳ
        apply numberCode_injective_l K
        apply Subtype.ext
        exact (hCode ⟨e, h₀⟩).trans he
      succ_l := fun a => by
        change E (F.succ_l a) = SecondOrderModel.succ_l (E a)
        have hSucc := (PowerlessHereditaryOmegaAbsolute.successor_l
          a.val (F.succ_l a).val).mp (F.succ_graph_l a)
        have hSucc' : PowerlessNatural.successor_l (ℳ := SecondOrderQuotient.structure_l hℳ)
            a.val.val (F.succ_l a).val.val := fun z => hSucc z
        have hExpected := PowerlessBMSQuotientSuccessor.successor_l K (E a)
        rw [hCode a] at hExpected
        apply numberCode_injective_l K
        apply Subtype.ext
        exact (hCode (F.succ_l a)).trans
          (PowerlessBMSQuotientRecursion.successor_unique_l (hM := hℳ) hSucc' hExpected)
      add_l := fun a b => by
        change E (F.add_l a b) = SecondOrderModel.add_l (E a) (E b)
        have hAdd := (PowerlessHereditaryAdditionAbsolute.instance_l K hω he
          (hCode a).symm (hCode b).symm).mp (F.add_graph_l a b)
        apply numberCode_injective_l K
        exact Subtype.ext ((hCode (F.add_l a b)).trans hAdd)
      mul_l := fun a b => by
        change E (F.mul_l a b) = SecondOrderModel.mul_l (E a) (E b)
        have hMul := PowerlessHereditaryMultiplicationAbsolute.instance_l K hω he
          (hCode a).symm (hCode b).symm (F.mul_graph_l a b)
        apply numberCode_injective_l K
        exact Subtype.ext ((hCode (F.mul_l a b)).trans hMul)
      member_iff_l := fun a A X hA => by
        change mem_l hℳ a.val.val A.val.val ↔ SecondOrderModel.mem_l (E a) X
        have h := hA (E a)
        rw [hCode a] at h
        exact h }
  exact ⟨C, fun _ _ => Iff.rfl⟩

/-- 只有实际完整源模型已建立后，才打包旧的逐候选接口。 -/
theorem candidate_l (K : source_coding_l hℳ)
    (hSource : Theory.Models 𝒩₁ PowerlessTheory.theory_m) {ω e : HType}
    (hω : ω.val = K.omega) (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (X : ℳ.Carrier .set) (A : PowerlessArithmetic.set_l (ℳ := 𝒩₁) ω)
    (hA : real_relation_l K A X) :
    Nonempty (PowerlessBMSMatrixTransfer.candidate_source_l.{u, u} (M := ℳ) X) := by
  have hz : PowerlessNatural.zero_l (ℳ := 𝒩₁) e := by
    apply (PowerlessHereditaryOmegaAbsolute.empty_l e).mpr
    intro z hz
    rw [he] at hz
    exact PowerlessBMSQuotientSuccessor.zero_l K z hz
  have h₀ : member_l 𝒩₁ e ω := by
    change mem_l hℳ e.val ω.val
    rw [hω, he]
    exact (numberCode_l K (SecondOrderModel.zero_l ℳ)).property
  have hωSource : omega_l (ℳ := 𝒩₁) ω :=
    (PowerlessHereditaryOmegaAbsolute.omega_l (hBase := hBase) ω).mpr (hω.symm ▸ K.omega_spec)
  obtain ⟨F⟩ := PowerlessArithmetic.operations_exists_l hSource hωSource hz
  obtain ⟨C, hC⟩ := correspondence_exists_l K hω he hz h₀ F
  exact ⟨{ source := 𝒩₁
           sourceOmega := ω
           sourceZero := e
           sourceZeroSpec := hz
           sourceZeroMem := h₀
           sourceOperations := F
           sourceModels := hSource
           sourceOmegaSpec := hωSource
           arithmeticCorrespondence := C
           representative := A
           representativeRelated := (hC A X).mpr hA }⟩

#print axioms correspondence_exists_l
#print axioms candidate_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryArithmeticCandidate
