import BMSConstructibleBridge.SecondOrderCanonicalHereditaryWitness
import BMSConstructibleBridge.SecondOrderRootedRealFamilyNormalization
import BMSConstructibleBridge.SecondOrderCodedFamilyCollection

/-! # 遗传见证的环境商收集

实际请求的逐数遗传见证先规范实数化，再统一归零并收集整行对象。
所有见证都来自同一张原模型实数；没有使用可数选择。输出 C 暂时
只有环境商成员性，尚未证明 C 或统一族实数进入相对构造内域。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalHereditaryCollection

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l mk_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

private theorem all_indices_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    ∃ I : SecondOrderModel.set_l ℳ, ∀ n, SecondOrderModel.mem_l n I := by
  obtain ⟨I, hI⟩ := SecondOrderModel.comprehension_l hℳ
    (.truth : Formula SecondOrderSyntax.signature_m [] [.num]) rfl Env.empty
  exact ⟨I, fun n => (hI n).mpr trivial⟩

theorem range_l (K : source_coding_l hℳ) {t₁ t₂ t₃ Pair Valid B P₀ S : SecondOrderQuotient.type_l hℳ}
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
    (hGuard : SecondOrderCanonicalLevelDerives.guard_l B P₀)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega S)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (hSome : ∀ x, mem_l hℳ x K.omega → ∃ X,
      PowerlessHereditaryClass.member_l hℳ B X ∧ φ.satisfies ((η.pushFree x).pushFree X)) :
    ∃ C : SecondOrderQuotient.type_l hℳ,
      (∀ X, mem_l hℳ X C → ∃ n, PowerlessHereditaryClass.member_l hℳ B X ∧
        φ.satisfies ((η.pushFree (numberCode_l K n).val).pushFree X)) ∧
      ∀ n, ∃ X, mem_l hℳ X C ∧ PowerlessHereditaryClass.member_l hℳ B X ∧
        φ.satisfies ((η.pushFree (numberCode_l K n).val).pushFree X) := by
  obtain ⟨H, hH⟩ := SecondOrderCanonicalHereditaryWitness.family_l K hCoding hGuard hS φ η hSome
  obtain ⟨J, hJ⟩ := SecondOrderRootedRealFamilyNormalization.exists_l hℳ H
  have hRow n (Y : SecondOrderModel.set_l ℳ) (hY : SecondOrderSections.spec_l J n Y) :
      ∃ hWf : SecondOrderDomain.wf_l Y (SecondOrderModel.zero_l ℳ),
        PowerlessHereditaryClass.member_l hℳ B (mk_l hℳ ⟨Y, SecondOrderModel.zero_l ℳ, hWf⟩) ∧
          φ.satisfies ((η.pushFree (numberCode_l K n).val).pushFree
            (mk_l hℳ ⟨Y, SecondOrderModel.zero_l ℳ, hWf⟩)) := by
    obtain ⟨V, X, hX, hφ, hRequest, hRead⟩ := hH n
    obtain ⟨hV, F, R, r, hWf, hTrace, hR, hRoot, hCollapse⟩ :=
      PowerlessHereditaryRealRequestDecode.exists_l K hS hRequest
    have hF : SecondOrderSections.spec_l H n F := fun m => (hTrace m).symm.trans (hRead m).symm
    obtain ⟨P, hNormal⟩ := SecondOrderRootedRealFamilyNormalization.row_normal_l hℳ hJ hF hR hRoot hY
    let A : SecondOrderGraph.code_l ℳ := ⟨R, r, hWf r⟩
    have hYwf := SecondOrderRootNormalization.root_l hℳ A hNormal
    have hEq : mk_l hℳ ⟨Y, SecondOrderModel.zero_l ℳ, hYwf⟩ = X :=
      ((SecondOrderQuotient.eq_iff_l hℳ _ A).mpr (SecondOrderRootNormalization.eq_l hℳ A hNormal)).trans hCollapse
    exact ⟨hYwf, hEq.symm ▸ hX, hEq.symm ▸ hφ⟩
  obtain ⟨I, hI⟩ := all_indices_l hℳ
  have hRows : SecondOrderCodedFamilyCollection.rows_wf_l J I := fun n _ Y hY => by
    obtain ⟨hWf, _, _⟩ := hRow n Y hY
    exact hWf
  obtain ⟨C, _, hC⟩ := SecondOrderCodedFamilyCollection.exists_l hℳ J I hRows
  refine ⟨mk_l hℳ C, ?_, fun n => ?_⟩
  · intro X hXC
    obtain ⟨D, rfl⟩ := SecondOrderQuotient.surj_l hℳ X
    obtain ⟨n, Y, _, hY, hZero, hDY⟩ := (hC D).mp hXC
    obtain ⟨hWf, hX, hφ⟩ := hRow n Y.real hY
    have hRoot : mk_l hℳ Y = mk_l hℳ ⟨Y.real, SecondOrderModel.zero_l ℳ, hWf⟩ := by
      cases Y with
      | mk real root wf => cases hZero; rfl
    have hEq := ((SecondOrderQuotient.eq_iff_l hℳ D Y).mpr hDY).trans hRoot
    exact ⟨n, hEq.symm ▸ hX, hEq.symm ▸ hφ⟩
  · obtain ⟨Y, hY⟩ := SecondOrderSections.exists_l hℳ J n
    obtain ⟨hWf, hX, hφ⟩ := hRow n Y hY
    exact ⟨mk_l hℳ ⟨Y, SecondOrderModel.zero_l ℳ, hWf⟩,
      (SecondOrderQuotient.mem_iff_l hℳ _ C).mpr
        (SecondOrderCodedFamilyCollection.row_mem_l hℳ hC (hI n) hY hWf), hX, hφ⟩

/-- 保留原覆盖接口；精确值域另由 range_l 提供，便于取序数共同界。 -/
theorem exists_l (K : source_coding_l hℳ) {t₁ t₂ t₃ Pair Valid B P₀ S : SecondOrderQuotient.type_l hℳ}
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
    (hGuard : SecondOrderCanonicalLevelDerives.guard_l B P₀)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega S)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (hSome : ∀ x, mem_l hℳ x K.omega → ∃ X,
      PowerlessHereditaryClass.member_l hℳ B X ∧ φ.satisfies ((η.pushFree x).pushFree X)) :
    ∃ C : SecondOrderQuotient.type_l hℳ, ∀ n, ∃ X,
      mem_l hℳ X C ∧ PowerlessHereditaryClass.member_l hℳ B X ∧
        φ.satisfies ((η.pushFree (numberCode_l K n).val).pushFree X) := by
  obtain ⟨C, _, hC⟩ := range_l K hCoding hGuard hS φ η hSome
  exact ⟨C, hC⟩

#print axioms range_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalHereditaryCollection
