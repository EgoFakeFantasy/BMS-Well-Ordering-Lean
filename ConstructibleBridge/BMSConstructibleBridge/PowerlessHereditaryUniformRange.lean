import BMSConstructibleBridge.PowerlessHereditaryRootedWitnessFamily
import BMSConstructibleBridge.SecondOrderRootedRealFamilyNormalization
import BMSConstructibleBridge.SecondOrderCodedFamilyCollection
import BMSConstructibleBridge.PowerlessHereditaryNormalizedCollection

/-! # 类内原请求的统一遗传见证值域

纯隶属 ℒ，原 Z₂ 背景。原有限遗传参数的 Class 请求由整张类内
带根族 U／H 表示，再按原内部数索引统一零根并拼接集合 C。
C 中没有无关对象，每个索引的选中见证均保留；不要求请求单值。

整族 U 和同一收集对象 C 均实际遗传。旧 exists_l 保留弱返回签名，
hereditary_l 提供新增的 C 遗传资格；完整对象 Collection 另由原模式接线。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryUniformRange

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l mk_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒩₀" => PowerlessRelativeClassStructure.structure_l hℳ B hBase
local notation "M" => PowerlessRelativeClassStructure.type_l hℳ B

private theorem indices_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    ∃ I : SecondOrderModel.set_l ℳ, ∀ n, SecondOrderModel.mem_l n I := by
  obtain ⟨I, hI⟩ := SecondOrderModel.comprehension_l hℳ
    (.truth : Formula SecondOrderSyntax.signature_m [] [.num]) rfl Env.empty
  exact ⟨I, fun n => (hI n).mpr trivial⟩

theorem hereditary_l (K : source_coding_l hℳ)
    (hB : PowerlessHereditaryClass.member_l hℳ B B) (hNonempty : ∃ d, mem_l hℳ d B)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) (χ : Env 𝒩₀ [] Δ)
    (hParams : ∀ v : Variable Δ .set, PowerlessHereditaryClass.member_l hℳ B (χ.freeVal v).val)
    (hSome : ∀ x : M, mem_l hℳ x.val K.omega → ∃ X : M,
      PowerlessHereditaryClass.member_l hℳ B X.val ∧ φ.satisfies ((χ.pushFree x).pushFree X)) :
    ∃ U : M, PowerlessHereditaryClass.member_l hℳ B U.val ∧
      ∃ hU : ∀ m, mem_l hℳ m U.val → mem_l hℳ m K.omega,
        ∃ H : SecondOrderModel.set_l ℳ, setRel_l K ⟨U.val, hU⟩ H ∧
          ∃ C : SecondOrderQuotient.type_l hℳ,
            PowerlessHereditaryClass.member_l hℳ B C ∧
            (∀ Z, mem_l hℳ Z C → ∃ n : SecondOrderModel.num_l ℳ, ∃ X : M,
              X.val = Z ∧ PowerlessHereditaryClass.member_l hℳ B X.val ∧
              φ.satisfies ((χ.pushFree (PowerlessRelativeClassInduction.number_l (hBase := hBase) K n)).pushFree X)) ∧
            ∀ n : SecondOrderModel.num_l ℳ, ∃ X : M, mem_l hℳ X.val C ∧
              PowerlessHereditaryClass.member_l hℳ B X.val ∧
              φ.satisfies ((χ.pushFree (PowerlessRelativeClassInduction.number_l (hBase := hBase) K n)).pushFree X) := by
  obtain ⟨S, _hSHC, hS, U, hUHC, hU, H, hTrace, hRows⟩ :=
    PowerlessHereditaryRootedWitnessFamily.exists_l K hB hNonempty φ χ hParams hSome
  obtain ⟨J, hJ⟩ := SecondOrderRootedRealFamilyNormalization.exists_l hℳ H
  have hRow n (Y : SecondOrderModel.set_l ℳ) (hY : SecondOrderSections.spec_l J n Y) :
      ∃ hWf : SecondOrderDomain.wf_l Y (SecondOrderModel.zero_l ℳ), ∃ X : M,
        mk_l hℳ ⟨Y, SecondOrderModel.zero_l ℳ, hWf⟩ = X.val ∧
          PowerlessHereditaryClass.member_l hℳ B X.val ∧
          φ.satisfies ((χ.pushFree (PowerlessRelativeClassInduction.number_l (hBase := hBase) K n)).pushFree X) := by
    obtain ⟨V, X, _hVHC, hXHC, hφ, hRequest, hRead⟩ := hRows n
    obtain ⟨hV, F, R, r, hWf, hVTrace, hR, hRoot, hCollapse⟩ :=
      PowerlessHereditaryRealRequestDecode.exists_l K hS hRequest
    have hF : SecondOrderSections.spec_l H n F := fun m => (hVTrace m).symm.trans (hRead m).symm
    obtain ⟨P, hNormal⟩ := SecondOrderRootedRealFamilyNormalization.row_normal_l hℳ hJ hF hR hRoot hY
    let A : SecondOrderGraph.code_l ℳ := ⟨R, r, hWf r⟩
    have hYwf := SecondOrderRootNormalization.root_l hℳ A hNormal
    have hEq : mk_l hℳ ⟨Y, SecondOrderModel.zero_l ℳ, hYwf⟩ = X.val :=
      ((SecondOrderQuotient.eq_iff_l hℳ _ A).mpr (SecondOrderRootNormalization.eq_l hℳ A hNormal)).trans hCollapse
    exact ⟨hYwf, X, hEq, hXHC, hφ⟩
  obtain ⟨I, hI⟩ := indices_l hℳ
  have hWfRows : SecondOrderCodedFamilyCollection.rows_wf_l J I := fun n _ Y hY => by
    obtain ⟨hWf, _⟩ := hRow n Y hY
    exact hWf
  obtain ⟨C, _hRoot, hC⟩ := SecondOrderCodedFamilyCollection.exists_l hℳ J I hWfRows
  have hCHC := PowerlessHereditaryNormalizedCollection.hereditary_l (hBase := hBase)
    K U hU hTrace hJ hI hWfRows (mk_l hℳ C)
    (fun D => (SecondOrderQuotient.mem_iff_l hℳ D C).trans (hC D))
  refine ⟨U, hUHC, hU, H, hTrace, mk_l hℳ C, hCHC, ?_, fun n => ?_⟩
  · intro Z hZC
    obtain ⟨D, rfl⟩ := SecondOrderQuotient.surj_l hℳ Z
    obtain ⟨n, Y, _hi, hY, hZero, hDY⟩ := (hC D).mp hZC
    obtain ⟨hWf, X, hEq, hXHC, hφ⟩ := hRow n Y.real hY
    have hRootEq : mk_l hℳ Y = mk_l hℳ ⟨Y.real, SecondOrderModel.zero_l ℳ, hWf⟩ := by
      cases Y with
      | mk real root wf => cases hZero; rfl
    have hDX := ((SecondOrderQuotient.eq_iff_l hℳ D Y).mpr hDY).trans (hRootEq.trans hEq)
    exact ⟨n, X, hDX.symm, hXHC, hφ⟩
  · obtain ⟨Y, hY⟩ := SecondOrderSections.exists_l hℳ J n
    obtain ⟨hWf, X, hEq, hXHC, hφ⟩ := hRow n Y hY
    exact ⟨X, hEq ▸ (SecondOrderQuotient.mem_iff_l hℳ _ C).mpr
      (SecondOrderCodedFamilyCollection.row_mem_l hℳ hC (hI n) hY hWf), hXHC, hφ⟩

/-- 保留原弱返回签名；新增强接口不改变调用端的对象和请求。 -/
theorem exists_l (K : source_coding_l hℳ)
    (hB : PowerlessHereditaryClass.member_l hℳ B B) (hNonempty : ∃ d, mem_l hℳ d B)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) (χ : Env 𝒩₀ [] Δ)
    (hParams : ∀ v : Variable Δ .set, PowerlessHereditaryClass.member_l hℳ B (χ.freeVal v).val)
    (hSome : ∀ x : M, mem_l hℳ x.val K.omega → ∃ X : M,
      PowerlessHereditaryClass.member_l hℳ B X.val ∧ φ.satisfies ((χ.pushFree x).pushFree X)) :
    ∃ U : M, PowerlessHereditaryClass.member_l hℳ B U.val ∧
      ∃ hU : ∀ m, mem_l hℳ m U.val → mem_l hℳ m K.omega,
        ∃ H : SecondOrderModel.set_l ℳ, setRel_l K ⟨U.val, hU⟩ H ∧
          ∃ C : SecondOrderQuotient.type_l hℳ,
            (∀ Z, mem_l hℳ Z C → ∃ n : SecondOrderModel.num_l ℳ, ∃ X : M,
              X.val = Z ∧ PowerlessHereditaryClass.member_l hℳ B X.val ∧
              φ.satisfies ((χ.pushFree (PowerlessRelativeClassInduction.number_l (hBase := hBase) K n)).pushFree X)) ∧
            ∀ n : SecondOrderModel.num_l ℳ, ∃ X : M, mem_l hℳ X.val C ∧
              PowerlessHereditaryClass.member_l hℳ B X.val ∧
              φ.satisfies ((χ.pushFree (PowerlessRelativeClassInduction.number_l (hBase := hBase) K n)).pushFree X) := by
  obtain ⟨U, hUHC, hU, H, hTrace, C, _hCHC, hRange, hCover⟩ :=
    hereditary_l K hB hNonempty φ χ hParams hSome
  exact ⟨U, hUHC, hU, H, hTrace, C, hRange, hCover⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryUniformRange
