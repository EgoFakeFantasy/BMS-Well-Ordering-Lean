import BMSConstructibleBridge.PowerlessHereditaryUniformRange
import BMSConstructibleBridge.PowerlessHereditaryIntrinsicRelativization

/-! # 实际遗传子模型真值的统一见证接口

纯隶属 ℒ，背景原 Z₂。输入正文在实际 Hereditary 子模型解释，
不是任意 Class 量词真值。前置逐公式翻译保留原有限参数、输入和
输出；整张统一族 U 属于 Hereditary，环境商集合 C 覆盖每个请求。

hereditary_l 现包含同一 C 的遗传资格，来自类内码的实际根解码，
不是从成员资格推断。旧 exists_l 的弱返回签名保持原样。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryIntrinsicUniformRange

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l
  PowerlessHereditaryStructure.structure_l PowerlessHereditaryStructure.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒩₀" => PowerlessRelativeClassStructure.structure_l hℳ B hBase
local notation "𝒩₁" => PowerlessHereditaryStructure.structure_l hℳ B hBase
local notation "M" => PowerlessRelativeClassStructure.type_l hℳ B
local notation "N" => PowerlessHereditaryStructure.type_l hℳ B

theorem push_free_l {Γ Δ : SortContext ℒ} (η : Env 𝒩₁ Γ Δ) (x : N) :
    PowerlessHereditaryIntrinsicRelativization.env_l (η.pushFree (sort := SetTheory.SetSort.set) x) =
      (PowerlessHereditaryIntrinsicRelativization.env_l η).pushFree
        (sort := SetTheory.SetSort.set) (PowerlessHereditaryIntrinsicRelativization.lift_l (hBase := hBase) x) := by
  apply Env.ext
  · intro s v; cases s; rfl
  · intro s v; cases s; cases v <;> rfl

theorem formula_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒩₁ [] Δ) (x X : N) :
    (PowerlessHereditaryIntrinsicRelativization.formula_m φ).satisfies
      (((PowerlessHereditaryIntrinsicRelativization.env_l η).pushFree
        (PowerlessHereditaryIntrinsicRelativization.lift_l (hBase := hBase) x)).pushFree
          (PowerlessHereditaryIntrinsicRelativization.lift_l (hBase := hBase) X)) ↔
      φ.satisfies ((η.pushFree x).pushFree X) := by
  have h := PowerlessHereditaryIntrinsicRelativization.formula_l φ ((η.pushFree x).pushFree X)
  simpa only [push_free_l] using h

theorem hereditary_l (K : source_coding_l hℳ)
    (hB : PowerlessHereditaryClass.member_l hℳ B B) (hNonempty : ∃ d, mem_l hℳ d B)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩₁ [] Δ)
    (hSome : ∀ x : N, mem_l hℳ x.val K.omega → ∃ X : N, φ.satisfies ((η.pushFree x).pushFree X)) :
    ∃ U : N, ∃ hU : ∀ m, mem_l hℳ m U.val → mem_l hℳ m K.omega,
      ∃ H : SecondOrderModel.set_l ℳ, setRel_l K ⟨U.val, hU⟩ H ∧
        ∃ C : SecondOrderQuotient.type_l hℳ,
          PowerlessHereditaryClass.member_l hℳ B C ∧
          (∀ Z, mem_l hℳ Z C → ∃ x X : N, mem_l hℳ x.val K.omega ∧
            X.val = Z ∧ φ.satisfies ((η.pushFree x).pushFree X)) ∧
          ∀ x : N, mem_l hℳ x.val K.omega → ∃ X : N, mem_l hℳ X.val C ∧
            φ.satisfies ((η.pushFree x).pushFree X) := by
  let χ := PowerlessHereditaryIntrinsicRelativization.env_l η
  let ψ := PowerlessHereditaryIntrinsicRelativization.formula_m φ
  have hωHC := PowerlessHereditaryOmega.member_l hℳ hBase K.omega_spec
  have hParams : ∀ v : Variable Δ .set, PowerlessHereditaryClass.member_l hℳ B (χ.freeVal v).val :=
    fun v => (η.freeVal v).property
  have hSome' (x : M) (hx : mem_l hℳ x.val K.omega) : ∃ X : M,
      PowerlessHereditaryClass.member_l hℳ B X.val ∧ ψ.satisfies ((χ.pushFree x).pushFree X) := by
    let x₀ : N := ⟨x.val, PowerlessHereditaryClass.transitive_l hℳ hωHC hx⟩
    have hEq : PowerlessHereditaryIntrinsicRelativization.lift_l (hBase := hBase) x₀ = x := Subtype.ext rfl
    obtain ⟨X, hX⟩ := hSome x₀ hx
    exact ⟨PowerlessHereditaryIntrinsicRelativization.lift_l (hBase := hBase) X,
      X.property, hEq ▸ (formula_l φ η x₀ X).mpr hX⟩
  obtain ⟨U, hUHC, hU, H, hTrace, C, hCHC, hRange, hCover⟩ :=
    PowerlessHereditaryUniformRange.hereditary_l K hB hNonempty ψ χ hParams hSome'
  refine ⟨⟨U.val, hUHC⟩, hU, H, hTrace, C, hCHC, ?_, ?_⟩
  · intro Z hZ
    obtain ⟨n, X, hXZ, hXHC, hφ⟩ := hRange Z hZ
    have hn : mem_l hℳ (numberCode_l K n).val K.omega := (numberCode_l K n).property
    let x : N := ⟨(numberCode_l K n).val, PowerlessHereditaryClass.transitive_l hℳ hωHC hn⟩
    let X₀ : N := ⟨X.val, hXHC⟩
    have hxEq : PowerlessHereditaryIntrinsicRelativization.lift_l (hBase := hBase) x =
        PowerlessRelativeClassInduction.number_l (hBase := hBase) K n := Subtype.ext rfl
    have hXEq : PowerlessHereditaryIntrinsicRelativization.lift_l (hBase := hBase) X₀ = X := Subtype.ext rfl
    refine ⟨x, X₀, hn, hXZ, ?_⟩
    exact (formula_l φ η x X₀).mp (hxEq.symm ▸ hXEq.symm ▸ hφ)
  · intro x hx
    obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨x.val, hx⟩
    have hn' : (numberCode_l K n).val = x.val := congrArg Subtype.val hn
    obtain ⟨X, hXC, hXHC, hφ⟩ := hCover n
    let X₀ : N := ⟨X.val, hXHC⟩
    have hxEq : PowerlessRelativeClassInduction.number_l (hBase := hBase) K n =
        PowerlessHereditaryIntrinsicRelativization.lift_l (hBase := hBase) x :=
      Subtype.ext hn'
    have hXEq : PowerlessHereditaryIntrinsicRelativization.lift_l (hBase := hBase) X₀ = X := Subtype.ext rfl
    exact ⟨X₀, hXC, (formula_l φ η x X₀).mp (hXEq.symm ▸ hxEq ▸ hφ)⟩

#print axioms formula_l
/-- 原弱接口仍返回相同请求的覆盖集合，不删除已有公共签名。 -/
theorem exists_l (K : source_coding_l hℳ)
    (hB : PowerlessHereditaryClass.member_l hℳ B B) (hNonempty : ∃ d, mem_l hℳ d B)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩₁ [] Δ)
    (hSome : ∀ x : N, mem_l hℳ x.val K.omega → ∃ X : N, φ.satisfies ((η.pushFree x).pushFree X)) :
    ∃ U : N, ∃ hU : ∀ m, mem_l hℳ m U.val → mem_l hℳ m K.omega,
      ∃ H : SecondOrderModel.set_l ℳ, setRel_l K ⟨U.val, hU⟩ H ∧
        ∃ C : SecondOrderQuotient.type_l hℳ,
          (∀ Z, mem_l hℳ Z C → ∃ x X : N, mem_l hℳ x.val K.omega ∧
            X.val = Z ∧ φ.satisfies ((η.pushFree x).pushFree X)) ∧
          ∀ x : N, mem_l hℳ x.val K.omega → ∃ X : N, mem_l hℳ X.val C ∧
            φ.satisfies ((η.pushFree x).pushFree X) := by
  obtain ⟨U, hU, H, hTrace, C, _hCHC, hRange, hCover⟩ :=
    hereditary_l K hB hNonempty φ η hSome
  exact ⟨U, hU, H, hTrace, C, hRange, hCover⟩

#print axioms hereditary_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryIntrinsicUniformRange
