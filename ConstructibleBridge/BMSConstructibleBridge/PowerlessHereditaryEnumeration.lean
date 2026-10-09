import BMSConstructibleBridge.PowerlessHereditaryCountability
import BMSConstructibleBridge.PowerlessHereditaryIntrinsicRelativization
import BMSConstructibleBridge.PowerlessRelativeClassInjectionEnumeration

/-! # 实际遗传母集的类内逆枚举

纯隶属 ℒ，背景原 Z₂。从同一母集已有的类内编号单射取得带默认值
逆枚举，再用 ω 与母集的遗传积包住整张图。输出是遗传域内真实函数，
不是环境枚举；不抽取 Type 选择。非空只提供一个 Prop 存在见证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryEnumeration

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessHereditaryStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  structure_l type_l PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒩₀" => PowerlessRelativeClassStructure.structure_l hℳ B hBase
local notation "𝒩₁" => structure_l hℳ B hBase
local notation "M" => PowerlessRelativeClassStructure.type_l hℳ B
local notation "N" => type_l hℳ B

theorem exists_l (K : source_coding_l hℳ) (O A : N)
    (hω : SecondOrderOmega.omega_l hℳ O.val) (hNonempty : ∃ d : N, mem_l hℳ d.val A.val) :
    ∃ F : N, map_l (ℳ := 𝒩₁) F O A ∧
      ∀ x : N, mem_l hℳ x.val A.val → ∃ i : N,
        mem_l hℳ i.val O.val ∧ value_l (ℳ := 𝒩₁) F i x := by
  obtain ⟨d, hd⟩ := hNonempty
  obtain ⟨f, hf, hMap, hInjective⟩ :=
    PowerlessHereditaryOrdinalCountability.countable_of_hereditary_l
      (hBase := hBase) K hω A.property
  let A₀ := PowerlessHereditaryIntrinsicRelativization.lift_l (hBase := hBase) A
  let O₀ := PowerlessHereditaryIntrinsicRelativization.lift_l (hBase := hBase) O
  let d₀ := PowerlessHereditaryIntrinsicRelativization.lift_l (hBase := hBase) d
  let R : M := ⟨f, hf⟩
  have hR : map_l (ℳ := 𝒩₀) R A₀ O₀ :=
    (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) R A₀ O₀).mpr hMap
  have hInj (x y i : M) (hx : value_l (ℳ := 𝒩₀) R x i)
      (hy : value_l (ℳ := 𝒩₀) R y i) : x = y :=
    Subtype.ext (hInjective x.val y.val i.val
      ((PowerlessRelativeClassFunctionAbsolute.value_l R x i).mp hx)
      ((PowerlessRelativeClassFunctionAbsolute.value_l R y i).mp hy))
  obtain ⟨G, hG, hOnto, _⟩ :=
    PowerlessRelativeClassInjectionEnumeration.exists_l hR hInj (d := d₀) hd
  have hRaw := (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) G O₀ A₀).mp hG
  have hHC := PowerlessHereditaryProduct.relation_l (hBase := hBase)
    O.property A.property G.property hRaw.1
  let F : N := ⟨G.val, hHC⟩
  refine ⟨F, (PowerlessHereditaryFunctionAbsolute.map_l (hBase := hBase) F O A).mpr hRaw, ?_⟩
  intro x hx
  let x₀ := PowerlessHereditaryIntrinsicRelativization.lift_l (hBase := hBase) x
  obtain ⟨i, hi, hix⟩ := hOnto x₀ hx
  let i₁ : N := ⟨i.val, PowerlessHereditaryClass.transitive_l hℳ O.property hi⟩
  exact ⟨i₁, hi, (PowerlessHereditaryFunctionAbsolute.value_l (hBase := hBase) F i₁ x).mpr
    ((PowerlessRelativeClassFunctionAbsolute.value_l G i x₀).mp hix)⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryEnumeration
