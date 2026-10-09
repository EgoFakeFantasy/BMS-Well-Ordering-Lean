import BMSConstructibleBridge.PowerlessHereditaryParameterSeparation
import BMSConstructibleBridge.PowerlessRelativeClassDefinableDiagramReading
import BMSConstructibleBridge.PowerlessRelativeClassRelation

/-! # 遗传参数给出同一实际数码隶属图

纯隶属 ℒ，背景原 Z₂。只用原参数的遗传资格，在实际 ω×ω 上
按 Class 真值分离，再认同原 raw 规范图。包络、分离种子、
初始序与程序枚举全部在证明内构造；原 A 不被替换。

本文件是语义接线，逐公式分离的对象出口在前置模块中。
原 raw 求值与 Class 求值仍须提供精确对应，不能用点态资格代替它。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryParameterDiagram

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessDefinableMembershipDiagram (spec_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => PowerlessRelativeClassStructure.structure_l hℳ B hBase
local notation "M" => PowerlessRelativeClassStructure.type_l hℳ B
local notation "ε" => SecondOrderQuotient.mem_l hℳ

theorem exists_l (hB : PowerlessHereditaryClass.member_l hℳ B B)
    (hNonempty : ∃ d, ε d B) (O : M) (hω : SecondOrderOmega.omega_l hℳ O.val)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) (χ : Env 𝒩₀ [] Δ)
    (hParams : ∀ v : Variable Δ .set, PowerlessHereditaryClass.member_l hℳ B (χ.freeVal v).val) :
    ∃ Z : M, PowerlessHereditaryClass.member_l hℳ B Z.val ∧ spec_l φ χ O Z := by
  have hωHC := PowerlessHereditaryOmega.member_l hℳ hBase hω
  obtain ⟨X, hX⟩ := SecondOrderDefinableRelationImage.exists_l hℳ (Δ := []) .truth Env.empty O.val O.val
  have hRawRead : ∀ p, ε p X ↔ ∃ n m,
      ε n O.val ∧ ε m O.val ∧ SecondOrderPairObjects.ordered_l hℳ n m p := by
    simpa only [Formula.satisfies, true_and] using hX
  have hXHC := PowerlessHereditaryProduct.member_l (hBase := hBase) hωHC hωHC hRawRead
  let X₀ : M := ⟨X, PowerlessHereditaryClass.contained_l hℳ hBase hXHC⟩
  have hProduct (p : M) : ε p.val X₀.val ↔ ∃ n m : M,
      ε n.val O.val ∧ ε m.val O.val ∧ ordered_l (ℳ := 𝒩₀) n m p := by
    constructor
    · intro hp
      obtain ⟨n, m, hn, hm, hPair⟩ := (hRawRead p.val).mp hp
      let n₀ : M := ⟨n, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase O.property hn⟩
      let m₀ : M := ⟨m, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase O.property hm⟩
      exact ⟨n₀, m₀, hn, hm,
        (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) n₀ m₀ p).mpr hPair⟩
    · rintro ⟨n, m, hn, hm, hPair⟩
      exact (hRawRead p.val).mpr ⟨n.val, m.val, hn, hm,
        (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) n m p).mp hPair⟩
  let ψ := PowerlessRelativeClassRelation.body_m (PowerlessDefinableMembershipDiagram.relation_m φ)
  let ξ := (χ.pushFree (sort := SetTheory.SetSort.set) O).pushFree (sort := SetTheory.SetSort.set) O
  have hParams' : ∀ v : Variable (.set :: .set :: Δ) .set,
      PowerlessHereditaryClass.member_l hℳ B (ξ.freeVal v).val := by
    intro v
    cases v with
    | here => exact hωHC
    | there v => cases v with
      | here => exact hωHC
      | there v => exact hParams v
  obtain ⟨Z, hZHC, hZ⟩ := PowerlessHereditaryParameterSeparation.exists_l hBase hω hB hNonempty
    ψ ξ X₀ hXHC hParams'
  refine ⟨Z, hZHC, fun p => ?_⟩
  have hBody := PowerlessRelativeClassRelation.body_formula_l
    (PowerlessDefinableMembershipDiagram.relation_m φ) χ O O p
  constructor
  · intro hp
    obtain ⟨_hpX, hpψ⟩ := (hZ p).mp hp
    obtain ⟨n, m, hn, hm, hPair, hEdge⟩ := hBody.mp hpψ
    exact ⟨n, m, hn, hm, (PowerlessDefinableMembershipDiagram.relation_formula_l φ χ n m).mp hEdge, hPair⟩
  · rintro ⟨n, m, hn, hm, hEdge, hPair⟩
    exact (hZ p).mpr ⟨(hProduct p).mpr ⟨n, m, hn, hm, hPair⟩,
      hBody.mpr ⟨n, m, hn, hm, hPair,
        (PowerlessDefinableMembershipDiagram.relation_formula_l φ χ n m).mpr hEdge⟩⟩

theorem same_l (hB : PowerlessHereditaryClass.member_l hℳ B B)
    (hNonempty : ∃ d, ε d B) (O : M) (hω : SecondOrderOmega.omega_l hℳ O.val)
    {Δ Θ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) (χ : Env 𝒩₀ [] Δ)
    (hParams : ∀ v : Variable Δ .set, PowerlessHereditaryClass.member_l hℳ B (χ.freeVal v).val)
    (ψ : Formula ℒ [] (.set :: .set :: Θ)) (ξ : Env 𝒱 [] Θ)
    (hRead : ∀ n y : M, ψ.satisfies ((ξ.pushFree n.val).pushFree y.val) ↔
      φ.satisfies ((χ.pushFree n).pushFree y))
    (hOutputs : ∀ (n : M) y, ψ.satisfies ((ξ.pushFree n.val).pushFree y) →
      PowerlessRelativeClassCorrespondence.member_l hℳ B y)
    (A : SecondOrderQuotient.type_l hℳ) (hA : spec_l ψ ξ O.val A) :
    PowerlessHereditaryClass.member_l hℳ B A := by
  obtain ⟨Z, hZHC, hZ⟩ := exists_l hB hNonempty O hω φ χ hParams
  have hEqual := PowerlessRelativeClassDefinableDiagramReading.same_l
    (hBase := hBase) φ ψ χ ξ hRead hOutputs O Z A hA hZ
  exact hEqual.symm ▸ hZHC

#print axioms exists_l
#print axioms same_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryParameterDiagram
