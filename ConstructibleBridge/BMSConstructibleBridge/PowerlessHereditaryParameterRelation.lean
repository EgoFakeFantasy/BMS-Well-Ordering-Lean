import BMSConstructibleBridge.PowerlessHereditaryParameterSeparation
import BMSConstructibleBridge.PowerlessRelativeClassRelationalGraph

/-! # 有限遗传参数定义的实际关系图

纯隶属 ℒ，原 Z₂ 背景。母域和陪域都遗传，指定有限原参数都遗传，
则任意 Class 公式在同一实际积上分离为整张遗传关系图。公式不要求 Δ₀；
点态值读数不能代替整图存在性。分离对象推导消费前置模块的原实例，
本文件只提供实际关系图的语义装配，不宣称 Collection 或最终良序完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryParameterRelation

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒩₀" => PowerlessRelativeClassStructure.structure_l hℳ B hBase
local notation "M" => PowerlessRelativeClassStructure.type_l hℳ B
local notation "ε" => SecondOrderQuotient.mem_l hℳ

theorem exists_l (hB : PowerlessHereditaryClass.member_l hℳ B B)
    (hNonempty : ∃ d, ε d B) {ω : SecondOrderQuotient.type_l hℳ}
    (hω : SecondOrderOmega.omega_l hℳ ω) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (χ : Env 𝒩₀ [] Δ)
    (hParams : ∀ v : Variable Δ .set, PowerlessHereditaryClass.member_l hℳ B (χ.freeVal v).val)
    (X Y : M) (hX : PowerlessHereditaryClass.member_l hℳ B X.val)
    (hY : PowerlessHereditaryClass.member_l hℳ B Y.val) :
    ∃ G : M, PowerlessHereditaryClass.member_l hℳ B G.val ∧
      ∀ p : M, ε p.val G.val ↔ ∃ x y : M, ε x.val X.val ∧ ε y.val Y.val ∧
        ordered_l (ℳ := 𝒩₀) x y p ∧ φ.satisfies ((χ.pushFree y).pushFree x) := by
  obtain ⟨P, hP⟩ := SecondOrderDefinableRelationImage.exists_l hℳ (Δ := []) .truth Env.empty X.val Y.val
  have hRaw : ∀ p, ε p P ↔ ∃ x y, ε x X.val ∧ ε y Y.val ∧
      SecondOrderPairObjects.ordered_l hℳ x y p := by
    simpa only [Formula.satisfies, true_and] using hP
  have hPHC := PowerlessHereditaryProduct.member_l (hBase := hBase) hX hY hRaw
  let P₀ : M := ⟨P, PowerlessHereditaryClass.contained_l hℳ hBase hPHC⟩
  have hProduct (p : M) : ε p.val P₀.val ↔ ∃ x y : M, ε x.val X.val ∧ ε y.val Y.val ∧
      ordered_l (ℳ := 𝒩₀) x y p := by
    constructor
    · intro hp
      obtain ⟨x, y, hx, hy, hxy⟩ := (hRaw p.val).mp hp
      let x₀ : M := ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase X.property hx⟩
      let y₀ : M := ⟨y, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Y.property hy⟩
      exact ⟨x₀, y₀, hx, hy,
        (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) x₀ y₀ p).mpr hxy⟩
    · rintro ⟨x, y, hx, hy, hxy⟩
      exact (hRaw p.val).mpr ⟨x.val, y.val, hx, hy,
        (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) x y p).mp hxy⟩
  let ξ := (χ.pushFree (sort := SetTheory.SetSort.set) Y).pushFree (sort := SetTheory.SetSort.set) X
  have hParams' : ∀ v : Variable (.set :: .set :: Δ) .set,
      PowerlessHereditaryClass.member_l hℳ B (ξ.freeVal v).val := by
    intro v
    cases v with
    | here => exact hX
    | there v => cases v with
      | here => exact hY
      | there v => exact hParams v
  obtain ⟨G, hGHC, hG⟩ := PowerlessHereditaryParameterSeparation.exists_l hBase hω hB hNonempty
    (PowerlessRelativeClassRelation.body_m φ) ξ P₀ hPHC hParams'
  refine ⟨G, hGHC, fun p => ?_⟩
  have hBody := PowerlessRelativeClassRelation.body_formula_l φ χ X Y p
  constructor
  · intro hp
    exact hBody.mp ((hG p).mp hp).2
  · rintro ⟨x, y, hx, hy, hxy, hφ⟩
    exact (hG p).mpr ⟨(hProduct p).mpr ⟨x, y, hx, hy, hxy⟩,
      hBody.mpr ⟨x, y, hx, hy, hxy, hφ⟩⟩

/-- 多值关系也允许；没有偷偷加入逐输入总唯一性。 -/
theorem values_l (hB : PowerlessHereditaryClass.member_l hℳ B B)
    (hNonempty : ∃ d, ε d B) {ω : SecondOrderQuotient.type_l hℳ}
    (hω : SecondOrderOmega.omega_l hℳ ω) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (χ : Env 𝒩₀ [] Δ)
    (hParams : ∀ v : Variable Δ .set, PowerlessHereditaryClass.member_l hℳ B (χ.freeVal v).val)
    (X Y : M) (hX : PowerlessHereditaryClass.member_l hℳ B X.val)
    (hY : PowerlessHereditaryClass.member_l hℳ B Y.val) :
    ∃ G : M, PowerlessHereditaryClass.member_l hℳ B G.val ∧
      ∀ x y : M, value_l (ℳ := 𝒩₀) G x y ↔ ε x.val X.val ∧ ε y.val Y.val ∧
        φ.satisfies ((χ.pushFree y).pushFree x) := by
  obtain ⟨G, hGHC, hG⟩ := exists_l hB hNonempty hω φ χ hParams X Y hX hY
  refine ⟨G, hGHC, fun x y => ⟨?_, ?_⟩⟩
  · rintro ⟨p, hp, hxy⟩
    obtain ⟨a, b, ha, hb, hab, hφ⟩ := (hG p).mp hp
    have hEq := (SecondOrderPairObjects.ordered_eq_l hℳ
      ((PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) x y p).mp hxy)
      ((PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) a b p).mp hab)).mp rfl
    have hxa : x = a := Subtype.ext hEq.1
    have hyb : y = b := Subtype.ext hEq.2
    simpa only [hxa, hyb] using And.intro ha (And.intro hb hφ)
  · rintro ⟨hx, hy, hφ⟩
    obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ x.val y.val
    let p₀ : M := ⟨p, PowerlessRelativeClassPair.ordered_l hℳ hBase x.property y.property hp⟩
    have hp' := (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) x y p₀).mpr hp
    exact ⟨p₀, (hG p₀).mpr ⟨x, y, hx, hy, hp', hφ⟩, hp'⟩

#print axioms exists_l
#print axioms values_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryParameterRelation
