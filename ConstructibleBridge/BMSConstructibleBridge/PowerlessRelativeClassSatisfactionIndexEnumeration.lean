import BMSConstructibleBridge.PowerlessRelativeClassFiniteSequenceEnumeration
import BMSConstructibleBridge.PowerlessRelativeClassProductEnumeration

/-! # 全内部满足关系槽指标的类内枚举

给定母集的实际类内 ω 满射，先枚举全部内部有限赋值，再两次形成并枚举
有序积，得到 ω × (ω × Seq(ω,X)) 的实际类内满射。两个积都保留全部
类坐标的精确规格。这里不收集逐阶段枚举，不宣称超限历史已构造。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSatisfactionIndexEnumeration

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒩" => structure_l hℳ B hBase

/-- 任意类集合的实际恒等图；仅使用纯等式 Δ₀ 切片。 -/
theorem identity_l (X : type_l hℳ B) :
    ∃ F : type_l hℳ B, map_l (ℳ := 𝒩) F X X ∧ ∀ x y : type_l hℳ B,
      value_l (ℳ := 𝒩) F x y ↔ mem_l hℳ x.val X.val ∧ y = x := by
  let φ : Formula ℒ [] [.set, .set] := .equal (.fvar (.there .here)) (.fvar .here)
  let η : Env 𝒩 [] [] := Env.empty
  have hφ (x y : type_l hℳ B) : φ.satisfies ((η.pushFree y).pushFree x) ↔ y = x := Iff.rfl
  obtain ⟨F, hF, hRead⟩ := PowerlessRelativeClassFunctionRelation.exists_l (hBase := hBase)
    (φ := φ) (show Formula.IsDelta0 membershipLevyBound φ from .equal _ _) η X X (by
      intro x hx
      exact ⟨x, ⟨hx, (hφ x x).mpr rfl⟩, fun y hy => (hφ x y).mp hy.2⟩)
  refine ⟨F, hF, fun x y => (hRead x y).trans ?_⟩
  constructor
  · intro h
    exact ⟨h.1, (hφ x y).mp h.2.2⟩
  · rintro ⟨hx, hEq⟩
    exact ⟨hx, hEq.symm ▸ hx, (hφ x y).mpr hEq⟩

/-- 已有规范槽载体可直接枚举，不必换掉其查询图或行族。 -/
theorem of_spec_l {ω X E S I J : type_l hℳ B}
    (hω : omega_l (ℳ := 𝒩) ω) (hE : map_l (ℳ := 𝒩) E ω X)
    (hOnto : ∀ x : type_l hℳ B, mem_l hℳ x.val X.val →
      ∃ i : type_l hℳ B, mem_l hℳ i.val ω.val ∧ value_l (ℳ := 𝒩) E i x)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒩) ω X S)
    (hI : ∀ p : type_l hℳ B, mem_l hℳ p.val I.val ↔ ∃ c f : type_l hℳ B,
      mem_l hℳ c.val ω.val ∧ mem_l hℳ f.val S.val ∧ ordered_l (ℳ := 𝒩) c f p)
    (hJ : ∀ p : type_l hℳ B, mem_l hℳ p.val J.val ↔ ∃ n i : type_l hℳ B,
      mem_l hℳ n.val ω.val ∧ mem_l hℳ i.val I.val ∧ ordered_l (ℳ := 𝒩) n i p) :
    ∃ U : type_l hℳ B, map_l (ℳ := 𝒩) U ω J ∧ ∀ p : type_l hℳ B,
      mem_l hℳ p.val J.val → ∃ i : type_l hℳ B, mem_l hℳ i.val ω.val ∧ value_l (ℳ := 𝒩) U i p := by
  obtain ⟨S₀, hS₀, F, hF, hFOnto⟩ := PowerlessRelativeClassFiniteSequenceEnumeration.exists_l hω hE hOnto
  have hEq : S₀ = S := by
    apply (PowerlessRelativeClassStructure.ext_l hℳ B hBase).eq_of_same_members
    exact fun f => (hS₀ f).trans (hS f).symm
  subst S₀
  obtain ⟨N, hN, hNRead⟩ := identity_l (hBase := hBase) ω
  have hNOnto : ∀ y : type_l hℳ B, mem_l hℳ y.val ω.val →
      ∃ i : type_l hℳ B, mem_l hℳ i.val ω.val ∧ value_l (ℳ := 𝒩) N i y :=
    fun y hy => ⟨y, hy, (hNRead y y).mpr ⟨hy, rfl⟩⟩
  obtain ⟨G, hG, hGOnto⟩ := PowerlessRelativeClassProductEnumeration.exists_l hω hN hF hNOnto hFOnto hI
  exact PowerlessRelativeClassProductEnumeration.exists_l hω hN hG hNOnto hGOnto hJ

theorem exists_l {ω X E : type_l hℳ B}
    (hω : omega_l (ℳ := 𝒩) ω) (hE : map_l (ℳ := 𝒩) E ω X)
    (hOnto : ∀ x : type_l hℳ B, mem_l hℳ x.val X.val →
      ∃ i : type_l hℳ B, mem_l hℳ i.val ω.val ∧ value_l (ℳ := 𝒩) E i x) :
    ∃ S I J U : type_l hℳ B,
      PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒩) ω X S ∧
      (∀ p : type_l hℳ B, mem_l hℳ p.val I.val ↔ ∃ c f : type_l hℳ B,
        mem_l hℳ c.val ω.val ∧ mem_l hℳ f.val S.val ∧ ordered_l (ℳ := 𝒩) c f p) ∧
      (∀ p : type_l hℳ B, mem_l hℳ p.val J.val ↔ ∃ n i : type_l hℳ B,
        mem_l hℳ n.val ω.val ∧ mem_l hℳ i.val I.val ∧ ordered_l (ℳ := 𝒩) n i p) ∧
      map_l (ℳ := 𝒩) U ω J ∧ ∀ p : type_l hℳ B, mem_l hℳ p.val J.val →
        ∃ i : type_l hℳ B, mem_l hℳ i.val ω.val ∧ value_l (ℳ := 𝒩) U i p := by
  obtain ⟨S, hS⟩ := PowerlessRelativeClassFiniteSequencesDerives.exists_l (hBase := hBase) (X := X) hω
  obtain ⟨I, hI⟩ := PowerlessRelativeClassProduct.exists_l hBase ω S
  obtain ⟨J, hJ⟩ := PowerlessRelativeClassProduct.exists_l hBase ω I
  obtain ⟨U, hU, hUOnto⟩ := of_spec_l hω hE hOnto hS hI hJ
  exact ⟨S, I, J, U, hS, hI, hJ, hU, hUOnto⟩

#print axioms identity_l
#print axioms of_spec_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSatisfactionIndexEnumeration
