import BMSConstructibleBridge.PowerlessRelativeClassFunctionAbsolute
import BMSConstructibleBridge.PowerlessSourceFamily

/-! # 同一带标签有限请求族的 Class 读数

原 raw 环境与类内原参数环境可以不同，只需逐项请求和标签读数对应。
每层标签的实际 Kuratowski 解码把内部候选送回 Class；保留原列表次序，
不以无标签析取替代，也不假定 raw 元数据全部属于 Class。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassRequestFamilyReading

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ z, mem_l hℳ z B → ∀ t, mem_l hℳ t z → mem_l hℳ t B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => structure_l hℳ B hBase
local notation "M" => type_l hℳ B

include hBase

theorem coordinates_l (p : M) {x y : SecondOrderQuotient.type_l hℳ}
    (h : ordered_l (ℳ := 𝒱) x y p.val) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B x ∧
      PowerlessRelativeClassCorrespondence.member_l hℳ B y := by
  change SecondOrderPairObjects.ordered_l hℳ x y p.val at h
  obtain ⟨s, t, _hs, ht, hp⟩ := h
  have htClass := PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase p.property
    ((hp t).mpr (Or.inr rfl))
  exact ⟨PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase htClass
      ((ht x).mpr (Or.inl rfl)),
    PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase htClass
      ((ht y).mpr (Or.inr rfl))⟩

theorem sum_l {Γ Θ : SortContext ℒ}
    (φ ψ : Formula ℒ [] (.set :: .set :: Γ)) (χ θ : Formula ℒ [] (.set :: .set :: Θ))
    (η : Env 𝒩₀ [] Γ) (ξ : Env 𝒱 [] Θ)
    (s t : Term ℒ [] Γ .set) (S T : Term ℒ [] Θ .set)
    (hs : (s.eval η).val = S.eval ξ) (ht : (t.eval η).val = T.eval ξ)
    (hφ : ∀ x y : M, χ.satisfies ((ξ.pushFree x.val).pushFree y.val) ↔
      φ.satisfies ((η.pushFree x).pushFree y))
    (hψ : ∀ x y : M, θ.satisfies ((ξ.pushFree x.val).pushFree y.val) ↔
      ψ.satisfies ((η.pushFree x).pushFree y)) (p y : M) :
    (PowerlessSourceFamily.sum_m χ θ S T).satisfies ((ξ.pushFree p.val).pushFree y.val) ↔
      (PowerlessSourceFamily.sum_m φ ψ s t).satisfies ((η.pushFree p).pushFree y) := by
  simp only [PowerlessSourceFamily.sum_formula_l]
  constructor
  · rintro ⟨x, ⟨hx, hχ⟩ | ⟨hx, hθ⟩⟩
    · let x₀ : M := ⟨x, (coordinates_l (hBase := hBase) p hx).2⟩
      have hPair := hx
      rw [← hs] at hPair
      exact ⟨x₀, Or.inl ⟨(PowerlessRelativeClassFunctionAbsolute.ordered_l
        (hBase := hBase) (s.eval η) x₀ p).mpr hPair, (hφ x₀ y).mp hχ⟩⟩
    · let x₀ : M := ⟨x, (coordinates_l (hBase := hBase) p hx).2⟩
      have hPair := hx
      rw [← ht] at hPair
      exact ⟨x₀, Or.inr ⟨(PowerlessRelativeClassFunctionAbsolute.ordered_l
        (hBase := hBase) (t.eval η) x₀ p).mpr hPair, (hψ x₀ y).mp hθ⟩⟩
  · rintro ⟨x, ⟨hx, hφx⟩ | ⟨hx, hψx⟩⟩
    · have hPair := (PowerlessRelativeClassFunctionAbsolute.ordered_l
        (hBase := hBase) (s.eval η) x p).mp hx
      rw [hs] at hPair
      exact ⟨x.val, Or.inl ⟨hPair, (hφ x y).mpr hφx⟩⟩
    · have hPair := (PowerlessRelativeClassFunctionAbsolute.ordered_l
        (hBase := hBase) (t.eval η) x p).mp hx
      rw [ht] at hPair
      exact ⟨x.val, Or.inr ⟨hPair, (hψ x y).mpr hψx⟩⟩

theorem sum_output_l {Θ : SortContext ℒ}
    (φ ψ : Formula ℒ [] (.set :: .set :: Θ)) (ξ : Env 𝒱 [] Θ)
    (s t : Term ℒ [] Θ .set)
    (hφ : ∀ x : M, ∀ y, φ.satisfies ((ξ.pushFree x.val).pushFree y) →
      PowerlessRelativeClassCorrespondence.member_l hℳ B y)
    (hψ : ∀ x : M, ∀ y, ψ.satisfies ((ξ.pushFree x.val).pushFree y) →
      PowerlessRelativeClassCorrespondence.member_l hℳ B y)
    (p : M) (y : SecondOrderQuotient.type_l hℳ)
    (h : (PowerlessSourceFamily.sum_m φ ψ s t).satisfies ((ξ.pushFree p.val).pushFree y)) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B y := by
  obtain ⟨x, hx⟩ := (PowerlessSourceFamily.sum_formula_l φ ψ ξ s t p.val y).mp h
  rcases hx with ⟨hx, hφx⟩ | ⟨hx, hψx⟩
  · exact hφ ⟨x, (coordinates_l (hBase := hBase) p hx).2⟩ y hφx
  · exact hψ ⟨x, (coordinates_l (hBase := hBase) p hx).2⟩ y hψx

theorem family_l {Γ Θ : SortContext ℒ}
    (η : Env 𝒩₀ [] Γ) (ξ : Env 𝒱 [] Θ)
    (s t : Term ℒ [] Γ .set) (S T : Term ℒ [] Θ .set)
    (hs : (s.eval η).val = S.eval ξ) (ht : (t.eval η).val = T.eval ξ)
    {Φ : List (Formula ℒ [] (.set :: .set :: Γ))}
    {Ψ : List (Formula ℒ [] (.set :: .set :: Θ))}
    (h : List.Forall₂ (fun φ ψ => ∀ x y : M,
      ψ.satisfies ((ξ.pushFree x.val).pushFree y.val) ↔
        φ.satisfies ((η.pushFree x).pushFree y)) Φ Ψ) :
    ∀ p y : M, (PowerlessSourceFamily.family_m S T Ψ).satisfies ((ξ.pushFree p.val).pushFree y.val) ↔
      (PowerlessSourceFamily.family_m s t Φ).satisfies ((η.pushFree p).pushFree y) := by
  induction h with
  | nil => intro p y; rfl
  | cons hHead _hTail ih =>
      intro p y
      exact sum_l _ _ _ _ η ξ s t S T hs ht hHead ih p y

theorem family_output_l {Θ : SortContext ℒ} (Ψ : List (Formula ℒ [] (.set :: .set :: Θ)))
    (ξ : Env 𝒱 [] Θ) (s t : Term ℒ [] Θ .set)
    (hΨ : ∀ ψ ∈ Ψ, ∀ x : M, ∀ y, ψ.satisfies ((ξ.pushFree x.val).pushFree y) →
      PowerlessRelativeClassCorrespondence.member_l hℳ B y) :
    ∀ p : M, ∀ y, (PowerlessSourceFamily.family_m s t Ψ).satisfies ((ξ.pushFree p.val).pushFree y) →
      PowerlessRelativeClassCorrespondence.member_l hℳ B y := by
  induction Ψ with
  | nil => intro p y h; exact h.elim
  | cons ψ Ψ ih =>
      intro p y h
      exact sum_output_l (hBase := hBase) ψ (PowerlessSourceFamily.family_m s t Ψ) ξ s t
        (hΨ ψ List.mem_cons_self)
        (ih (fun χ hχ => hΨ χ (List.mem_cons_of_mem ψ hχ))) p y h

#print axioms coordinates_l
#print axioms sum_l
#print axioms family_l
#print axioms family_output_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassRequestFamilyReading
