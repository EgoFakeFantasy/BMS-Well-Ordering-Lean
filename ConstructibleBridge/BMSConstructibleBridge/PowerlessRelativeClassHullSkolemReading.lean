import BMSConstructibleBridge.PowerlessRelativeClassRequestFamilyReading
import BMSConstructibleBridge.PowerlessRelativeClassCanonicalSkolemReading
import BMSConstructibleBridge.PowerlessClassProgramHull

/-! # 原壳区分／上邻及带标签最小见证的同值读数

原程序的 separate_m、upper_m 与实际 family_m 全部保留；只把逐项
请求读数接成同一带标签族。编码元数据、族标签及原公式参数分别核对，
不将类相对 raw 公式误认作任意 raw 公式的绝对性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassHullSkolemReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassRequestFamilyReading (coordinates_l)

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

private theorem separate_formula_l {Γ : SortContext ℒ} (η : Env 𝒩₀ [] Γ) (p y : M) :
    (PowerlessClassHullRequests.separate_m (Δ := Γ)).satisfies ((η.pushFree p).pushFree y) ↔
      ∃ x z : M, ordered_l (ℳ := 𝒩₀) x z p ∧ ¬(mem_l hℳ y.val x.val ↔ mem_l hℳ y.val z.val) := by
  simp only [PowerlessClassHullRequests.separate_m, Formula.satisfies, ordered_formula_l,
    PowerlessClassHullRequests.difference_m, SecondOrderObjectSyntax.member_m,
    Arguments.eval, Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  rfl

theorem separate_l {Γ Θ : SortContext ℒ} (η : Env 𝒩₀ [] Γ) (ξ : Env 𝒱 [] Θ) (p y : M) :
    (PowerlessClassHullRequests.separate_m (Δ := Θ)).satisfies ((ξ.pushFree p.val).pushFree y.val) ↔
      (PowerlessClassHullRequests.separate_m (Δ := Γ)).satisfies ((η.pushFree p).pushFree y) := by
  rw [PowerlessClassHullRequests.separate_formula_l, separate_formula_l]
  constructor
  · rintro ⟨x, z, hxz, hDiff⟩
    have hCoords := coordinates_l (hBase := hBase) p hxz
    let x₀ : M := ⟨x, hCoords.1⟩
    let z₀ : M := ⟨z, hCoords.2⟩
    exact ⟨x₀, z₀, (PowerlessRelativeClassFunctionAbsolute.ordered_l
      (hBase := hBase) x₀ z₀ p).mpr hxz, hDiff⟩
  · rintro ⟨x, z, hxz, hDiff⟩
    exact ⟨x.val, z.val, (PowerlessRelativeClassFunctionAbsolute.ordered_l
      (hBase := hBase) x z p).mp hxz, hDiff⟩

theorem separate_output_l {Θ : SortContext ℒ} (ξ : Env 𝒱 [] Θ) (p : M)
    (y : SecondOrderQuotient.type_l hℳ)
    (h : (PowerlessClassHullRequests.separate_m (Δ := Θ)).satisfies ((ξ.pushFree p.val).pushFree y)) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B y := by
  classical
  obtain ⟨x, z, hxz, hDiff⟩ := (PowerlessClassHullRequests.separate_formula_l ξ p.val y).mp h
  have hCoords := coordinates_l (hBase := hBase) p hxz
  by_cases hyx : mem_l hℳ y x
  · exact PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hCoords.1 hyx
  · have hyz : mem_l hℳ y z := by
      by_contra hyz
      exact hDiff (iff_of_false hyx hyz)
    exact PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hCoords.2 hyz

theorem upper_l {Γ Θ : SortContext ℒ} (η : Env 𝒩₀ [] Γ) (ξ : Env 𝒱 [] Θ) (p y : M) :
    (PowerlessClassHullRequests.upper_m (Δ := Θ)).satisfies ((ξ.pushFree p.val).pushFree y.val) ↔
      (PowerlessClassHullRequests.upper_m (Δ := Γ)).satisfies ((η.pushFree p).pushFree y) := by
  rw [PowerlessClassHullRequests.upper_formula_l]
  simp only [PowerlessClassHullRequests.upper_m, pair_formula_l, Term.eval,
    Env.pushFree_here, Env.pushFree_there]
  exact (PowerlessRelativeClassFunctionAbsolute.pair_l (hBase := hBase) p p y).symm

theorem upper_output_l {Θ : SortContext ℒ} (ξ : Env 𝒱 [] Θ) (p : M)
    (y : SecondOrderQuotient.type_l hℳ)
    (h : (PowerlessClassHullRequests.upper_m (Δ := Θ)).satisfies ((ξ.pushFree p.val).pushFree y)) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B y :=
  PowerlessRelativeClassPair.pair_l hℳ hBase p.property p.property
    ((PowerlessClassHullRequests.upper_formula_l ξ p.val y).mp h)

theorem family_l {Γ Θ : SortContext ℒ}
    (η : Env 𝒩₀ [] Γ) (ξ : Env 𝒱 [] Θ)
    (s t : Term ℒ [] Γ .set) (S T : Term ℒ [] Θ .set)
    (hs : (s.eval η).val = S.eval ξ) (ht : (t.eval η).val = T.eval ξ)
    {Φ : List (Formula ℒ [] (.set :: .set :: Γ))}
    {Ψ : List (Formula ℒ [] (.set :: .set :: Θ))}
    (h : List.Forall₂ (fun φ ψ => ∀ x y : M,
      ψ.satisfies ((ξ.pushFree x.val).pushFree y.val) ↔
        φ.satisfies ((η.pushFree x).pushFree y)) Φ Ψ) :
    ∀ p y : M, (PowerlessClassHullRequests.family_m Ψ S T).satisfies ((ξ.pushFree p.val).pushFree y.val) ↔
      (PowerlessClassHullRequests.family_m Φ s t).satisfies ((η.pushFree p).pushFree y) :=
  PowerlessRelativeClassRequestFamilyReading.family_l η ξ s t S T hs ht
    (List.Forall₂.cons (fun p y => separate_l η ξ p y)
      (List.Forall₂.cons (fun p y => upper_l η ξ p y) h))

theorem family_output_l {Θ : SortContext ℒ}
    (Ψ : List (Formula ℒ [] (.set :: .set :: Θ))) (ξ : Env 𝒱 [] Θ)
    (s t : Term ℒ [] Θ .set)
    (hΨ : ∀ ψ ∈ Ψ, ∀ x : M, ∀ y, ψ.satisfies ((ξ.pushFree x.val).pushFree y) →
      PowerlessRelativeClassCorrespondence.member_l hℳ B y) :
    ∀ p : M, ∀ y, (PowerlessClassHullRequests.family_m Ψ s t).satisfies ((ξ.pushFree p.val).pushFree y) →
      PowerlessRelativeClassCorrespondence.member_l hℳ B y := by
  apply PowerlessRelativeClassRequestFamilyReading.family_output_l (hBase := hBase)
  intro ψ hψ p y h
  rcases List.mem_cons.mp hψ with rfl | hψ
  · exact separate_output_l (hBase := hBase) ξ p y h
  · rcases List.mem_cons.mp hψ with rfl | hψ
    · exact upper_output_l (hBase := hBase) ξ p y h
    · exact hΨ ψ hψ p y h

/-- 原带标签总族作为同一 raw 请求，输出关系与类内算子逐点相同。 -/
theorem relation_l (K : source_coding_l hℳ) {Γ Θ : SortContext ℒ}
    (η : Env 𝒩₀ [] Γ) (ξ : Env 𝒱 [] Θ)
    (s t : Term ℒ [] Γ .set) (S T : Term ℒ [] Θ .set)
    (hs : (s.eval η).val = S.eval ξ) (ht : (t.eval η).val = T.eval ξ)
    {Φ : List (Formula ℒ [] (.set :: .set :: Γ))}
    {Ψ : List (Formula ℒ [] (.set :: .set :: Θ))}
    (h : List.Forall₂ (fun φ ψ => ∀ x y : M,
      ψ.satisfies ((ξ.pushFree x.val).pushFree y.val) ↔
        φ.satisfies ((η.pushFree x).pushFree y)) Φ Ψ)
    (hΨ : ∀ ψ ∈ Ψ, ∀ x : M, ∀ y, ψ.satisfies ((ξ.pushFree x.val).pushFree y) →
      PowerlessRelativeClassCorrespondence.member_l hℳ B y)
    (ω P₀ x y : M) (hω : ω.val = K.omega)
    {t₁ t₂ t₃ Pair Valid : SecondOrderQuotient.type_l hℳ}
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
    (hGuard : SecondOrderCanonicalLevelDerives.guard_l B P₀.val) :
    PowerlessCanonicalCodedSkolemSyntax.relation_l (𝒩 := 𝒩₀)
      (PowerlessClassHullRequests.family_m Φ s t) η
      ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ ω P₀ x y ↔
    SecondOrderCanonicalClassSkolem.relation_l (PowerlessClassHullRequests.family_m Ψ S T)
      ξ K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val
      t₁ t₂ t₃ Pair Valid B P₀.val x.val y.val :=
  PowerlessRelativeClassCanonicalSkolemReading.transfer_l K _ _ η ξ ω P₀ x y
    hω hCoding hGuard.1 hGuard.2.2.1 hGuard.2.2.2
    (fun z => family_l η ξ s t S T hs ht h x z)
    (family_output_l (hBase := hBase) Ψ ξ S T hΨ x)

#print axioms separate_l
#print axioms upper_l
#print axioms family_l
#print axioms family_output_l
#print axioms relation_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassHullSkolemReading
