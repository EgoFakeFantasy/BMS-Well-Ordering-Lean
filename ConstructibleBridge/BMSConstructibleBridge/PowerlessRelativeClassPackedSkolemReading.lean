import BMSConstructibleBridge.PowerlessRelativeClassCanonicalSkolemReading
import BMSConstructibleBridge.PowerlessClassProgramFiniteRequests
import BMSConstructibleBridge.PowerlessRelativeClassSource

/-! # 原程序打包请求的类内最小见证读数

使用现有实际 family_m 中的逐项 form_m，而非另造 raw 请求。
有限元数、原公式及原参数替换保持不变；原编码元数据只留在 raw
环境中，不添加它们属于 Class 的前提。这里只接逐条请求，
原带标签请求总族及内部执行轨迹仍须后续装配。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassPackedSkolemReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  structure_l type_l PowerlessSourceClass.structure_l PowerlessSourceClass.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ z, mem_l hℳ z B → ∀ t, mem_l hℳ t z → mem_l hℳ t B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => structure_l hℳ B hBase
local notation "M" => type_l hℳ B

theorem request_l (K : source_coding_l hℳ) {Γ Θ : SortContext ℒ}
    (n : Nat) (φ : Formula ℒ [] (.set :: (List.replicate n .set ++ Γ)))
    (b : Term ℒ [] Θ .set) (ν : VariableSubstitution ℒ Γ [] Θ)
    (ξ : Env 𝒱 [] Θ) (η : Env 𝒩₀ [] Γ) (hb : b.eval ξ = B)
    (hν : ∀ v : Variable Γ .set, (ν v).eval ξ = (η.freeVal v).val) (p y : M) :
    (PowerlessClassPackedRequests.form_m (PowerlessClassProgramFiniteRequests.domain_m b) n φ ν).satisfies
      ((ξ.pushFree p.val).pushFree y.val) ↔
      (PowerlessSourceTuple.form_m n φ).satisfies ((η.pushFree p).pushFree y) := by
  have hD (z : SecondOrderQuotient.type_l hℳ) :
      (PowerlessClassProgramFiniteRequests.domain_m b).satisfies (ξ.pushFree z) ↔
      PowerlessRelativeClassCorrespondence.member_l hℳ B z := by
    rw [PowerlessClassProgramFiniteRequests.domain_formula_l K, hb]
  let hP : ∃ z, PowerlessRelativeClassCorrespondence.member_l hℳ B z :=
    ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩
  let ζ : Env (PowerlessSourceClass.structure_l (ℳ := 𝒱)
      (PowerlessRelativeClassCorrespondence.member_l hℳ B) hP) [] Γ :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with | .set => ⟨(η.freeVal v).val, (η.freeVal v).property⟩ }
  let p₀ : PowerlessSourceClass.type_l (ℳ := 𝒱)
    (PowerlessRelativeClassCorrespondence.member_l hℳ B) := ⟨p.val, p.property⟩
  let y₀ : PowerlessSourceClass.type_l (ℳ := 𝒱)
    (PowerlessRelativeClassCorrespondence.member_l hℳ B) := ⟨y.val, y.property⟩
  have hPacked := PowerlessClassPackedRequests.formula_l
    («𝒱» := 𝒱) (P := PowerlessRelativeClassCorrespondence.member_l hℳ B)
    (hP := hP) (PowerlessClassProgramFiniteRequests.domain_m b) n φ ν ξ ζ hν hD p₀ y₀
  have hEnv : PowerlessRelativeClassSource.env_l (hBase := hBase) (Δ := .set :: .set :: Γ)
      ((ζ.pushFree p₀).pushFree y₀) = (η.pushFree p).pushFree y := by
    apply Env.ext
    · intro _ v; nomatch v
    · intro s v
      cases s
      cases v with
      | here => exact Subtype.ext rfl
      | there v => cases v with
        | here => exact Subtype.ext rfl
        | there v => exact Subtype.ext rfl
  have hRead := PowerlessRelativeClassSource.formula_l (hBase := hBase)
    (PowerlessSourceTuple.form_m n φ) ((ζ.pushFree p₀).pushFree y₀)
  rw [hEnv] at hRead
  exact hPacked.trans hRead.symm

theorem output_class_l (K : source_coding_l hℳ) {Γ Θ : SortContext ℒ}
    (n : Nat) (φ : Formula ℒ [] (.set :: (List.replicate n .set ++ Γ)))
    (b : Term ℒ [] Θ .set) (ν : VariableSubstitution ℒ Γ [] Θ)
    (ξ : Env 𝒱 [] Θ) (hb : b.eval ξ = B) (p y : SecondOrderQuotient.type_l hℳ)
    (h : (PowerlessClassPackedRequests.form_m
      (PowerlessClassProgramFiniteRequests.domain_m b) n φ ν).satisfies
        ((ξ.pushFree p).pushFree y)) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B y := by
  let D := PowerlessClassProgramFiniteRequests.domain_m b
  have hFree : PowerlessSourceClass.free_l
      ((ξ.pushFree (sort := SetTheory.SetSort.set) p).pushFree (sort := SetTheory.SetSort.set) y) =
      (ξ.pushFree (sort := SetTheory.SetSort.set) p).pushFree (sort := SetTheory.SetSort.set) y := by
    apply Env.ext
    · intro _ v; nomatch v
    · intro _ v; rfl
  have hDomain := (PowerlessSourceClass.domain_formula_l (PowerlessClassPackedRequests.domain_m D)
    ((ξ.pushFree p).pushFree y) (.fvar .here)).mp h.1
  simp only [hFree, Term.eval, Env.pushFree_here] at hDomain
  have hD := (PowerlessClassPackedRequests.domain_formula_l D ξ p y y).mp hDomain
  have hClass := (PowerlessClassProgramFiniteRequests.domain_formula_l K ξ b y).mp hD
  rw [hb] at hClass
  exact hClass

theorem relation_l (K : source_coding_l hℳ) {Γ Θ : SortContext ℒ}
    (n : Nat) (φ : Formula ℒ [] (.set :: (List.replicate n .set ++ Γ)))
    (b : Term ℒ [] Θ .set) (ν : VariableSubstitution ℒ Γ [] Θ)
    (ξ : Env 𝒱 [] Θ) (η : Env 𝒩₀ [] Γ) (hb : b.eval ξ = B)
    (hν : ∀ v : Variable Γ .set, (ν v).eval ξ = (η.freeVal v).val)
    (ω P₀ x y : M) (hω : ω.val = K.omega)
    {t₁ t₂ t₃ Pair Valid : SecondOrderQuotient.type_l hℳ}
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
    (hGuard : SecondOrderCanonicalLevelDerives.guard_l B P₀.val) :
    PowerlessCanonicalCodedSkolemSyntax.relation_l (𝒩 := 𝒩₀)
      (PowerlessSourceTuple.form_m n φ) η
      ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ ω P₀ x y ↔
    SecondOrderCanonicalClassSkolem.relation_l
      (PowerlessClassPackedRequests.form_m (PowerlessClassProgramFiniteRequests.domain_m b) n φ ν)
      ξ K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val
      t₁ t₂ t₃ Pair Valid B P₀.val x.val y.val :=
  PowerlessRelativeClassCanonicalSkolemReading.transfer_l K (PowerlessSourceTuple.form_m n φ) _
    η ξ ω P₀ x y hω hCoding hGuard.1 hGuard.2.2.1 hGuard.2.2.2
    (fun z => request_l K n φ b ν ξ η hb hν x z)
    (fun z hz => output_class_l K n φ b ν ξ hb x.val z hz)

#print axioms request_l
#print axioms output_class_l
#print axioms relation_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassPackedSkolemReading
