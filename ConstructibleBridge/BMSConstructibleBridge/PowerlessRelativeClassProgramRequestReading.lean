import BMSConstructibleBridge.PowerlessRelativeClassPackedSkolemReading
import BMSConstructibleBridge.PowerlessRelativeClassHullSkolemReading

/-! # 实际有限程序请求族的原参数归一读数

原 family_m 的每个有限元数、请求 AST、列表次序及参数替换均保持。
类内正文只使用原参数与类内标签，原 raw 环境中的其余规范编码不必
属于 Class。逐项读数不是新增假设，而是从原打包公式规格证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassProgramRequestReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

def parameters_m {Γ Δ : SortContext ℒ} (ν : VariableSubstitution ℒ Γ [] Δ) :
    Substitution ℒ [] Γ [] Δ := .map (fun v => nomatch v) ν

/-- 原元组请求仅代入原参数，不再重复做 Class 相对化。 -/
def form_m {Γ Δ : SortContext ℒ} (n : Nat)
    (φ : Formula ℒ [] (.set :: (List.replicate n .set ++ Γ)))
    (ν : VariableSubstitution ℒ Γ [] Δ) : Formula ℒ [] (.set :: .set :: Δ) :=
  (PowerlessSourceTuple.form_m n φ).substitute
    (parameters_m (PowerlessClassPackedRequests.binding_m ν))

def family_m {Γ Δ : SortContext ℒ}
    (Φ : List (Σ n : Nat, Formula ℒ [] (.set :: (List.replicate n .set ++ Γ))))
    (ν : VariableSubstitution ℒ Γ [] Δ) : List (Formula ℒ [] (.set :: .set :: Δ)) :=
  Φ.map fun p => form_m p.1 p.2 ν

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (n : Nat) (φ : Formula ℒ [] (.set :: (List.replicate n .set ++ Γ)))
    (ν : VariableSubstitution ℒ Γ [] Δ) (η : Env 𝒩 [] Δ) (p y : carrier_l 𝒩) :
    (form_m n φ ν).satisfies ((η.pushFree p).pushFree y) ↔
      (PowerlessSourceTuple.form_m n φ).satisfies
        (((η.pullback (parameters_m ν)).pushFree p).pushFree y) := by
  rw [form_m, Formula.satisfies_substitute]
  have hEnv : ((η.pushFree p).pushFree y).pullback
      (parameters_m (PowerlessClassPackedRequests.binding_m ν)) =
      ((η.pullback (parameters_m ν)).pushFree p).pushFree y := by
    apply Env.ext
    · intro _ v; nomatch v
    · intro s v
      cases s
      cases v with
      | here => rfl
      | there v => cases v with
        | here => rfl
        | there v =>
            simp only [parameters_m, Env.pullback, PowerlessClassPackedRequests.binding_m,
              Term.eval_weakenFree, Env.pushFree_there]
  rw [hEnv]

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ z, mem_l hℳ z B → ∀ t, mem_l hℳ t z → mem_l hℳ t B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => structure_l hℳ B hBase
local notation "M" => type_l hℳ B

include hBase

theorem request_l (K : source_coding_l hℳ) {Γ Δ Θ : SortContext ℒ}
    (n : Nat) (φ : Formula ℒ [] (.set :: (List.replicate n .set ++ Γ)))
    (b : Term ℒ [] Θ .set) (σ : VariableSubstitution ℒ Γ [] Δ)
    (ν : VariableSubstitution ℒ Γ [] Θ) (η : Env 𝒩₀ [] Δ) (ξ : Env 𝒱 [] Θ)
    (hb : b.eval ξ = B) (hν : ∀ v : Variable Γ .set, (ν v).eval ξ = ((σ v).eval η).val) (p y : M) :
    (PowerlessClassPackedRequests.form_m (PowerlessClassProgramFiniteRequests.domain_m b) n φ ν).satisfies
      ((ξ.pushFree p.val).pushFree y.val) ↔
      (form_m n φ σ).satisfies ((η.pushFree p).pushFree y) :=
  (PowerlessRelativeClassPackedSkolemReading.request_l K n φ b ν ξ
    (η.pullback (parameters_m σ)) hb hν p y).trans
      (formula_l n φ σ η p y).symm

theorem family_l (K : source_coding_l hℳ) {Γ Δ Θ : SortContext ℒ}
    (Φ : List (Σ n : Nat, Formula ℒ [] (.set :: (List.replicate n .set ++ Γ))))
    (b : Term ℒ [] Θ .set) (σ : VariableSubstitution ℒ Γ [] Δ)
    (ν : VariableSubstitution ℒ Γ [] Θ) (η : Env 𝒩₀ [] Δ) (ξ : Env 𝒱 [] Θ)
    (hb : b.eval ξ = B) (hν : ∀ v : Variable Γ .set, (ν v).eval ξ = ((σ v).eval η).val) :
    List.Forall₂ (fun φ ψ => ∀ x y : M,
      ψ.satisfies ((ξ.pushFree x.val).pushFree y.val) ↔
        φ.satisfies ((η.pushFree x).pushFree y))
      (family_m Φ σ) (PowerlessClassProgramFiniteRequests.family_m Φ b ν) := by
  induction Φ with
  | nil => exact List.Forall₂.nil
  | cons p Φ ih =>
      exact List.Forall₂.cons (fun x y => request_l K p.1 p.2 b σ ν η ξ hb hν x y) ih

omit hBase in
theorem family_output_l (K : source_coding_l hℳ) {Γ Θ : SortContext ℒ}
    (Φ : List (Σ n : Nat, Formula ℒ [] (.set :: (List.replicate n .set ++ Γ))))
    (b : Term ℒ [] Θ .set) (ν : VariableSubstitution ℒ Γ [] Θ) (ξ : Env 𝒱 [] Θ)
    (hb : b.eval ξ = B) :
    ∀ ψ ∈ PowerlessClassProgramFiniteRequests.family_m Φ b ν, ∀ x : M, ∀ y,
      ψ.satisfies ((ξ.pushFree x.val).pushFree y) →
        PowerlessRelativeClassCorrespondence.member_l hℳ B y := by
  intro ψ hψ x y h
  obtain ⟨p, _hp, rfl⟩ := List.mem_map.mp hψ
  exact PowerlessRelativeClassPackedSkolemReading.output_class_l K p.1 p.2 b ν ξ hb x.val y h

theorem relation_l (K : source_coding_l hℳ) {Γ Δ Θ : SortContext ℒ}
    (Φ : List (Σ n : Nat, Formula ℒ [] (.set :: (List.replicate n .set ++ Γ))))
    (b : Term ℒ [] Θ .set) (σ : VariableSubstitution ℒ Γ [] Δ)
    (ν : VariableSubstitution ℒ Γ [] Θ) (η : Env 𝒩₀ [] Δ) (ξ : Env 𝒱 [] Θ)
    (hb : b.eval ξ = B) (hν : ∀ v : Variable Γ .set, (ν v).eval ξ = ((σ v).eval η).val)
    (s t : Term ℒ [] Δ .set) (S T : Term ℒ [] Θ .set)
    (hs : (s.eval η).val = S.eval ξ) (ht : (t.eval η).val = T.eval ξ)
    (ω P₀ x y : M) (hω : ω.val = K.omega)
    {t₁ t₂ t₃ Pair Valid : SecondOrderQuotient.type_l hℳ}
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
    (hGuard : SecondOrderCanonicalLevelDerives.guard_l B P₀.val) :
    PowerlessCanonicalCodedSkolemSyntax.relation_l (𝒩 := 𝒩₀)
      (PowerlessClassHullRequests.family_m (family_m Φ σ) s t) η
      ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ ω P₀ x y ↔
    SecondOrderCanonicalClassSkolem.relation_l
      (PowerlessClassHullRequests.family_m (PowerlessClassProgramFiniteRequests.family_m Φ b ν) S T)
      ξ K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val
      t₁ t₂ t₃ Pair Valid B P₀.val x.val y.val :=
  PowerlessRelativeClassHullSkolemReading.relation_l K η ξ s t S T hs ht
    (family_l K Φ b σ ν η ξ hb hν)
    (family_output_l K Φ b ν ξ hb) ω P₀ x y hω hCoding hGuard

#print axioms formula_l
#print axioms request_l
#print axioms family_l
#print axioms family_output_l
#print axioms relation_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassProgramRequestReading
