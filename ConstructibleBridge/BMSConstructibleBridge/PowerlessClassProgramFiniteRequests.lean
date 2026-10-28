import BMSConstructibleBridge.PowerlessClassPackedRequests
import BMSConstructibleBridge.PowerlessSourceClassPairing
import BMSConstructibleBridge.PowerlessClassProgramRequests

/-! # 同一实际程序的原有限元数类请求闭包

原公式族和原参数替换决定实际打包请求族；同一个 Class 最小见证算子
及原全码域产生虚拟壳。配对、调用和总定义性均由原 Z₂ 构造规格取得，
没有把请求闭包或完整源理论加入前提。这里只读出原类结构的有限请求
闭包；有限元素性的对象句、凝聚与最终良序句仍须后续装配。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassProgramFiniteRequests

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderCanonicalLevelDerives (guard_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessSourceClass.structure_l PowerlessSourceClass.type_l

universe u

def domain_m {Δ : SortContext ℒ} (B : Term ℒ [] Δ .set) : Formula ℒ [] (.set :: Δ) :=
  PowerlessRelativeHierarchySyntax.class_m
    (Term.weakenFree (σ := ℒ) SetTheory.SetSort.set B) (.fvar .here)

def family_m {Γ Δ : SortContext ℒ}
    (Φ : List (Σ n : Nat, Formula ℒ [] (.set :: (List.replicate n .set ++ Γ))))
    (B : Term ℒ [] Δ .set) (ν : VariableSubstitution ℒ Γ [] Δ) :
    List (Formula ℒ [] (.set :: .set :: Δ)) :=
  PowerlessClassPackedRequests.family_m (domain_m B) Φ ν

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "ε" => SecondOrderQuotient.mem_l hℳ

theorem domain_formula_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (ξ : Env 𝒱 [] Δ) (B : Term ℒ [] Δ .set) (x : Raw) :
    (domain_m B).satisfies (ξ.pushFree x) ↔
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval ξ) x := by
  simp only [domain_m, PowerlessRelativeHierarchySemantics.class_formula_l K,
    Term.eval_weakenFree, Term.eval, Env.pushFree_here]
  rfl

def image_l {Γ Δ : SortContext ℒ}
    (Φ : List (Σ n : Nat, Formula ℒ [] (.set :: (List.replicate n .set ++ Γ))))
    (ν : VariableSubstitution ℒ Γ [] Δ) (ξ : Env 𝒱 [] Δ)
    (ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a P s t : Term ℒ [] Δ .set) : Raw → Prop :=
  PowerlessRelativeFiniteProgramVirtualClosure.image_l false
    (PowerlessClassProgramHull.operator_m (family_m Φ B ν) ω e r₁ r₂ r₃ Pair Valid B P₀ s t)
    ξ (B.eval ξ) (C.eval ξ) (ω.eval ξ) (Q.eval ξ) (e.eval ξ)
      (t₀.eval ξ) (t₁.eval ξ) (t₂.eval ξ) (a.eval ξ) (P.eval ξ)

/-- 原构造规格消去打包请求闭包的全部配对／调用前提。 -/
theorem requests_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (Φ : List (Σ n : Nat, Formula ℒ [] (.set :: (List.replicate n .set ++ Γ))))
    (ν : VariableSubstitution ℒ Γ [] Δ) (ξ : Env 𝒱 [] Δ)
    (ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a S P s t : Term ℒ [] Δ .set)
    (hCoding : SecondOrderComparisonStageTotal.coding_l K (r₁.eval ξ) (r₂.eval ξ)
      (r₃.eval ξ) (Pair.eval ξ) (Valid.eval ξ))
    (hω : SecondOrderOmega.omega_l hℳ (ω.eval ξ))
    (hGuard : guard_l (B.eval ξ) (P₀.eval ξ))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval ξ) (C.eval ξ))
    (hωC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval ξ) (ω.eval ξ))
    (hQ : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval ξ) (Q.eval ξ))
    (he : ∀ x, ¬ε x (e.eval ξ))
    (ha : PowerlessRelativeFiniteProgramStep.record_l (e.eval ξ) (e.eval ξ) (e.eval ξ) (a.eval ξ))
    (ht : t₀.eval ξ ≠ t₁.eval ξ ∧ t₀.eval ξ ≠ t₂.eval ξ ∧ t₁.eval ξ ≠ t₂.eval ξ)
    (hAlphabet : ∀ q, ε q (Q.eval ξ) ↔
      PowerlessRelativeFiniteProgramAlphabet.instruction_l (C.eval ξ) (ω.eval ξ)
        (t₀.eval ξ) (t₁.eval ξ) (t₂.eval ξ) q)
    (hDomain : PowerlessRelativeFiniteProgramDomain.domain_l (B.eval ξ) (ω.eval ξ)
      (Q.eval ξ) (S.eval ξ) (P.eval ξ))
    (hBC : ε (B.eval ξ) (C.eval ξ)) (hs : ε (s.eval ξ) (C.eval ξ))
    (htC : ε (t.eval ξ) (C.eval ξ)) (hst : s.eval ξ ≠ t.eval ξ)
    {hP : ∃ x, PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval ξ) x}
    (η : Env (PowerlessSourceClass.structure_l (ℳ := 𝒱)
      (fun x => PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval ξ) x) hP) [] Γ)
    (hν : ∀ v : Variable Γ .set, (ν v).eval ξ = (η.freeVal v).val) :
    PowerlessSourcePredicateRequests.closed_l Φ η
      (fun x => image_l Φ ν ξ ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a P s t x.val) := by
  let D := domain_m B
  let Ψ := family_m Φ B ν
  let A : Raw → Prop := fun x => PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval ξ) x
  let 𝒩 := PowerlessSourceClass.structure_l (ℳ := 𝒱) A hP
  let I := image_l Φ ν ξ ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a P s t
  have hB : ∀ x, ε x (B.eval ξ) → ∀ z, ε z x → ε z (B.eval ξ) :=
    fun x hx z hz => hGuard.2.1 x z hx hz
  obtain ⟨_, hClass, hSeed, hPair, hCall, hTotal⟩ := PowerlessClassProgramHull.closure_l
    K Ψ ξ ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a S P s t
      hCoding hω hGuard hC hωC hQ he ha ht hAlphabet hDomain hBC
  have hTrans : ∀ x, A x → ∀ z, member_l 𝒱 z x → A z :=
    fun _ hx _ hz => PowerlessRelativeClassCorrespondence.transitive_l hℳ hB hx hz
  have hAPair : ∀ x y p, A x → A y → ThirdOrderSemantics.pair_l (ℳ := 𝒱) x y p → A p :=
    fun _ _ _ hx hy hp => PowerlessRelativeClassPair.pair_l hℳ hB hx hy hp
  have hPairRaw : ∀ x y : Raw, ∃ p, ThirdOrderSemantics.pair_l (ℳ := 𝒱) x y p :=
    SecondOrderPairObjects.pair_exists_l hℳ
  have hPairClass : ∀ x y : PowerlessSourceClass.type_l (ℳ := 𝒱) A,
      ∃ p, ordered_l (ℳ := 𝒩) x y p :=
    PowerlessSourceClassPairing.ordered_exists_l hTrans hAPair hPairRaw
  have hClosed : ∀ x y p : PowerlessSourceClass.type_l (ℳ := 𝒱) A,
      I x.val → I y.val → ordered_l (ℳ := 𝒩) x y p → I p.val := by
    intro x y p hx hy hp
    obtain ⟨q, hq, hqp⟩ := hPair x.val y.val hx hy
    have hqEq : q = p.val := SecondOrderPairObjects.ordered_unique_l hℳ hqp
      (PowerlessSourceClassPairing.ordered_raw_l hTrans hp)
    exact hqEq ▸ hq
  have hCaptured : ∀ ψ ∈ Ψ, ∀ p, I p →
      (∃ y, A y ∧ ψ.satisfies ((ξ.pushFree p).pushFree y)) →
        ∃ y, I y ∧ ψ.satisfies ((ξ.pushFree p).pushFree y) := by
    intro ψ hψ p hp hSome
    exact PowerlessVirtualHullRequests.witness_l Ψ ξ s t I hst (hSeed _ hs) (hSeed _ htC)
      hPair hCall hTotal ψ hψ p hp hSome
  exact PowerlessClassPackedRequests.family_l D Φ ν ξ η hν
    (domain_formula_l K ξ B) I hClass
    ⟨B.eval ξ, PowerlessRelativeClassCorrespondence.base_object_l hℳ hB⟩
    (hSeed _ hBC) hPairClass hClosed hCaptured

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassProgramFiniteRequests
