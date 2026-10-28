import BMSConstructibleBridge.SecondOrderClassWitnessCommonLevelDerives
import BMSConstructibleBridge.SecondOrderMemberEnumeration

/-! # 全类可数分支中的任意母集收集

母集的环境枚举只用来重排实际请求，不要求它属于相对类。所有输出
仍是类内见证；共同层自身属于类，因此给出真正的类内收集对象。
该接口保留全部序数类内可数的分支条件，尚未解决截断分支。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAllCountableClassCollection

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private def insert_m {Δ : SortContext ℒ} :
    VariableSubstitution ℒ (.set :: .set :: Δ) [.set] (.set :: .set :: .set :: .set :: Δ)
  | _, .here => .fvar .here
  | _, .there .here => .bvar .here
  | _, .there (.there v) => .fvar (.there (.there (.there (.there v))))

private def body_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [.set] (.set :: .set :: .set :: .set :: Δ) :=
  φ.substitute (show Substitution ℒ [] (.set :: .set :: Δ) [.set] (.set :: .set :: .set :: .set :: Δ) from
    .map (fun v => nomatch v) insert_m)

/-- 自由槽依次为输出、内部编号、环境枚举、母集和原参数。 -/
def pullback_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [] (.set :: .set :: .set :: .set :: Δ) :=
  .existsE .set <| .conj
    (SecondOrderObjectSyntax.member_m (.bvar .here) (.fvar (.there (.there (.there .here))))) <|
      .conj (PowerlessValueBounded.formula_m (.fvar (.there (.there .here)))
        (.fvar (.there .here)) (.bvar .here)) (body_m φ)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def env_l {Δ : SortContext ℒ} (η : Env 𝒱 [] Δ) (A f : type_l hℳ) : Env 𝒱 [] (.set :: .set :: Δ) :=
  (η.pushFree A).pushFree f

theorem pullback_formula_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (A f n y : type_l hℳ) :
    (pullback_m φ).satisfies (((env_l η A f).pushFree n).pushFree y) ↔
      ∃ x, mem_l hℳ x A ∧ value_l (ℳ := 𝒱) f n x ∧ φ.satisfies ((η.pushFree x).pushFree y) := by
  have hBody (x : type_l hℳ) : (body_m φ).satisfies
      ((((env_l η A f).pushFree n).pushFree y).pushBound x) ↔ φ.satisfies ((η.pushFree x).pushFree y) := by
    rw [body_m, Formula.satisfies_substitute]
    apply Iff.of_eq
    apply congrArg (fun ξ => φ.satisfies ξ)
    apply Env.ext
    · intro s v; nomatch v
    · intro s v
      cases v with
      | here => rfl
      | there v => cases v <;> rfl
  simp only [pullback_m, Formula.satisfies, PowerlessValueBounded.formula_l,
    hBody, SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval]
  rfl

private theorem enumeration_l (K : source_coding_l hℳ) (X : type_l hℳ) (hX : ∃ x, mem_l hℳ x X) :
    ∃ f : type_l hℳ, map_l (ℳ := 𝒱) f K.omega X ∧
      ∀ x, mem_l hℳ x X → ∃ i, mem_l hℳ i K.omega ∧ value_l (ℳ := 𝒱) f i x := by
  obtain ⟨x, hx⟩ := hX
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ X
  obtain ⟨a, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
  obtain ⟨n, hn, _⟩ := (SecondOrderQuotient.mem_iff_l hℳ a A).mp hx
  obtain ⟨f, hf, _, hOnto⟩ := SecondOrderMemberEnumeration.exists_l K A n hn
  exact ⟨f, hf, hOnto⟩

theorem exists_l (K : source_coding_l hℳ) {t₁ t₂ t₃ Pair Valid P₀ S : type_l hℳ}
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B : Term ℒ [] Δ .set) (hGuard : SecondOrderCanonicalLevelDerives.guard_l (B.eval η) P₀)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega S)
    (hAll : ∀ a, SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) a →
      PowerlessRelativeOrdinalCutoff.countable_l (B.eval η) K.omega a)
    (A : type_l hℳ) (hSome : ∀ x, mem_l hℳ x A → ∃ y,
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) y ∧ φ.satisfies ((η.pushFree x).pushFree y)) :
    ∃ C : type_l hℳ, PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) C ∧
      ∀ x, mem_l hℳ x A → ∃ y, mem_l hℳ y C ∧
        PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) y ∧ φ.satisfies ((η.pushFree x).pushFree y) := by
  classical
  have hBase x hx y hy := hGuard.2.1 x y hx hy
  by_cases hNonempty : ∃ x, mem_l hℳ x A
  · obtain ⟨f, hf, hOnto⟩ := enumeration_l K A hNonempty
    let ξ := env_l η A f
    let B' := (B.weakenFree SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set
    have hB : B'.eval ξ = B.eval η := by simp only [B', ξ, env_l, Term.eval_weakenFree]
    have hSome' (n : type_l hℳ) (hn : mem_l hℳ n K.omega) : ∃ y,
        PowerlessRelativeClassCorrespondence.member_l hℳ (B'.eval ξ) y ∧
          (pullback_m φ).satisfies ((ξ.pushFree n).pushFree y) := by
      obtain ⟨x, ⟨hxA, hnx⟩, _⟩ := hf.2 n hn
      obtain ⟨y, hy, hφ⟩ := hSome x hxA
      exact ⟨y, hB.symm ▸ hy, (pullback_formula_l φ η A f n y).mpr ⟨x, hxA, hnx, hφ⟩⟩
    obtain ⟨δ, L, _, _, hL, hWitness⟩ := SecondOrderClassWitnessCommonLevel.exists_l K hCoding
      (pullback_m φ) ξ B' (hB.symm ▸ hGuard) hS (hB.symm ▸ hAll) hSome'
    rw [hB] at hL
    have hLClass := PowerlessRelativeLevelClosure.class_l hℳ hBase hL
    refine ⟨L, hLClass, fun x hx => ?_⟩
    obtain ⟨n, hn, hnx⟩ := hOnto x hx
    obtain ⟨y, hyL, hPullback⟩ := hWitness n hn
    obtain ⟨z, _, hnz, hφ⟩ := (pullback_formula_l φ η A f n y).mp hPullback
    have hzx := SecondOrderFunctionProperties.value_unique_l hℳ hf hnz hnx
    exact ⟨y, hyL, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hLClass hyL, hzx ▸ hφ⟩
  · refine ⟨K.omega, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
      (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec), fun x hx => ?_⟩
    exact False.elim (hNonempty ⟨x, hx⟩)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAllCountableClassCollection
