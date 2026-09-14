import BMSConstructibleBridge.PowerlessSourceCoverage

/-!
# 实际求值子集算子的基本集合闭包

用原源公式及实际参数环境构造指定子集，不将外部存在性误作域内成员性。
配对只要求参数属于域；后继与并的见证范围另用域传递性控制。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessOperatorClosure

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ A D : carrier_l ℳ} (hω : omega_l ω)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
  (hD : PowerlessEvaluationOperator.operator_l ω e T t₁ t₂ t₃ A D)

include hℳ hω ht hT hD

theorem specified_l {hA : ∃ a, member_l ℳ a A} {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ (.set :: Γ) Δ) (η : Env (structure_l A hA) Γ Δ)
    {B : carrier_l ℳ} (hB : ∀ x, member_l ℳ x B ↔
      ∃ hx : member_l ℳ x A, Formula.satisfies (η.pushBound ⟨x, hx⟩) φ) :
    member_l ℳ B D := by
  obtain ⟨C, hC, h⟩ := PowerlessSourceCoverage.operator_l hℳ hω ht hT hD φ η
  have h₀ := (PowerlessTheory.ext_l hℳ).eq_of_same_members C B (fun x => (h x).trans (hB x).symm)
  exact h₀ ▸ hC

theorem empty_l {z : carrier_l ℳ} (hz : PowerlessNatural.zero_l z) : member_l ℳ z D := by
  classical
  by_cases hA : ∃ a, member_l ℳ a A
  · apply specified_l hℳ hω ht hT hD (hA := hA) (.falsum : Formula ℒ [.set] []) Env.empty
    intro x
    exact ⟨fun hx => (hz x hx).elim, fun ⟨_, h⟩ => h.elim⟩
  · exact (PowerlessEvaluationOperator.empty_l hℳ hω hD (fun x hx => hA ⟨x, hx⟩) z).mpr hz

theorem pair_l {a b p : carrier_l ℳ} (ha : member_l ℳ a A) (hb : member_l ℳ b A)
    (hp : ThirdOrderSemantics.pair_l a b p) : member_l ℳ p D := by
  let hA : ∃ x, member_l ℳ x A := ⟨a, ha⟩
  let η : Env (structure_l A hA) [.set, .set] [] :=
    ((Env.empty (σ := ℒ) (M := structure_l A hA)).pushBound
      (sort := SetTheory.SetSort.set) ⟨b, hb⟩).pushBound ⟨a, ha⟩
  let φ : Formula ℒ [.set, .set, .set] [] :=
    .disj (.equal (.bvar .here) (.bvar (.there .here)))
      (.equal (.bvar .here) (.bvar (.there (.there .here))))
  apply specified_l hℳ hω ht hT hD φ η
  intro x
  change member_l ℳ x p ↔ ∃ hx : member_l ℳ x A,
    (⟨x, hx⟩ : type_l A) = ⟨a, ha⟩ ∨ (⟨x, hx⟩ : type_l A) = ⟨b, hb⟩
  constructor
  · intro hx
    rcases (hp x).mp hx with h | h
    · subst x
      exact ⟨ha, Or.inl rfl⟩
    · subst x
      exact ⟨hb, Or.inr rfl⟩
  · rintro ⟨_, h | h⟩
    · exact (hp x).mpr (Or.inl (congrArg Subtype.val h))
    · exact (hp x).mpr (Or.inr (congrArg Subtype.val h))

theorem successor_l {a b : carrier_l ℳ} (hAT : PowerlessNaturalOrder.transitive_l A)
    (ha : member_l ℳ a A) (hb : PowerlessNatural.successor_l a b) : member_l ℳ b D := by
  let hA : ∃ x, member_l ℳ x A := ⟨a, ha⟩
  let η : Env (structure_l A hA) [.set] [] := Env.empty.pushBound ⟨a, ha⟩
  let φ : Formula ℒ [.set, .set] [] :=
    .disj (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there .here)))
      (.equal (.bvar .here) (.bvar (.there .here)))
  apply specified_l hℳ hω ht hT hD φ η
  intro x
  change member_l ℳ x b ↔ ∃ hx : member_l ℳ x A,
    member_l ℳ x a ∨ (⟨x, hx⟩ : type_l A) = ⟨a, ha⟩
  constructor
  · intro hx
    rcases (hb x).mp hx with h | h
    · exact ⟨hAT a x ha h, Or.inl h⟩
    · subst x
      exact ⟨ha, Or.inr rfl⟩
  · rintro ⟨_, h | h⟩
    · exact (hb x).mpr (Or.inl h)
    · exact (hb x).mpr (Or.inr (congrArg Subtype.val h))

theorem union_l {a b : carrier_l ℳ} (hAT : PowerlessNaturalOrder.transitive_l A)
    (ha : member_l ℳ a A)
    (hb : ∀ x, member_l ℳ x b ↔ ∃ y, member_l ℳ y a ∧ member_l ℳ x y) : member_l ℳ b D := by
  let hA : ∃ x, member_l ℳ x A := ⟨a, ha⟩
  let η : Env (structure_l A hA) [.set] [] := Env.empty.pushBound ⟨a, ha⟩
  let φ : Formula ℒ [.set, .set] [] :=
    .existsE .set (.conj
      (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there (.there .here))))
      (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (.bvar .here)))
  apply specified_l hℳ hω ht hT hD φ η
  intro x
  change member_l ℳ x b ↔ ∃ hx : member_l ℳ x A,
    ∃ y : type_l A, member_l ℳ y.val a ∧ member_l ℳ x y.val
  constructor
  · intro hx
    obtain ⟨y, hy, h⟩ := (hb x).mp hx
    have hyA := hAT a y ha hy
    exact ⟨hAT y x hyA h, ⟨y, hyA⟩, hy, h⟩
  · rintro ⟨_, y, hy, h⟩
    exact (hb x).mpr ⟨y.val, hy, h⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessOperatorClosure
