import BMSConstructibleBridge.PowerlessExtension
import BMSConstructibleBridge.PowerlessNaturalStep

/-!
# 纯定义算子的内部有限递归轨迹

`trace_m φ` 是原集合语言中的实际公式，长度参数来自模型内部。
它要求定义域恰为长度的后继、给定初值以及此前所有后继方程。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessTrace

open Logic FirstOrder ThirdOrderSemantics PowerlessNatural

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

/-- 自由变量依次是轨迹、长度、零、初值，随后保留原算子的所有参数。 -/
def trace_m {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ)) :
    Formula ℒ [] (.set :: .set :: .set :: .set :: Γ) :=
  let σ : Substitution ℒ [] (.set :: .set :: Γ)
      [.set, .set, .set, .set, .set, .set] (.set :: .set :: .set :: .set :: Γ) :=
    .map (fun v => nomatch v) (fun {s} v => match s, v with
      | .set, .here => .bvar .here
      | .set, .there .here => .bvar (.there .here)
      | .set, .there (.there v) => .fvar (.there (.there (.there (.there v)))))
  .existsE .set (.existsE .set (.conj
    (PowerlessNaturalStep.successor_m (.fvar (.there .here)) (.bvar (.there .here)))
    (.conj (SecondOrderObjectSyntax.map_m (.fvar .here) (.bvar (.there .here)) (.bvar .here))
      (.conj (SecondOrderObjectSyntax.value_m (.fvar .here)
        (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here)))))
        (.forallE .set (.forallE .set (.forallE .set (.forallE .set
          (.imp (SecondOrderObjectSyntax.member_m (.bvar (.there (.there (.there .here))))
            (.fvar (.there .here)))
            (.imp (PowerlessNaturalStep.successor_m (.bvar (.there (.there (.there .here))))
              (.bvar (.there (.there .here))))
              (.imp (SecondOrderObjectSyntax.value_m (.fvar .here)
                (.bvar (.there (.there (.there .here)))) (.bvar (.there .here)))
                (.imp (SecondOrderObjectSyntax.value_m (.fvar .here)
                  (.bvar (.there (.there .here))) (.bvar .here)) (φ.substitute σ)))))))))))))

def trace_l {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (g n e a : carrier_l ℳ) : Prop :=
  ∃ S B, successor_l n S ∧ map_l g S B ∧ value_l g e a ∧
    ∀ k l x y, member_l ℳ k n → successor_l k l → value_l g k x → value_l g l y →
      φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y)

theorem trace_formula_l {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (g n e a : carrier_l ℳ) :
    (trace_m φ).satisfies (((((PowerlessComprehension.env_l η).pushFree a).pushFree e).pushFree n).pushFree g) ↔
      trace_l φ η g n e a := by
  simp only [trace_m, trace_l, Formula.satisfies, PowerlessNaturalStep.successor_formula_l,
    map_formula_l, value_formula_l, Formula.satisfies_substitute,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  apply exists_congr
  intro S
  apply exists_congr
  intro B
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  apply forall_congr'
  intro k
  apply forall_congr'
  intro l
  apply forall_congr'
  intro x
  apply forall_congr'
  intro y
  apply imp_congr_right
  intro _
  apply imp_congr_right
  intro _
  apply imp_congr_right
  intro _
  apply imp_congr_right
  intro _
  apply Iff.of_eq
  apply congrArg (fun η => φ.satisfies η)
  apply Env.ext (bound := []) (fun {_} v => nomatch v)
  · intro s v
    match s, v with
    | .set, .here => rfl
    | .set, .there .here => rfl
    | .set, .there (.there v) => rfl

def exists_m {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ)) :
    Formula ℒ [] (.set :: .set :: .set :: Γ) :=
  (trace_m φ).existsFreeTop .set

theorem exists_formula_l {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (n e a : carrier_l ℳ) :
    (exists_m φ).satisfies ((((PowerlessComprehension.env_l η).pushFree a).pushFree e).pushFree n) ↔
      ∃ g, trace_l φ η g n e a := by
  rw [exists_m, Formula.satisfies_existsFreeTop]
  exact exists_congr fun g => trace_formula_l φ η g n e a

theorem zero_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    {e : carrier_l ℳ} (he : PowerlessNatural.zero_l e) (a : carrier_l ℳ) :
    ∃ g, trace_l φ η g e e a := by
  obtain ⟨S, hS⟩ := successor_exists_l hℳ e
  obtain ⟨g, B, hg, hV⟩ := PowerlessExtension.constant_l hℳ S a
  exact ⟨g, S, B, hS, hg, (hV e a).mpr ⟨(hS e).mpr (Or.inr rfl), rfl⟩,
    fun k _ _ _ hk _ _ _ => (he k hk).elim⟩

theorem extend_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (h : ∀ x, ∃ y, φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y))
    {ω g n m e a : carrier_l ℳ} (hω : omega_l ω) (hn : member_l ℳ n ω)
    (hm : successor_l n m) (hg : trace_l φ η g n e a) :
    ∃ f, trace_l φ η f m e a := by
  obtain ⟨S, B, hS, hg, h₀, h₁⟩ := hg
  have h₂ := successor_unique_l hℳ hS hm
  subst S
  obtain ⟨x, hx, _⟩ := hg.2 n ((hm n).mpr (Or.inr rfl))
  obtain ⟨y, hy⟩ := h x
  obtain ⟨T, hT⟩ := successor_exists_l hℳ m
  have h₃ : ¬member_l ℳ m m := fun h₃ => asymmetry_l hℳ h₃ h₃
  obtain ⟨f, C, hf, hV⟩ := PowerlessExtension.exists_l hℳ hg h₃ hT (d := y)
  have h₄ : ∀ k z, member_l ℳ k m → value_l f k z → value_l g k z := by
    intro k z hk hz
    rcases (hV k z).mp hz with hz | ⟨rfl, _⟩
    · exact hz
    · exact (h₃ hk).elim
  refine ⟨f, T, C, hT, hf, (hV e a).mpr (Or.inl h₀), ?_⟩
  intro k l z w hk hl hz hw
  rcases (hm k).mp hk with hk | hk
  · have h₅ := PowerlessNaturalStep.bound_l hℳ hω n hn k l hk hl
    exact h₁ k l z w hk hl (h₄ k z ((hm k).mpr (Or.inl hk)) hz)
      (h₄ l w ((hm l).mpr h₅) hw)
  · subst k
    have h₅ := successor_unique_l hℳ hl hm
    subst l
    have h₆ := PowerlessFunction.value_unique_l hℳ hg
      (h₄ n z ((hm n).mpr (Or.inr rfl)) hz) hx.2
    have h₇ := PowerlessFunction.value_unique_l hℳ hf hw ((hV m y).mpr (Or.inr ⟨rfl, rfl⟩))
    subst z
    subst w
    exact hy

/-- 对实际轨迹公式作模型内部归纳；包括模型中的非标准自然数。 -/
theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (h : ∀ x, ∃ y, φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y))
    {ω e : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e) (a : carrier_l ℳ) :
    ∀ n, member_l ℳ n ω → ∃ g, trace_l φ η g n e a := by
  have h₀ : ∀ n, (exists_m φ).satisfies
      ((PowerlessComprehension.env_l ((η.push a).push e)).pushFree n) ↔ ∃ g, trace_l φ η g n e a := by
    intro n
    rw [PowerlessComprehension.env_push_l (Γ := .set :: Γ) (η.push a) e,
      PowerlessComprehension.env_push_l (Γ := Γ) η a]
    exact exists_formula_l φ η n e a
  have h₁ := PowerlessNatural.induction_l hℳ (exists_m φ) ((η.push a).push e) hω
    (fun z hz => (h₀ z).mpr (by
      have h₂ := PowerlessNatural.zero_unique_l hℳ hz he
      subst z
      exact zero_l hℳ φ η he a))
    (fun n m hn hm h₂ => (h₀ m).mpr (by
      obtain ⟨g, hg⟩ := (h₀ n).mp h₂
      exact extend_l hℳ φ η h hω hn hm hg))
  exact fun n hn => (h₀ n).mp (h₁ n hn)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessTrace
