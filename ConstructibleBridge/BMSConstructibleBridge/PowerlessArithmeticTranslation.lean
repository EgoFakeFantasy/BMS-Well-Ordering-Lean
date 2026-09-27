import BMSConstructibleBridge.PowerlessArithmeticTerms

/-!
# 双排序算术公式的纯集合翻译

数量词只遍历同一内部 ω，集合量词只遍历实际的 ω 子集。
保持任意原参数和量词交替，逐公式比较显式算术结构与原纯集合模型的满足关系。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessArithmeticTranslation

open Logic FirstOrder ThirdOrderSemantics PowerlessArithmeticTerms
open Automation.RelationalTranslation (weakenTerm witnesses existsBlock pushBlock
  weakenTerm_eval witnesses_eval existsBlock_satisfies)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessArithmetic.structure_l

universe u

def lift_m {Γ : SortContext SecondOrderSyntax.signature_m} {Δ Θ : SortContext ℒ}
    {s : SecondOrderSyntax.sort_m} (ρ : assignment_m Γ Δ Θ) : assignment_m (s :: Γ) (.set :: Δ) Θ :=
  fun v => match v with
    | .here => .bvar .here
    | .there v => weakenTerm (τ := ℒ) [SetTheory.SetSort.set] (ρ v)

def domain_m {Γ Δ : SortContext ℒ} (s : SecondOrderSyntax.sort_m)
    (ω a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  match s with
  | .num => SecondOrderObjectSyntax.member_m a ω
  | .set => .forallE .set (.imp
      (SecondOrderObjectSyntax.member_m (.bvar .here) (a.weakenBound SetTheory.SetSort.set))
      (SecondOrderObjectSyntax.member_m (.bvar .here) (ω.weakenBound SetTheory.SetSort.set)))

def relation_m {Γ Δ : SortContext ℒ} : (r : SecondOrderSyntax.rel_m) →
    Arguments ℒ Γ Δ (context_m (SecondOrderSyntax.signature_m.relDomain r)) → Formula ℒ Γ Δ
  | .mem, .cons a (.cons A .nil) => SecondOrderObjectSyntax.member_m a A
  | .start, .cons _ (.cons _ .nil) => .falsum
  | .step, .cons _ (.cons _ (.cons _ .nil)) => .falsum

def formula_m {Γ Δ : SortContext SecondOrderSyntax.signature_m} {Θ Λ : SortContext ℒ}
    (ω e : Term ℒ Θ Λ .set) (ρ : assignment_m Γ Θ Λ) (τ : assignment_m Δ Θ Λ) :
    Formula SecondOrderSyntax.signature_m Γ Δ → Formula ℒ Θ Λ
  | .falsum => .falsum
  | .truth => .truth
  | .rel r a =>
      let Ξ := context_m (SecondOrderSyntax.signature_m.relDomain r)
      existsBlock Ξ (.conj
        (arguments_m (weakenTerm Ξ ω) (weakenTerm Ξ e) (weaken_m Ξ ρ) (weaken_m Ξ τ) a (witnesses Ξ))
        (relation_m r (witnesses Ξ)))
  | .equal a b => .existsE .set (.conj
      (term_m (weakenTerm (τ := ℒ) [.set] ω) (weakenTerm (τ := ℒ) [.set] e)
        (weaken_m [.set] ρ) (weaken_m [.set] τ) a (.bvar .here))
      (term_m (weakenTerm (τ := ℒ) [.set] ω) (weakenTerm (τ := ℒ) [.set] e)
        (weaken_m [.set] ρ) (weaken_m [.set] τ) b (.bvar .here)))
  | .neg φ => .neg (formula_m ω e ρ τ φ)
  | .conj φ ψ => .conj (formula_m ω e ρ τ φ) (formula_m ω e ρ τ ψ)
  | .disj φ ψ => .disj (formula_m ω e ρ τ φ) (formula_m ω e ρ τ ψ)
  | .imp φ ψ => .imp (formula_m ω e ρ τ φ) (formula_m ω e ρ τ ψ)
  | .iff φ ψ => .iff (formula_m ω e ρ τ φ) (formula_m ω e ρ τ ψ)
  | .forallE s φ => .forallE .set (.imp (domain_m s (weakenTerm (τ := ℒ) [.set] ω) (.bvar .here))
      (formula_m (weakenTerm (τ := ℒ) [.set] ω) (weakenTerm (τ := ℒ) [.set] e) (lift_m ρ) (weaken_m [.set] τ) φ))
  | .existsE s φ => .existsE .set (.conj (domain_m s (weakenTerm (τ := ℒ) [.set] ω) (.bvar .here))
      (formula_m (weakenTerm (τ := ℒ) [.set] ω) (weakenTerm (τ := ℒ) [.set] e) (lift_m ρ) (weaken_m [.set] τ) φ))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def domain_l (ω : carrier_l ℳ) (s : SecondOrderSyntax.sort_m) (a : carrier_l ℳ) : Prop :=
  match s with
  | .num => member_l ℳ a ω
  | .set => subset_l a ω

theorem domain_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ)
    (s : SecondOrderSyntax.sort_m) (ω a : Term ℒ Γ Δ .set) :
    (domain_m s ω a).satisfies η ↔ domain_l (ω.eval η) s (a.eval η) := by
  cases s
  · rfl
  · simp only [domain_m, domain_l, subset_l, Formula.satisfies, SecondOrderObjectSyntax.member_m,
      Arguments.eval, Term.eval_weakenBound]
    rfl

theorem domain_val_l {ω : carrier_l ℳ} {s : SecondOrderSyntax.sort_m} (a : sort_l ω s) :
    domain_l ω s (val_l a) := by
  cases s <;> exact a.property

theorem domain_exists_l {ω : carrier_l ℳ} (s : SecondOrderSyntax.sort_m) (x : carrier_l ℳ) :
    domain_l ω s x ↔ ∃ a : sort_l ω s, val_l a = x := by
  cases s <;> exact ⟨fun h => ⟨⟨x, h⟩, rfl⟩, fun ⟨a, h⟩ => h ▸ a.property⟩

variable {ω e : carrier_l ℳ} {he : PowerlessNatural.zero_l e} {h₀ : member_l ℳ e ω}
  {F : PowerlessArithmetic.operations_l ω e}

local notation "𝒩" => PowerlessArithmetic.structure_l he h₀ F

theorem lift_l {Γ Δ : SortContext SecondOrderSyntax.signature_m} {Θ Λ : SortContext ℒ}
    {ξ : Env 𝒩 Γ Δ} {η : Env ℳ Θ Λ} {ρ : assignment_m Γ Θ Λ}
    (h : agrees_l η ρ ξ.boundVal) {s : SecondOrderSyntax.sort_m} (a : sort_l ω s) :
    agrees_l (η.pushBound (val_l a)) (lift_m ρ) (ξ.pushBound a).boundVal := by
  intro t v
  cases v with
  | here => rfl
  | there v => exact (weakenTerm_eval η (.cons (val_l a) .nil) (ρ v)).trans (h v)

theorem relation_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ)
    (r : SecondOrderSyntax.rel_m)
    (a : Arguments ℒ Γ Δ (context_m (SecondOrderSyntax.signature_m.relDomain r)))
    (b : Values (sort_l ω) (SecondOrderSyntax.signature_m.relDomain r))
    (ha : a.eval η = values_l b) :
    (relation_m r a).satisfies η ↔ (𝒩).relInterp r b := by
  match r, a, b with
  | .mem, .cons x (.cons y .nil), .cons b (.cons c .nil) =>
    obtain ⟨hx, hy⟩ := Values.cons.inj ha
    have hy := (Values.cons.inj hy).1
    change member_l ℳ (x.eval η) (y.eval η) ↔ member_l ℳ b.val c.val
    exact Iff.of_eq (congrArg₂ (member_l ℳ) hx hy)
  | .start, .cons _ (.cons _ .nil), .cons _ (.cons _ .nil) => rfl
  | .step, .cons _ (.cons _ (.cons _ .nil)), .cons _ (.cons _ (.cons _ .nil)) => rfl

/-- 全部原公式的真值保持，特别包括任意交替的内部集合量词。 -/
theorem formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    {Γ Δ : SortContext SecondOrderSyntax.signature_m} {Θ Λ : SortContext ℒ}
    (ξ : Env 𝒩 Γ Δ) (η : Env ℳ Θ Λ) (w z : Term ℒ Θ Λ .set)
    (ρ : assignment_m Γ Θ Λ) (τ : assignment_m Δ Θ Λ)
    (hw : w.eval η = ω) (hz : z.eval η = e)
    (hρ : agrees_l η ρ ξ.boundVal) (hτ : agrees_l η τ ξ.freeVal)
    (φ : Formula SecondOrderSyntax.signature_m Γ Δ) :
    (formula_m w z ρ τ φ).satisfies η ↔ φ.satisfies ξ := by
  have hw₁ (x : carrier_l ℳ) :
      (weakenTerm (τ := ℒ) [.set] w).eval (η.pushBound x) = ω :=
    (weakenTerm_eval η (.cons x .nil) w).trans hw
  cases φ with
  | falsum | truth => rfl
  | rel r a =>
    rw [formula_m, existsBlock_satisfies]
    constructor
    · rintro ⟨b, hb, h⟩
      have h₁ := (arguments_formula_l hℳ hω he F ξ (pushBlock η b) _ _ _ _
        ((weakenTerm_eval η b w).trans hw) ((weakenTerm_eval η b z).trans hz)
        (weaken_l hρ b) (weaken_l hτ b) a _).mp hb
      rw [witnesses_eval] at h₁
      subst b
      exact (relation_formula_l (he := he) (h₀ := h₀) (F := F) _ r _ (a.eval ξ) (witnesses_eval η _)).mp h
    · intro h
      refine ⟨values_l (a.eval ξ), ?_, ?_⟩
      · apply (arguments_formula_l hℳ hω he F ξ _ _ _ _ _
          ((weakenTerm_eval η _ w).trans hw) ((weakenTerm_eval η _ z).trans hz)
          (weaken_l hρ _) (weaken_l hτ _) a _).mpr
        exact witnesses_eval η _
      · exact (relation_formula_l (he := he) (h₀ := h₀) (F := F) _ r _ (a.eval ξ) (witnesses_eval η _)).mpr h
  | @equal Γ Δ s a b =>
    change (∃ x, (term_m _ _ _ _ a _).satisfies (η.pushBound x) ∧
      (term_m _ _ _ _ b _).satisfies (η.pushBound x)) ↔ a.eval ξ = b.eval ξ
    have h (c : Term SecondOrderSyntax.signature_m Γ Δ s) (x : carrier_l ℳ) :=
      term_formula_l hℳ hω he F ξ (η.pushBound x) _ _ _ _
        ((weakenTerm_eval η (.cons x .nil) w).trans hw)
        ((weakenTerm_eval η (.cons x .nil) z).trans hz)
        (weaken_l hρ (.cons x .nil)) (weaken_l hτ (.cons x .nil)) c (.bvar .here)
    simp only [h, Term.eval, Env.pushBound_bound_here]
    exact ⟨fun ⟨_, h₁, h₂⟩ => val_injective_l (h₁.symm.trans h₂),
      fun h₁ => ⟨val_l (a.eval ξ), rfl, congrArg val_l h₁⟩⟩
  | neg φ => exact not_congr (formula_l hℳ hω ξ η w z ρ τ hw hz hρ hτ φ)
  | conj φ ψ =>
    exact and_congr (formula_l hℳ hω ξ η w z ρ τ hw hz hρ hτ φ)
      (formula_l hℳ hω ξ η w z ρ τ hw hz hρ hτ ψ)
  | disj φ ψ =>
    exact or_congr (formula_l hℳ hω ξ η w z ρ τ hw hz hρ hτ φ)
      (formula_l hℳ hω ξ η w z ρ τ hw hz hρ hτ ψ)
  | imp φ ψ =>
    exact imp_congr (formula_l hℳ hω ξ η w z ρ τ hw hz hρ hτ φ)
      (formula_l hℳ hω ξ η w z ρ τ hw hz hρ hτ ψ)
  | iff φ ψ =>
    exact iff_congr (formula_l hℳ hω ξ η w z ρ τ hw hz hρ hτ φ)
      (formula_l hℳ hω ξ η w z ρ τ hw hz hρ hτ ψ)
  | forallE s φ =>
    change (∀ x, (domain_m s _ _).satisfies (η.pushBound x) →
      (formula_m _ _ _ _ φ).satisfies (η.pushBound x)) ↔ ∀ a : sort_l ω s, φ.satisfies (ξ.pushBound a)
    have h (a : sort_l ω s) := formula_l hℳ hω (ξ.pushBound a) (η.pushBound (val_l a)) _ _ _ _
      ((weakenTerm_eval η (.cons (val_l a) .nil) w).trans hw)
      ((weakenTerm_eval η (.cons (val_l a) .nil) z).trans hz)
      (lift_l hρ a) (weaken_l hτ (.cons (val_l a) .nil)) φ
    constructor
    · intro h₁ a
      apply (h a).mp (h₁ (val_l a) ?_)
      apply (domain_formula_l _ _ _ _).mpr
      simpa only [hw₁, Term.eval, Env.pushBound_bound_here] using domain_val_l a
    · intro h₁ x hx
      have hx := (domain_formula_l _ _ _ _).mp hx
      have hx : domain_l ω s x := by
        simpa only [hw₁, Term.eval, Env.pushBound_bound_here] using hx
      obtain ⟨a, rfl⟩ := (domain_exists_l s x).mp hx
      exact (h a).mpr (h₁ a)
  | existsE s φ =>
    change (∃ x, (domain_m s _ _).satisfies (η.pushBound x) ∧
      (formula_m _ _ _ _ φ).satisfies (η.pushBound x)) ↔ ∃ a : sort_l ω s, φ.satisfies (ξ.pushBound a)
    have h (a : sort_l ω s) := formula_l hℳ hω (ξ.pushBound a) (η.pushBound (val_l a)) _ _ _ _
      ((weakenTerm_eval η (.cons (val_l a) .nil) w).trans hw)
      ((weakenTerm_eval η (.cons (val_l a) .nil) z).trans hz)
      (lift_l hρ a) (weaken_l hτ (.cons (val_l a) .nil)) φ
    constructor
    · rintro ⟨x, hx, h₁⟩
      have hx := (domain_formula_l _ _ _ _).mp hx
      have hx : domain_l ω s x := by
        simpa only [hw₁, Term.eval, Env.pushBound_bound_here] using hx
      obtain ⟨a, rfl⟩ := (domain_exists_l s x).mp hx
      exact ⟨a, (h a).mp h₁⟩
    · rintro ⟨a, h₁⟩
      refine ⟨val_l a, (domain_formula_l _ _ _ _).mpr ?_, (h a).mpr h₁⟩
      simpa only [hw₁, Term.eval, Env.pushBound_bound_here] using domain_val_l a

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessArithmeticTranslation
