import BMSConstructibleBridge.PowerlessSourceTuple

/-!
# 有限多条有限元数请求的共同闭包层

使用两个不同标签区分请求，而不是直接析取后允许返回错误分支的见证。
每条公式先按其外部有限元数编码，再将有限列表合成一个原公式。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceFamily

open Logic FirstOrder ThirdOrderSemantics PowerlessHierarchyStage

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def binding_m {Γ : SortContext ℒ} :
    Substitution ℒ [] (.set :: .set :: Γ) [.set] (.set :: .set :: Γ) :=
  .map (fun v => nomatch v) (fun v => match v with
    | .here => .fvar .here
    | .there .here => .bvar .here
    | .there (.there v) => .fvar (.there (.there v)))

theorem binding_formula_l {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : Env ℳ [] Γ) (p y x : carrier_l ℳ) :
    (φ.substitute binding_m).satisfies (((η.pushFree p).pushFree y).pushBound x) ↔
      φ.satisfies ((η.pushFree x).pushFree y) := by
  rw [Formula.satisfies_substitute]
  apply Iff.of_eq
  congr 1
  apply Env.ext
  · intro _ v
    nomatch v
  · intro s v
    cases v with
    | here => rfl
    | there v => cases v <;> rfl

def sum_m {Γ : SortContext ℒ} (φ ψ : Formula ℒ [] (.set :: .set :: Γ))
    (s t : Term ℒ [] Γ .set) : Formula ℒ [] (.set :: .set :: Γ) :=
  let q (r : Term ℒ [] Γ .set) :=
    ((r.weakenFree SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .existsE .set (.disj
    (.conj (SecondOrderObjectSyntax.ordered_m (q s) (.bvar .here) (.fvar (.there .here)))
      (φ.substitute binding_m))
    (.conj (SecondOrderObjectSyntax.ordered_m (q t) (.bvar .here) (.fvar (.there .here)))
      (ψ.substitute binding_m)))

theorem sum_formula_l {Γ : SortContext ℒ} (φ ψ : Formula ℒ [] (.set :: .set :: Γ))
    (η : Env ℳ [] Γ) (s t : Term ℒ [] Γ .set) (p y : carrier_l ℳ) :
    (sum_m φ ψ s t).satisfies ((η.pushFree p).pushFree y) ↔
      ∃ x, (ordered_l (s.eval η) x p ∧ φ.satisfies ((η.pushFree x).pushFree y)) ∨
        (ordered_l (t.eval η) x p ∧ ψ.satisfies ((η.pushFree x).pushFree y)) := by
  simp only [sum_m, Formula.satisfies, ordered_formula_l, binding_formula_l,
    Term.eval_weakenBound, Term.eval_weakenFree]
  rfl

theorem left_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (φ ψ : Formula ℒ [] (.set :: .set :: Γ))
    (η : Env ℳ [] Γ) (s t : Term ℒ [] Γ .set) (hst : s.eval η ≠ t.eval η)
    {p x : carrier_l ℳ} (hp : ordered_l (s.eval η) x p) (y : carrier_l ℳ) :
    (sum_m φ ψ s t).satisfies ((η.pushFree p).pushFree y) ↔
      φ.satisfies ((η.pushFree x).pushFree y) := by
  rw [sum_formula_l]
  constructor
  · rintro ⟨z, ⟨hz, hφ⟩ | ⟨hz, _⟩⟩
    · obtain ⟨_, rfl⟩ := (PowerlessBasic.ordered_eq_l hℳ hz hp).mp rfl
      exact hφ
    · exact (hst ((PowerlessBasic.ordered_eq_l hℳ hp hz).mp rfl).1).elim
  · intro hφ
    exact ⟨x, Or.inl ⟨hp, hφ⟩⟩

theorem right_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (φ ψ : Formula ℒ [] (.set :: .set :: Γ))
    (η : Env ℳ [] Γ) (s t : Term ℒ [] Γ .set) (hst : s.eval η ≠ t.eval η)
    {p x : carrier_l ℳ} (hp : ordered_l (t.eval η) x p) (y : carrier_l ℳ) :
    (sum_m φ ψ s t).satisfies ((η.pushFree p).pushFree y) ↔
      ψ.satisfies ((η.pushFree x).pushFree y) := by
  rw [sum_formula_l]
  constructor
  · rintro ⟨z, ⟨hz, _⟩ | ⟨hz, hψ⟩⟩
    · exact (hst ((PowerlessBasic.ordered_eq_l hℳ hz hp).mp rfl).1).elim
    · obtain ⟨_, rfl⟩ := (PowerlessBasic.ordered_eq_l hℳ hz hp).mp rfl
      exact hψ
  · intro hψ
    exact ⟨x, Or.inr ⟨hp, hψ⟩⟩

def closed_l {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : Env ℳ [] Γ) (A : carrier_l ℳ) (P : carrier_l ℳ → Prop) : Prop :=
  ∀ x, member_l ℳ x A → (∃ y, P y ∧ φ.satisfies ((η.pushFree x).pushFree y)) →
    ∃ y, member_l ℳ y A ∧ φ.satisfies ((η.pushFree x).pushFree y)

theorem sum_closed_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (φ ψ : Formula ℒ [] (.set :: .set :: Γ))
    (η : Env ℳ [] Γ) (s t : Term ℒ [] Γ .set) (A : carrier_l ℳ) (P : carrier_l ℳ → Prop)
    (hs : member_l ℳ (s.eval η) A) (ht : member_l ℳ (t.eval η) A)
    (hst : s.eval η ≠ t.eval η)
    (hA : ∀ a b p, member_l ℳ a A → member_l ℳ b A → ordered_l a b p → member_l ℳ p A)
    (h : closed_l (sum_m φ ψ s t) η A P) : closed_l φ η A P ∧ closed_l ψ η A P := by
  constructor
  · rintro x hx ⟨y, hy, hφ⟩
    obtain ⟨p, hp⟩ := PowerlessBasic.ordered_exists_l hℳ (s.eval η) x
    obtain ⟨z, hz, hψ⟩ := h p (hA _ _ _ hs hx hp) ⟨y, hy, (left_l hℳ φ ψ η s t hst hp y).mpr hφ⟩
    exact ⟨z, hz, (left_l hℳ φ ψ η s t hst hp z).mp hψ⟩
  · rintro x hx ⟨y, hy, hψ⟩
    obtain ⟨p, hp⟩ := PowerlessBasic.ordered_exists_l hℳ (t.eval η) x
    obtain ⟨z, hz, hφ⟩ := h p (hA _ _ _ ht hx hp) ⟨y, hy, (right_l hℳ φ ψ η s t hst hp y).mpr hψ⟩
    exact ⟨z, hz, (right_l hℳ φ ψ η s t hst hp z).mp hφ⟩

def family_m {Γ : SortContext ℒ} (s t : Term ℒ [] Γ .set) :
    List (Formula ℒ [] (.set :: .set :: Γ)) → Formula ℒ [] (.set :: .set :: Γ)
  | [] => .falsum
  | φ :: Φ => sum_m φ (family_m s t Φ) s t

theorem family_closed_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (η : Env ℳ [] Γ) (s t : Term ℒ [] Γ .set)
    (A : carrier_l ℳ) (P : carrier_l ℳ → Prop)
    (hs : member_l ℳ (s.eval η) A) (ht : member_l ℳ (t.eval η) A)
    (hst : s.eval η ≠ t.eval η)
    (hA : ∀ a b p, member_l ℳ a A → member_l ℳ b A → ordered_l a b p → member_l ℳ p A)
    (Φ : List (Formula ℒ [] (.set :: .set :: Γ))) (h : closed_l (family_m s t Φ) η A P) :
    ∀ φ ∈ Φ, closed_l φ η A P := by
  induction Φ with
  | nil => simp
  | cons ψ Φ ih =>
    obtain ⟨hψ, hΦ⟩ := sum_closed_l hℳ ψ (family_m s t Φ) η s t A P hs ht hst hA h
    intro φ hφ
    rcases List.mem_cons.mp hφ with rfl | hφ
    · exact hψ
    · exact ih hΦ φ hφ

/-- 每条请求可有不同的外部有限元数；所有请求使用同一个实际极限层。 -/
theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ}
    (Φ : List (Σ n : Nat, Formula ℒ [] (.set :: (List.replicate n .set ++ Γ))))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (ω e T t₁ t₂ t₃ : Term ℒ [] Γ .set) (α : carrier_l ℳ)
    (hω : omega_l (ω.eval (PowerlessComprehension.env_l η)))
    (ht : PowerlessEvaluationTags.tags_l (e.eval (PowerlessComprehension.env_l η))
      (t₁.eval (PowerlessComprehension.env_l η)) (t₂.eval (PowerlessComprehension.env_l η))
      (t₃.eval (PowerlessComprehension.env_l η)))
    (hT : PowerlessTriangular.triangular_l (ω.eval (PowerlessComprehension.env_l η))
      (e.eval (PowerlessComprehension.env_l η)) (T.eval (PowerlessComprehension.env_l η)))
    (hα : PowerlessOrdinal.ordinal_l α) :
    ∃ δ U, PowerlessStagePair.limit_l δ ∧ member_l ℳ α δ ∧
      stage_l (ω.eval (PowerlessComprehension.env_l η)) (e.eval (PowerlessComprehension.env_l η))
        (T.eval (PowerlessComprehension.env_l η)) (t₁.eval (PowerlessComprehension.env_l η))
        (t₂.eval (PowerlessComprehension.env_l η)) (t₃.eval (PowerlessComprehension.env_l η)) δ U ∧
      ∀ n φ, Sigma.mk n φ ∈ Φ → ∀ v, PowerlessSourceTuple.bounded_l U n v →
        (∃ y, PowerlessSourceWitnessDomain.domain_l
          (ω.eval (PowerlessComprehension.env_l η)) (e.eval (PowerlessComprehension.env_l η))
          (T.eval (PowerlessComprehension.env_l η)) (t₁.eval (PowerlessComprehension.env_l η))
          (t₂.eval (PowerlessComprehension.env_l η)) (t₃.eval (PowerlessComprehension.env_l η)) y ∧
          φ.satisfies ((PowerlessSourceTuple.env_l (PowerlessComprehension.env_l η) n v).pushFree y)) →
        ∃ y, member_l ℳ y U ∧
          φ.satisfies ((PowerlessSourceTuple.env_l (PowerlessComprehension.env_l η) n v).pushFree y) := by
  let ρ := PowerlessComprehension.env_l η
  let Ψ := Φ.map (fun p => PowerlessSourceTuple.form_m p.1 p.2)
  obtain ⟨δ, U, hδ, hαδ, hU, h⟩ := PowerlessSourceWitnessDomain.exists_l hℳ
    (family_m e t₁ Ψ) η ω e T t₁ t₂ t₃ α hω ht.1 hα
  have heU := PowerlessStageClosure.empty_l hℳ hω hU hδ ht hT ht.1
  have htU : member_l ℳ (t₁.eval ρ) U := PowerlessStageClosure.pair_l hℳ hω hU hδ ht hT
    heU heU (by
      intro x
      simpa only [ht.1 x, false_or, or_self] using ht.2.1 x)
  have h₀ : e.eval ρ ≠ t₁.eval ρ := by
    intro h₀
    have h₁ := (ht.2.1 (e.eval ρ)).mpr (Or.inr rfl)
    rw [← h₀] at h₁
    exact ht.1 _ h₁
  have hA := fun a b p ha hb hp => PowerlessStageGraphClosure.ordered_l hℳ hω ht hT hU hδ
    (a := a) (b := b) (p := p) ha hb hp
  have h₁ := family_closed_l hℳ ρ e t₁ U _ heU htU h₀ hA Ψ h
  refine ⟨δ, U, hδ, hαδ, hU, ?_⟩
  intro n φ hφ
  exact PowerlessSourceTuple.closure_l hℳ ρ n φ _ U (e.eval ρ) heU hA
    (h₁ _ (List.mem_map.mpr ⟨⟨n, φ⟩, hφ, rfl⟩))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceFamily
