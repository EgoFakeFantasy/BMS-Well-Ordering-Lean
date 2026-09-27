import BMSConstructibleBridge.PowerlessSourceWitnessBound
import BMSConstructibleBridge.PowerlessOrdinalMinimum

/-!
# 固定源公式的实际层次推进图

推进条件直接量化两个实际层及源公式见证；最低输出序数由内部最小化取得。
输入非序数时才取指定缺省值。覆盖只约束指定公式的见证，尚不证明最终反射。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceWitnessStep

open Logic FirstOrder ThirdOrderSemantics PowerlessHierarchyStage

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def binding_m {Γ : SortContext ℒ} :
    Substitution ℒ [] (.set :: .set :: Γ) [.set, .set, .set, .set] (.set :: .set :: Γ) :=
  .map (fun {s} (v : Variable ([] : SortContext ℒ) s) => nomatch v)
    (fun {s} (v : Variable (.set :: .set :: Γ) s) => match v with
    | .here => .bvar .here
    | .there .here => .bvar (.there .here)
    | .there (.there v) => .fvar (.there (.there v)))

theorem binding_formula_l {Γ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Γ)) (η : Env ℳ [] Γ) (α β A B x y : carrier_l ℳ) :
    (φ.substitute binding_m).satisfies
      ((((((η.pushFree α).pushFree β).pushBound A).pushBound B).pushBound x).pushBound y) ↔
        φ.satisfies ((η.pushFree x).pushFree y) := by
  rw [Formula.satisfies_substitute]
  apply Iff.of_eq
  congr 1
  apply Env.ext
  · intro s v
    nomatch v
  · intro s v
    cases v with
    | here => rfl
    | there v => cases v <;> rfl

def step_m {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (ω e T t₁ t₂ t₃ : Term ℒ [] Γ .set) : Formula ℒ [] (.set :: .set :: Γ) :=
  let q (s : Term ℒ [] Γ .set) : Term ℒ [.set, .set] (.set :: .set :: Γ) .set :=
    (((s.weakenFree SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set
      ).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  let P : Formula ℒ [.set, .set, .set] (.set :: .set :: Γ) :=
    .imp (.existsE .set (φ.substitute binding_m))
      (.existsE .set (.conj
        (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there (.there .here))))
        (φ.substitute binding_m)))
  .conj (SecondOrderObjectSyntax.member_m (.fvar (.there .here)) (.fvar .here))
    (.existsE .set (.existsE .set (.conj
      (stage_m (q ω) (q e) (q T) (q t₁) (q t₂) (q t₃) (.fvar (.there .here)) (.bvar (.there .here)))
      (.conj (stage_m (q ω) (q e) (q T) (q t₁) (q t₂) (q t₃) (.fvar .here) (.bvar .here))
        (.forallE .set (.imp
          (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there (.there .here)))) P))))))

def step_l {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : Env ℳ [] Γ) (ω e T t₁ t₂ t₃ α β : carrier_l ℳ) : Prop :=
  member_l ℳ α β ∧ ∃ A B, stage_l ω e T t₁ t₂ t₃ α A ∧ stage_l ω e T t₁ t₂ t₃ β B ∧
    ∀ x, member_l ℳ x A → (∃ y, φ.satisfies ((η.pushFree x).pushFree y)) →
      ∃ y, member_l ℳ y B ∧ φ.satisfies ((η.pushFree x).pushFree y)

theorem step_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ)) (η : Env ℳ [] Γ)
    (ω e T t₁ t₂ t₃ : Term ℒ [] Γ .set) (α β : carrier_l ℳ) :
    (step_m φ ω e T t₁ t₂ t₃).satisfies ((η.pushFree α).pushFree β) ↔
      step_l φ η (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) α β := by
  simp only [step_m, step_l, Formula.satisfies, stage_formula_l hℳ,
    binding_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval,
    Term.eval_weakenBound, Term.eval_weakenFree]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (ω e T t₁ t₂ t₃ : Term ℒ [] Γ .set) (α : carrier_l ℳ)
    (hω : omega_l (ω.eval (PowerlessComprehension.env_l η)))
    (hα : PowerlessOrdinal.ordinal_l α)
    (hC : ∀ x y,
      φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) → ∃ γ U,
      stage_l (ω.eval (PowerlessComprehension.env_l η)) (e.eval (PowerlessComprehension.env_l η))
        (T.eval (PowerlessComprehension.env_l η)) (t₁.eval (PowerlessComprehension.env_l η))
        (t₂.eval (PowerlessComprehension.env_l η)) (t₃.eval (PowerlessComprehension.env_l η)) γ U ∧
      member_l ℳ y U) :
    ∃ β, step_l φ (PowerlessComprehension.env_l η)
      (ω.eval (PowerlessComprehension.env_l η)) (e.eval (PowerlessComprehension.env_l η))
      (T.eval (PowerlessComprehension.env_l η)) (t₁.eval (PowerlessComprehension.env_l η))
      (t₂.eval (PowerlessComprehension.env_l η)) (t₃.eval (PowerlessComprehension.env_l η)) α β := by
  let ρ := PowerlessComprehension.env_l η
  obtain ⟨A, hA⟩ := PowerlessHierarchyStage.exists_l hℳ hω hα
    (e.eval ρ) (T.eval ρ) (t₁.eval ρ) (t₂.eval ρ) (t₃.eval ρ)
  obtain ⟨β, B, hαβ, hB, h⟩ := PowerlessSourceWitnessBound.bound_l hℳ φ η ω e T t₁ t₂ t₃ A α hω hα hC
  exact ⟨β, hαβ, A, B, hA, hB, h⟩

def select_m {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (ω e T t₁ t₂ t₃ : Term ℒ [] Γ .set) : Formula ℒ [] (.set :: .set :: Γ) :=
  let P : Formula ℒ [] (.set :: .set :: Γ) := PowerlessOrdinal.ordinal_m (.fvar (.there .here))
  .disj (.conj P (PowerlessOrdinalMinimum.minimum_m (step_m φ ω e T t₁ t₂ t₃)))
    (.conj (.neg P) (.equal (.fvar .here)
      ((e.weakenFree SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set)))

theorem select_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ)) (η : Env ℳ [] Γ)
    (ω e T t₁ t₂ t₃ : Term ℒ [] Γ .set) (α β : carrier_l ℳ) :
    (select_m φ ω e T t₁ t₂ t₃).satisfies ((η.pushFree α).pushFree β) ↔
      (PowerlessOrdinal.ordinal_l α ∧
        PowerlessOrdinalMinimum.minimum_l (step_m φ ω e T t₁ t₂ t₃) (η.pushFree α) β) ∨
      (¬PowerlessOrdinal.ordinal_l α ∧ β = e.eval η) := by
  simp only [select_m, Formula.satisfies, PowerlessOrdinal.ordinal_formula_l hℳ,
    PowerlessOrdinalMinimum.minimum_formula_l hℳ, Term.eval_weakenFree]
  rfl

theorem select_unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ)) (η : Env ℳ [] Γ)
    (ω e T t₁ t₂ t₃ : Term ℒ [] Γ .set) {α β γ : carrier_l ℳ}
    (hβ : (select_m φ ω e T t₁ t₂ t₃).satisfies ((η.pushFree α).pushFree β))
    (hγ : (select_m φ ω e T t₁ t₂ t₃).satisfies ((η.pushFree α).pushFree γ)) : β = γ := by
  rw [select_formula_l hℳ] at hβ hγ
  rcases hβ with ⟨hα, hβ⟩ | ⟨hα, rfl⟩
  · rcases hγ with ⟨_, hγ⟩ | ⟨h, _⟩
    · exact PowerlessOrdinalMinimum.unique_l hℳ hβ hγ
    · exact (h hα).elim
  · rcases hγ with ⟨h, _⟩ | ⟨_, rfl⟩
    · exact (hα h).elim
    · rfl

theorem select_exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (ω e T t₁ t₂ t₃ : Term ℒ [] Γ .set)
    (hω : omega_l (ω.eval (PowerlessComprehension.env_l η)))
    (hC : ∀ x y,
      φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) → ∃ γ U,
      stage_l (ω.eval (PowerlessComprehension.env_l η)) (e.eval (PowerlessComprehension.env_l η))
        (T.eval (PowerlessComprehension.env_l η)) (t₁.eval (PowerlessComprehension.env_l η))
        (t₂.eval (PowerlessComprehension.env_l η)) (t₃.eval (PowerlessComprehension.env_l η)) γ U ∧
      member_l ℳ y U) (α : carrier_l ℳ) :
    ∃ β, (select_m φ ω e T t₁ t₂ t₃).satisfies
      (((PowerlessComprehension.env_l η).pushFree α).pushFree β) := by
  classical
  let ρ := PowerlessComprehension.env_l η
  by_cases hα : PowerlessOrdinal.ordinal_l α
  · obtain ⟨β, hβ⟩ := exists_l hℳ φ η ω e T t₁ t₂ t₃ α hω hα hC
    have hβ₀ : PowerlessOrdinal.ordinal_l β := by
      obtain ⟨_, A, B, _, hB, _⟩ := hβ
      exact hB.1
    obtain ⟨γ, hγ⟩ := PowerlessOrdinalMinimum.exists_l hℳ (step_m φ ω e T t₁ t₂ t₃)
      (η.push α) ⟨β, hβ₀, by
        rw [PowerlessComprehension.env_push_l]
        exact (step_formula_l hℳ φ ρ ω e T t₁ t₂ t₃ α β).mpr hβ⟩
    rw [PowerlessComprehension.env_push_l] at hγ
    exact ⟨γ, (select_formula_l hℳ φ ρ ω e T t₁ t₂ t₃ α γ).mpr (Or.inl ⟨hα, hγ⟩)⟩
  · exact ⟨e.eval ρ, (select_formula_l hℳ φ ρ ω e T t₁ t₂ t₃ α (e.eval ρ)).mpr
      (Or.inr ⟨hα, rfl⟩)⟩

theorem selected_step_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ)) (η : Env ℳ [] Γ)
    (ω e T t₁ t₂ t₃ : Term ℒ [] Γ .set) {α β : carrier_l ℳ}
    (hα : PowerlessOrdinal.ordinal_l α)
    (h : (select_m φ ω e T t₁ t₂ t₃).satisfies ((η.pushFree α).pushFree β)) :
    step_l φ η (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) α β := by
  rcases (select_formula_l hℳ φ η ω e T t₁ t₂ t₃ α β).mp h with ⟨_, h⟩ | ⟨h, _⟩
  · exact (step_formula_l hℳ φ η ω e T t₁ t₂ t₃ α β).mp h.2.1
  · exact (h hα).elim


end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceWitnessStep
