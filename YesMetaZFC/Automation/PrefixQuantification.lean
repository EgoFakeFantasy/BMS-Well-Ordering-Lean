import YesMetaZFC.Automation.ModelClosure

/-! # 保留尾部参数的有限前缀量化

只关闭自由上下文的指定前缀，保留绑定上下文和尾部参数。值列语义精确
记录这些量词的作用域，供先存在编码、再全称量化参数的对象模式使用。
-/

namespace YesMetaZFC.Automation.PrefixQuantification

open Logic Logic.FirstOrder RelationalTranslation

set_option autoImplicit false

universe u

variable {σ : Signature.{0, 0, 0}} {𝒩 : Structure.{0, 0, 0, u} σ}

def env_l {Γ Δ : SortContext σ} (η : Env 𝒩 Γ Δ) :
    {Θ : SortContext σ} → Values 𝒩.Carrier Θ → Env 𝒩 Γ (Θ ++ Δ)
  | .nil, .nil => η
  | _ :: _, .cons x xs => (env_l η xs).pushFree x

def weaken_m {Γ Δ : SortContext σ} {s : σ.SortSymbol} (Θ : SortContext σ)
    (t : Term σ Γ Δ s) : Term σ Γ (Θ ++ Δ) s :=
  match Θ with
  | [] => t
  | q :: Θ => (weaken_m Θ t).weakenFree q

theorem weaken_l {Γ Δ Θ : SortContext σ} {s : σ.SortSymbol}
    (η : Env 𝒩 Γ Δ) (xs : Values 𝒩.Carrier Θ) (t : Term σ Γ Δ s) :
    (weaken_m Θ t).eval (env_l η xs) = t.eval η := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [weaken_m, env_l, Term.eval_weakenFree] using ih

def entry_m {Γ Δ : SortContext σ} : {Θ : SortContext σ} → {s : σ.SortSymbol} →
    Variable Θ s → Term σ Γ (Θ ++ Δ) s
  | _, _, .here => .fvar .here
  | _, _, .there v => (entry_m v).weakenFree _

theorem entry_l {Γ Δ Θ : SortContext σ} (η : Env 𝒩 Γ Δ) (xs : Values 𝒩.Carrier Θ)
    {s : σ.SortSymbol} (v : Variable Θ s) :
    (entry_m (Γ := Γ) (Δ := Δ) v).eval (env_l η xs) = valuesAssignment xs v := by
  induction xs with
  | nil => nomatch v
  | cons x xs ih =>
    cases v with
    | here => rfl
    | there v => simpa only [entry_m, env_l, Term.eval_weakenFree, valuesAssignment] using ih v

def forall_m {Γ Δ : SortContext σ} : (Θ : SortContext σ) → Formula σ Γ (Θ ++ Δ) → Formula σ Γ Δ
  | .nil, φ => φ
  | s :: Θ, φ => forall_m Θ (φ.forallFreeTop s)

def exists_m {Γ Δ : SortContext σ} : (Θ : SortContext σ) → Formula σ Γ (Θ ++ Δ) → Formula σ Γ Δ
  | .nil, φ => φ
  | s :: Θ, φ => exists_m Θ (φ.existsFreeTop s)

theorem forall_formula_l {Γ Δ : SortContext σ} (Θ : SortContext σ)
    (φ : Formula σ Γ (Θ ++ Δ)) (η : Env 𝒩 Γ Δ) :
    (forall_m Θ φ).satisfies η ↔ ∀ xs : Values 𝒩.Carrier Θ, φ.satisfies (env_l η xs) := by
  induction Θ with
  | nil =>
    exact ⟨fun h xs => by cases xs; exact h, fun h => h .nil⟩
  | cons s Θ ih =>
    rw [forall_m, ih]
    constructor
    · intro h xs
      cases xs with
      | cons x xs => exact (Formula.satisfies_forallFreeTop (env_l η xs) φ).mp (h xs) x
    · intro h xs
      exact (Formula.satisfies_forallFreeTop (env_l η xs) φ).mpr (fun x => h (.cons x xs))

theorem exists_formula_l {Γ Δ : SortContext σ} (Θ : SortContext σ)
    (φ : Formula σ Γ (Θ ++ Δ)) (η : Env 𝒩 Γ Δ) :
    (exists_m Θ φ).satisfies η ↔ ∃ xs : Values 𝒩.Carrier Θ, φ.satisfies (env_l η xs) := by
  induction Θ with
  | nil =>
    exact ⟨fun h => ⟨.nil, h⟩, fun ⟨xs, h⟩ => by cases xs; exact h⟩
  | cons s Θ ih =>
    rw [exists_m, ih]
    constructor
    · rintro ⟨xs, h⟩
      obtain ⟨x, hx⟩ := (Formula.satisfies_existsFreeTop (env_l η xs) φ).mp h
      exact ⟨.cons x xs, hx⟩
    · rintro ⟨xs, h⟩
      cases xs with
      | cons x xs => exact ⟨xs, (Formula.satisfies_existsFreeTop (env_l η xs) φ).mpr ⟨x, h⟩⟩

def conjunction_m {Γ Δ : SortContext σ} : (Θ : SortContext σ) →
    ({s : σ.SortSymbol} → Variable Θ s → Formula σ Γ Δ) → Formula σ Γ Δ
  | .nil, _ => .truth
  | _ :: Θ, p => .conj (p .here) (conjunction_m Θ (fun v => p (.there v)))

theorem conjunction_formula_l {Γ Δ : SortContext σ} (Θ : SortContext σ)
    (p : {s : σ.SortSymbol} → Variable Θ s → Formula σ Γ Δ) (η : Env 𝒩 Γ Δ) :
    (conjunction_m Θ p).satisfies η ↔ ∀ {s} (v : Variable Θ s), (p v).satisfies η := by
  induction Θ with
  | nil =>
    constructor
    · intro _ _ v
      nomatch v
    · intro _
      trivial
  | cons s Θ ih =>
    change (Formula.satisfies η (p .here) ∧ Formula.satisfies η (conjunction_m Θ _)) ↔ _
    rw [ih]
    constructor
    · intro h _ v
      cases v with
      | here => exact h.1
      | there v => exact h.2 v
    · intro h
      exact ⟨h .here, fun v => h (.there v)⟩

end YesMetaZFC.Automation.PrefixQuantification
