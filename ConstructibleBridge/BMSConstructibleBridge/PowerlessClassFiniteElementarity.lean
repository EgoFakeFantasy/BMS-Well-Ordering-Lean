import BMSConstructibleBridge.PowerlessSourceClassInclusion
import BMSConstructibleBridge.PowerlessClassRelativeParameters

/-! # 虚拟子域与可定义类的有限元素性对象公式

原绑定变量按虚拟域守卫，原自由参数经指定替换代入。类和虚拟域
均可只有一元定义而无集合载体；其余元数据不要求在任一域内。
这里只从原请求闭包装配对象公式，实际程序消去闭包前提在后续完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassFiniteElementarity

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  PowerlessSourceClass.structure_l PowerlessSourceClass.type_l

universe u

variable {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ}

abbrev family_m (Δ : SortContext ℒ) := List (Σ Γ : SortContext ℒ, Formula ℒ Γ Δ)

def requests_m {Δ : SortContext ℒ} (Φ : family_m Δ) :
    List (Σ n : Nat, Formula ℒ [] (.set :: (List.replicate n .set ++ Δ))) :=
  Φ.flatMap fun p => PowerlessSourceRequests.requests_m .truth p.2

private theorem free_eq_l {Γ Θ : SortContext ℒ} (ξ : Env 𝒱 Γ Θ) (ζ : Env 𝒱 [] Θ)
    (h : ∀ s (v : Variable Θ s), ξ.freeVal v = ζ.freeVal v) :
    PowerlessSourceClass.free_l ξ = ζ := by
  apply Env.ext
  · intro _ v
    nomatch v
  · intro s v
    exact h s v

private theorem eval_l {Γ Θ : SortContext ℒ} (t : Term ℒ [] Θ .set)
    (ξ : Env 𝒱 Γ Θ) (ζ : Env 𝒱 [] Θ)
    (h : ∀ s (v : Variable Θ s), ξ.freeVal v = ζ.freeVal v) :
    (t.embedBoundClosed Γ).eval ξ = t.eval ζ := by
  match t with
  | .bvar v => nomatch v
  | .fvar v => simpa only [Term.embedBoundClosed_fvar, Term.eval] using h _ v
  | .app f _ => nomatch f

private theorem domain_l {Γ Θ : SortContext ℒ} {I : carrier_l 𝒱 → Prop}
    (E : Formula ℒ [] (.set :: Θ)) (ξ : Env 𝒱 Γ Θ) (ζ : Env 𝒱 [] Θ)
    (hξ : ∀ s (v : Variable Θ s), ξ.freeVal v = ζ.freeVal v)
    (hE : ∀ x, E.satisfies (ζ.pushFree x) ↔ I x) (t : Term ℒ Γ Θ .set) :
    (PowerlessSourceClass.domain_m E t).satisfies ξ ↔ I (t.eval ξ) := by
  rw [PowerlessSourceClass.domain_formula_l, free_eq_l ξ ζ hξ]
  exact hE (t.eval ξ)

def parameters_m {Θ : SortContext ℒ} (E : Formula ℒ [] (.set :: Θ)) :
    {Δ : SortContext ℒ} → VariableSubstitution ℒ Δ [] Θ → Formula ℒ [] Θ
  | List.nil, _ => .truth
  | List.cons .set _, ν => .conj (PowerlessSourceClass.domain_m E (ν .here))
      (parameters_m E (fun v => ν (.there v)))

theorem parameters_formula_l {Δ Θ : SortContext ℒ} {I : carrier_l 𝒱 → Prop}
    (E : Formula ℒ [] (.set :: Θ)) (ν : VariableSubstitution ℒ Δ [] Θ) (ζ : Env 𝒱 [] Θ)
    (hE : ∀ x, E.satisfies (ζ.pushFree x) ↔ I x) :
    (parameters_m E ν).satisfies ζ ↔ ∀ v : Variable Δ .set, I ((ν v).eval ζ) := by
  match Δ with
  | [] =>
    constructor
    · intro _ v
      nomatch v
    · intro _
      trivial
  | .set :: Δ =>
    change (_ ∧ _) ↔ _
    rw [domain_l E ζ ζ (fun _ _ => rfl) hE,
      parameters_formula_l E (fun v => ν (.there v)) ζ hE]
    constructor
    · rintro ⟨h₀, h₁⟩ v
      cases v with
      | here => exact h₀
      | there v => exact h₁ v
    · intro h
      exact ⟨h .here, fun v => h (.there v)⟩

private def instance_m {Γ Δ Θ : SortContext ℒ} (D : Formula ℒ [] (.set :: Θ))
    (φ : Formula ℒ Γ Δ) (ν : VariableSubstitution ℒ Δ [] Θ) : Formula ℒ Γ Θ :=
  PowerlessClassRelativeParameters.form_m D φ (fun v => .bvar v)
    (VariableSubstitution.embedBoundClosed Γ ν)

private def quantify_m {Θ : SortContext ℒ} (E : Formula ℒ [] (.set :: Θ)) :
    {Γ : SortContext ℒ} → Formula ℒ Γ Θ → Formula ℒ [] Θ
  | List.nil, φ => φ
  | List.cons .set _, φ => quantify_m E (.forallE .set
      (.imp (PowerlessSourceClass.domain_m E (.bvar .here)) φ))

private theorem quantify_l {Γ Θ : SortContext ℒ} {I : carrier_l 𝒱 → Prop}
    (E : Formula ℒ [] (.set :: Θ)) (φ : Formula ℒ Γ Θ) (ζ : Env 𝒱 [] Θ)
    (hE : ∀ x, E.satisfies (ζ.pushFree x) ↔ I x) :
    (quantify_m E φ).satisfies ζ ↔ ∀ ξ : Env 𝒱 Γ Θ,
      (∀ s (v : Variable Θ s), ξ.freeVal v = ζ.freeVal v) →
      (∀ v : Variable Γ .set, I (ξ.boundVal v)) → φ.satisfies ξ := by
  induction Γ with
  | nil =>
    rw [quantify_m]
    constructor
    · intro h ξ hξ _
      have hη : ξ = ζ := by
        apply Env.ext
        · intro _ v; nomatch v
        · intro s v
          exact hξ s v
      simpa only [hη] using h
    · intro h
      exact h ζ (fun _ _ => rfl) (fun v => nomatch v)
  | cons s Γ ih =>
    cases s
    rw [quantify_m, ih]
    constructor
    · intro h ξ hξ hBound
      let ξ₀ := PowerlessSourceOpening.tail_l ξ
      have h₀ := h ξ₀ hξ (fun v => hBound (.there v))
      change ∀ x, (PowerlessSourceClass.domain_m E (.bvar .here)).satisfies (ξ₀.pushBound x) →
        φ.satisfies (ξ₀.pushBound x) at h₀
      have hx := (domain_l E (ξ₀.pushBound (ξ.boundVal .here)) ζ hξ hE (.bvar .here)).mpr
        (hBound .here)
      have hη : ξ₀.pushBound (ξ.boundVal .here) = ξ := by
        apply Env.ext
        · intro _ v; cases v <;> rfl
        · intro _ _; rfl
      simpa only [hη] using h₀ (ξ.boundVal .here) hx
    · intro h ξ hξ hBound
      change ∀ x, (PowerlessSourceClass.domain_m E (.bvar .here)).satisfies (ξ.pushBound x) →
        φ.satisfies (ξ.pushBound x)
      intro x hx
      have hxI := (domain_l E (ξ.pushBound x) ζ hξ hE (.bvar .here)).mp hx
      exact h (ξ.pushBound x) hξ (fun v => by
        cases v with
        | here => exact hxI
        | there v => exact hBound v)

def entry_m {Γ Δ Θ : SortContext ℒ} (D E : Formula ℒ [] (.set :: Θ))
    (φ : Formula ℒ Γ Δ) (ν : VariableSubstitution ℒ Δ [] Θ) : Formula ℒ [] Θ :=
  quantify_m E (.iff (instance_m D φ ν) (instance_m E φ ν))

def form_m {Δ Θ : SortContext ℒ} (D E : Formula ℒ [] (.set :: Θ))
    (Φ : family_m Δ) (ν : VariableSubstitution ℒ Δ [] Θ) : Formula ℒ [] Θ :=
  match Φ with
  | [] => .truth
  | p :: Φ => .conj (entry_m D E p.2 ν) (form_m D E Φ ν)

variable {I P : carrier_l 𝒱 → Prop} {hI : ∃ x, I x} {hP : ∃ x, P x}

local notation "𝒩" => PowerlessSourceClass.structure_l (ℳ := 𝒱) I hI

/-- 对象元素性正文只消费原类请求闭包，不要求虚拟域传递。 -/
theorem entry_l {Γ Δ Θ : SortContext ℒ} (D E : Formula ℒ [] (.set :: Θ))
    (φ : Formula ℒ Γ Δ) (ν : VariableSubstitution ℒ Δ [] Θ) (ζ : Env 𝒱 [] Θ)
    (η : Env 𝒩 [] Δ) (hIP : ∀ x, I x → P x)
    (hν : ∀ v : Variable Δ .set, (ν v).eval ζ = (η.freeVal v).val)
    (hD : ∀ x, D.satisfies (ζ.pushFree x) ↔ P x)
    (hE : ∀ x, E.satisfies (ζ.pushFree x) ↔ I x)
    (h : PowerlessSourcePredicateRequests.closed_l (PowerlessSourceRequests.requests_m .truth φ)
      (PowerlessSourceClass.free_l (PowerlessSourceClassInclusion.env_l (hP := hP) hIP η))
      (fun x => I x.val)) : (entry_m D E φ ν).satisfies ζ := by
  apply (quantify_l E _ ζ hE).mpr
  intro ξ hξ hBound
  let η₀ : Env 𝒩 Γ Δ :=
    { boundVal := fun {s} v => match s with | .set => ⟨ξ.boundVal v, hBound v⟩
      freeVal := η.freeVal }
  have hFree : PowerlessSourceClass.free_l
      (PowerlessSourceClassInclusion.env_l (hP := hP) hIP η₀) =
        PowerlessSourceClass.free_l (PowerlessSourceClassInclusion.env_l (hP := hP) hIP η) := by
    apply Env.ext
    · intro _ v; nomatch v
    · intro _ _; rfl
  have hφ := PowerlessSourceClassInclusion.formula_l (hP := hP) hIP φ η₀
    (by simpa only [hFree] using h)
  have hPull : ξ.pullback (.map (fun v => .bvar v)
      (VariableSubstitution.embedBoundClosed Γ ν)) = PowerlessSourceClass.env_l η₀ := by
    apply Env.ext
    · intro s v; cases s; rfl
    · intro s v
      cases s
      exact (eval_l (ν v) ξ ζ hξ).trans (hν v)
  have hEnv : PowerlessSourceClass.env_l
      (PowerlessSourceClassInclusion.env_l (hP := hP) hIP η₀) =
        PowerlessSourceClass.env_l η₀ := by
    apply Env.ext <;> intro _ _ <;> rfl
  have hD₀ (x : carrier_l 𝒱) :
      D.satisfies ((PowerlessSourceClass.free_l ξ).pushFree x) ↔ P x := by
    rw [free_eq_l ξ ζ hξ]
    exact hD x
  have hE₀ (x : carrier_l 𝒱) :
      E.satisfies ((PowerlessSourceClass.free_l ξ).pushFree x) ↔ I x := by
    rw [free_eq_l ξ ζ hξ]
    exact hE x
  have h₀ := PowerlessClassRelativeParameters.formula_l D φ (fun v => .bvar v)
    (VariableSubstitution.embedBoundClosed Γ ν) ξ
    (PowerlessSourceClassInclusion.env_l (hP := hP) hIP η₀) (hPull.trans hEnv.symm) hD₀
  have h₁ := PowerlessClassRelativeParameters.formula_l E φ (fun v => .bvar v)
    (VariableSubstitution.embedBoundClosed Γ ν) ξ η₀ hPull hE₀
  exact (h₀.trans hφ).trans h₁.symm

theorem formula_l {Δ Θ : SortContext ℒ} (D E : Formula ℒ [] (.set :: Θ))
    (Φ : family_m Δ) (ν : VariableSubstitution ℒ Δ [] Θ) (ζ : Env 𝒱 [] Θ)
    (η : Env 𝒩 [] Δ) (hIP : ∀ x, I x → P x)
    (hν : ∀ v : Variable Δ .set, (ν v).eval ζ = (η.freeVal v).val)
    (hD : ∀ x, D.satisfies (ζ.pushFree x) ↔ P x)
    (hE : ∀ x, E.satisfies (ζ.pushFree x) ↔ I x)
    (h : ∀ p ∈ Φ, PowerlessSourcePredicateRequests.closed_l
      (PowerlessSourceRequests.requests_m .truth p.2)
      (PowerlessSourceClass.free_l (PowerlessSourceClassInclusion.env_l (hP := hP) hIP η))
      (fun x => I x.val)) : (form_m D E Φ ν).satisfies ζ := by
  induction Φ with
  | nil => trivial
  | cons p Φ ih =>
    exact ⟨entry_l D E p.2 ν ζ η hIP hν hD hE (h p List.mem_cons_self),
      ih (fun q hq => h q (List.mem_cons_of_mem _ hq))⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassFiniteElementarity
