import BMSConstructibleBridge.PowerlessSourceWitnessDomain

/-!
# 原公式向可定义类的量词相对化

仍使用原 Formula；类由一个带参数的一元原公式给出。
语义结构取环境模型中该类的实际子类型，不预设类是集合、
满足无幂集核心或具有任何初等性。自由参数在量词下保持不变。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceClass

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def type_l (P : carrier_l ℳ → Prop) := {x : carrier_l ℳ // P x}

def structure_l (P : carrier_l ℳ → Prop) (hP : ∃ x, P x) : FirstOrder.Structure.{0, 0, 0, u} ℒ where
  Carrier _ := type_l P
  nonempty _ := hP.elim fun x hx => ⟨⟨x, hx⟩⟩
  funcInterp f := nomatch f
  relInterp
    | .membership, .cons x (.cons y .nil) => member_l ℳ x.val y.val

def env_l {P : carrier_l ℳ → Prop} {hP : ∃ x, P x} {Γ Δ : SortContext ℒ}
    (η : Env (structure_l P hP) Γ Δ) : Env ℳ Γ Δ where
  boundVal v := (η.boundVal v).val
  freeVal v := (η.freeVal v).val

def free_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) : Env ℳ [] Δ where
  boundVal v := nomatch v
  freeVal v := η.freeVal v

theorem term_l {P : carrier_l ℳ → Prop} {hP : ∃ x, P x} {Γ Δ : SortContext ℒ}
    (η : Env (structure_l P hP) Γ Δ) (t : Term ℒ Γ Δ .set) :
    t.eval (env_l η) = (t.eval η).val := by
  match t with
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .app f _ => nomatch f

theorem push_l {P : carrier_l ℳ → Prop} {hP : ∃ x, P x} {Γ Δ : SortContext ℒ}
    (η : Env (structure_l P hP) Γ Δ) (x : type_l P) :
    env_l (η.pushBound (sort := SetTheory.SetSort.set) x) =
      (env_l η).pushBound (sort := SetTheory.SetSort.set) x.val := by
  apply Env.ext
  · intro s v
    cases v <;> rfl
  · intro _ _
    rfl

def binding_m {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :
    Substitution ℒ [] (.set :: Δ) Γ Δ :=
  .map (fun v => nomatch v) (fun v => match v with
    | .here => t
    | .there v => .fvar v)

def domain_m {Γ Δ : SortContext ℒ} (D : Formula ℒ [] (.set :: Δ)) (t : Term ℒ Γ Δ .set) :
    Formula ℒ Γ Δ := D.substitute (binding_m t)

theorem domain_formula_l {Γ Δ : SortContext ℒ} (D : Formula ℒ [] (.set :: Δ))
    (η : Env ℳ Γ Δ) (t : Term ℒ Γ Δ .set) :
    (domain_m D t).satisfies η ↔ D.satisfies ((free_l η).pushFree (t.eval η)) := by
  rw [domain_m, Formula.satisfies_substitute]
  apply Iff.of_eq
  congr 1
  apply Env.ext
  · intro _ v
    nomatch v
  · intro s v
    cases v <;> rfl

def form_m {Γ Δ : SortContext ℒ} (D : Formula ℒ [] (.set :: Δ)) :
    Formula ℒ Γ Δ → Formula ℒ Γ Δ
  | .falsum => .falsum
  | .truth => .truth
  | .rel r ts => .rel r ts
  | .equal s t => .equal s t
  | .neg φ => .neg (form_m D φ)
  | .conj φ ψ => .conj (form_m D φ) (form_m D ψ)
  | .disj φ ψ => .disj (form_m D φ) (form_m D ψ)
  | .imp φ ψ => .imp (form_m D φ) (form_m D ψ)
  | .iff φ ψ => .iff (form_m D φ) (form_m D ψ)
  | .forallE .set φ => .forallE .set (.imp (domain_m D (.bvar .here)) (form_m D φ))
  | .existsE .set φ => .existsE .set (.conj (domain_m D (.bvar .here)) (form_m D φ))

/-- 逐公式语义对应；这是类相对化，不是类与环境之间的初等性。 -/
theorem formula_l {P : carrier_l ℳ → Prop} {hP : ∃ x, P x} {Γ Δ : SortContext ℒ}
    (D : Formula ℒ [] (.set :: Δ)) (φ : Formula ℒ Γ Δ) (η : Env (structure_l P hP) Γ Δ)
    (hD : ∀ x, D.satisfies ((free_l (env_l η)).pushFree x) ↔ P x) :
    (form_m D φ).satisfies (env_l η) ↔ φ.satisfies η := by
  match φ with
  | .falsum => exact Iff.rfl
  | .truth => exact Iff.rfl
  | .rel .membership (.cons s (.cons t .nil)) =>
    change member_l ℳ (s.eval (env_l η)) (t.eval (env_l η)) ↔
      member_l ℳ (s.eval η).val (t.eval η).val
    rw [term_l, term_l]
  | .equal (sort := .set) s t =>
    change s.eval (env_l η) = t.eval (env_l η) ↔ s.eval η = t.eval η
    rw [term_l, term_l]
    exact ⟨Subtype.ext, fun h => congrArg Subtype.val h⟩
  | .neg φ => exact not_congr (formula_l D φ η hD)
  | .conj φ ψ => exact and_congr (formula_l D φ η hD) (formula_l D ψ η hD)
  | .disj φ ψ => exact or_congr (formula_l D φ η hD) (formula_l D ψ η hD)
  | .imp φ ψ => exact imp_congr (formula_l D φ η hD) (formula_l D ψ η hD)
  | .iff φ ψ => exact iff_congr (formula_l D φ η hD) (formula_l D ψ η hD)
  | .forallE .set φ =>
    have h₀ (x : carrier_l ℳ) :
        (domain_m D (.bvar .here)).satisfies ((env_l η).pushBound (sort := SetTheory.SetSort.set) x) ↔ P x :=
      (domain_formula_l D _ _).trans (hD x)
    have h₁ (x : type_l P) := formula_l D φ (η.pushBound x) hD
    simp only [push_l] at h₁
    change (∀ x, (domain_m D (.bvar .here)).satisfies ((env_l η).pushBound x) →
      (form_m D φ).satisfies ((env_l η).pushBound x)) ↔ ∀ x, φ.satisfies (η.pushBound x)
    constructor
    · intro h x
      exact (h₁ x).mp (h x.val ((h₀ x.val).mpr x.property))
    · intro h x hx
      exact (h₁ ⟨x, (h₀ x).mp hx⟩).mpr (h ⟨x, (h₀ x).mp hx⟩)
  | .existsE .set φ =>
    have h₀ (x : carrier_l ℳ) :
        (domain_m D (.bvar .here)).satisfies ((env_l η).pushBound (sort := SetTheory.SetSort.set) x) ↔ P x :=
      (domain_formula_l D _ _).trans (hD x)
    have h₁ (x : type_l P) := formula_l D φ (η.pushBound x) hD
    simp only [push_l] at h₁
    change (∃ x, (domain_m D (.bvar .here)).satisfies ((env_l η).pushBound x) ∧
      (form_m D φ).satisfies ((env_l η).pushBound x)) ↔ ∃ x, φ.satisfies (η.pushBound x)
    constructor
    · rintro ⟨x, hx, hφ⟩
      exact ⟨⟨x, (h₀ x).mp hx⟩, (h₁ ⟨x, (h₀ x).mp hx⟩).mp hφ⟩
    · rintro ⟨x, hφ⟩
      exact ⟨x.val, (h₀ x.val).mpr x.property, (h₁ x).mpr hφ⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceClass
