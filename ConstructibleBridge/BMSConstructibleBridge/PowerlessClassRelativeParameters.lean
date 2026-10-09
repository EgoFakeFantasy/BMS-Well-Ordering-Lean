import BMSConstructibleBridge.PowerlessSourceClass

/-!
# 类相对公式与原参数环境

先代入原公式参数，再用环境中的一元公式限制量词。只有拉回后的原
参数环境取值于类；承载域定义和编码包的其余环境参数不必在类内。
本模块给出逐公式读出，尚不声称类与环境或虚拟壳之间有元素性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassRelativeParameters

open Logic FirstOrder ThirdOrderSemantics PowerlessSourceClass

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

variable {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def form_m {Γ Δ Ψ Θ : SortContext ℒ} (D : Formula ℒ [] (.set :: Θ))
    (φ : Formula ℒ Γ Δ) (σ : VariableSubstitution ℒ Γ Ψ Θ)
    (ν : VariableSubstitution ℒ Δ Ψ Θ) : Formula ℒ Ψ Θ :=
  PowerlessSourceClass.form_m D (φ.substitute (.map σ ν))

private theorem term_l {P : carrier_l 𝒱 → Prop} {hP : ∃ x, P x}
    {Γ Δ Ψ Θ : SortContext ℒ} (σ : VariableSubstitution ℒ Γ Ψ Θ)
    (ν : VariableSubstitution ℒ Δ Ψ Θ) (ξ : Env 𝒱 Ψ Θ)
    (η : Env (structure_l P hP) Γ Δ)
    (hη : ξ.pullback (.map σ ν) = env_l η) (t : Term ℒ Γ Δ .set) :
    (t.substitute (.map σ ν)).eval ξ = (t.eval η).val := by
  rw [Term.eval_substitute, hη, PowerlessSourceClass.term_l]

/-- 相对化只限定原公式的量词，不把环境元数据误当成原类内参数。 -/
theorem formula_l {P : carrier_l 𝒱 → Prop} {hP : ∃ x, P x}
    {Γ Δ Ψ Θ : SortContext ℒ} (D : Formula ℒ [] (.set :: Θ))
    (φ : Formula ℒ Γ Δ) (σ : VariableSubstitution ℒ Γ Ψ Θ)
    (ν : VariableSubstitution ℒ Δ Ψ Θ) (ξ : Env 𝒱 Ψ Θ)
    (η : Env (structure_l P hP) Γ Δ)
    (hη : ξ.pullback (.map σ ν) = env_l η)
    (hD : ∀ x, D.satisfies ((free_l ξ).pushFree x) ↔ P x) :
    (form_m D φ σ ν).satisfies ξ ↔ φ.satisfies η := by
  match φ with
  | .falsum => exact Iff.rfl
  | .truth => exact Iff.rfl
  | .rel .membership (.cons s (.cons t .nil)) =>
    change member_l 𝒱 ((s.substitute (.map σ ν)).eval ξ)
      ((t.substitute (.map σ ν)).eval ξ) ↔
        member_l 𝒱 (s.eval η).val (t.eval η).val
    rw [term_l σ ν ξ η hη, term_l σ ν ξ η hη]
  | .equal (sort := .set) s t =>
    change (s.substitute (.map σ ν)).eval ξ = (t.substitute (.map σ ν)).eval ξ ↔
      s.eval η = t.eval η
    rw [term_l σ ν ξ η hη, term_l σ ν ξ η hη]
    exact ⟨Subtype.ext, fun h => congrArg Subtype.val h⟩
  | .neg φ => exact not_congr (formula_l D φ σ ν ξ η hη hD)
  | .conj φ ψ =>
    exact and_congr (formula_l D φ σ ν ξ η hη hD) (formula_l D ψ σ ν ξ η hη hD)
  | .disj φ ψ =>
    exact or_congr (formula_l D φ σ ν ξ η hη hD) (formula_l D ψ σ ν ξ η hη hD)
  | .imp φ ψ =>
    exact imp_congr (formula_l D φ σ ν ξ η hη hD) (formula_l D ψ σ ν ξ η hη hD)
  | .iff φ ψ =>
    exact iff_congr (formula_l D φ σ ν ξ η hη hD) (formula_l D ψ σ ν ξ η hη hD)
  | .forallE .set φ =>
    have h₀ (x : carrier_l 𝒱) :
        (domain_m D (.bvar .here)).satisfies (ξ.pushBound x) ↔ P x :=
      (domain_formula_l D _ _).trans (hD x)
    have h₁ (x : type_l P) :
        (form_m D φ (VariableSubstitution.liftBound (σ := ℒ) SetTheory.SetSort.set σ)
          (VariableSubstitution.weakenBound (σ := ℒ) SetTheory.SetSort.set ν)).satisfies
          (ξ.pushBound x.val) ↔ φ.satisfies (η.pushBound x) := by
      apply formula_l D φ _ _ _ _
      · change (ξ.pushBound x.val).pullback
          (Substitution.liftBound (σ := ℒ) SetTheory.SetSort.set (.map σ ν)) = _
        rw [Env.pullback_liftBound, hη, ← push_l]
      · exact hD
    change (∀ x, (domain_m D (.bvar .here)).satisfies (ξ.pushBound x) →
      (form_m D φ (VariableSubstitution.liftBound (σ := ℒ) SetTheory.SetSort.set σ)
        (VariableSubstitution.weakenBound (σ := ℒ) SetTheory.SetSort.set ν)).satisfies
          (ξ.pushBound x)) ↔
        ∀ x, φ.satisfies (η.pushBound x)
    constructor
    · intro h x
      exact (h₁ x).mp (h x.val ((h₀ x.val).mpr x.property))
    · intro h x hx
      exact (h₁ ⟨x, (h₀ x).mp hx⟩).mpr (h ⟨x, (h₀ x).mp hx⟩)
  | .existsE .set φ =>
    have h₀ (x : carrier_l 𝒱) :
        (domain_m D (.bvar .here)).satisfies (ξ.pushBound x) ↔ P x :=
      (domain_formula_l D _ _).trans (hD x)
    have h₁ (x : type_l P) :
        (form_m D φ (VariableSubstitution.liftBound (σ := ℒ) SetTheory.SetSort.set σ)
          (VariableSubstitution.weakenBound (σ := ℒ) SetTheory.SetSort.set ν)).satisfies
          (ξ.pushBound x.val) ↔ φ.satisfies (η.pushBound x) := by
      apply formula_l D φ _ _ _ _
      · change (ξ.pushBound x.val).pullback
          (Substitution.liftBound (σ := ℒ) SetTheory.SetSort.set (.map σ ν)) = _
        rw [Env.pullback_liftBound, hη, ← push_l]
      · exact hD
    change (∃ x, (domain_m D (.bvar .here)).satisfies (ξ.pushBound x) ∧
      (form_m D φ (VariableSubstitution.liftBound (σ := ℒ) SetTheory.SetSort.set σ)
        (VariableSubstitution.weakenBound (σ := ℒ) SetTheory.SetSort.set ν)).satisfies
          (ξ.pushBound x)) ↔
        ∃ x, φ.satisfies (η.pushBound x)
    constructor
    · rintro ⟨x, hx, hφ⟩
      exact ⟨⟨x, (h₀ x).mp hx⟩, (h₁ ⟨x, (h₀ x).mp hx⟩).mp hφ⟩
    · rintro ⟨x, hφ⟩
      exact ⟨x.val, (h₀ x.val).mpr x.property, (h₁ x).mpr hφ⟩

def instance_m {Δ Ψ Θ : SortContext ℒ} (D : Formula ℒ [] (.set :: Θ))
    (φ : Formula ℒ [] Δ) (ν : VariableSubstitution ℒ Δ Ψ Θ) : Formula ℒ Ψ Θ :=
  form_m D φ (fun v => nomatch v) ν

theorem instance_l {P : carrier_l 𝒱 → Prop} {hP : ∃ x, P x}
    {Δ Ψ Θ : SortContext ℒ} (D : Formula ℒ [] (.set :: Θ))
    (φ : Formula ℒ [] Δ) (ν : VariableSubstitution ℒ Δ Ψ Θ)
    (ξ : Env 𝒱 Ψ Θ) (η : Env (structure_l P hP) [] Δ)
    (hν : ∀ (v : Variable Δ .set), (ν v).eval ξ = (η.freeVal v).val)
    (hD : ∀ x, D.satisfies ((free_l ξ).pushFree x) ↔ P x) :
    (instance_m D φ ν).satisfies ξ ↔ φ.satisfies η := by
  apply formula_l D φ _ ν ξ η
  · apply Env.ext
    · intro _ v
      nomatch v
    · intro s v
      cases s
      exact hν v
  · exact hD

#print axioms formula_l
#print axioms instance_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassRelativeParameters
