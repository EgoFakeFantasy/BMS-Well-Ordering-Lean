import BMSConstructibleBridge.PowerlessSourceOpening

/-!
# 实际子公式请求与有限反射准则

存在量词请求原矩阵的见证；全称量词请求反例矩阵的见证。
原矩阵先按给定类域相对化，再把实际绑定变量变为有限输入。
闭包准则消费这些实际请求，不把任意列表闭包冒充反射。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceRequests

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  PowerlessSourceClass.structure_l PowerlessSourceClass.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def entry_m {Γ Δ : SortContext ℒ} (D : Formula ℒ [] (.set :: Δ))
    (φ : Formula ℒ (.set :: Γ) Δ) :
    Σ n : Nat, Formula ℒ [] (.set :: (List.replicate n .set ++ Δ)) :=
  ⟨Γ.length, PowerlessSourceOpening.form_m (PowerlessSourceClass.form_m D φ)⟩

def requests_m {Γ Δ : SortContext ℒ} (D : Formula ℒ [] (.set :: Δ)) :
    Formula ℒ Γ Δ → List (Σ n : Nat, Formula ℒ [] (.set :: (List.replicate n .set ++ Δ)))
  | .falsum | .truth | .rel _ _ | .equal _ _ => []
  | .neg φ => requests_m D φ
  | .conj φ ψ | .disj φ ψ | .imp φ ψ | .iff φ ψ => requests_m D φ ++ requests_m D ψ
  | .forallE .set φ => entry_m D (.neg φ) :: requests_m D φ
  | .existsE .set φ => entry_m D φ :: requests_m D φ

def closed_l {Δ : SortContext ℒ}
    (Φ : List (Σ n : Nat, Formula ℒ [] (.set :: (List.replicate n .set ++ Δ))))
    (η : Env ℳ [] Δ) (A : carrier_l ℳ) (P : carrier_l ℳ → Prop) : Prop :=
  ∀ n φ, Sigma.mk n φ ∈ Φ → ∀ v, PowerlessSourceTuple.bounded_l A n v →
    (∃ y, P y ∧ φ.satisfies ((PowerlessSourceTuple.env_l η n v).pushFree y)) →
      ∃ y, member_l ℳ y A ∧ φ.satisfies ((PowerlessSourceTuple.env_l η n v).pushFree y)

theorem subset_l {Δ : SortContext ℒ}
    {Φ : List (Σ n : Nat, Formula ℒ [] (.set :: (List.replicate (α := (ℒ).SortSymbol) n .set ++ Δ)))}
    {Ψ : List (Σ n : Nat, Formula ℒ [] (.set :: (List.replicate (α := (ℒ).SortSymbol) n .set ++ Δ)))}
    {η : Env ℳ [] Δ} {A : carrier_l ℳ} {P : carrier_l ℳ → Prop}
    (h : ∀ p ∈ Ψ, p ∈ Φ) (hΦ : closed_l Φ η A P) : closed_l Ψ η A P :=
  fun n φ hφ => hΦ n φ (h _ hφ)

theorem witness_l {Γ Δ : SortContext ℒ} (D : Formula ℒ [] (.set :: Δ))
    (φ : Formula ℒ (.set :: Γ) Δ) (η : Env ℳ Γ Δ) (A : carrier_l ℳ) (P : carrier_l ℳ → Prop)
    {Φ : List (Σ n : Nat, Formula ℒ [] (.set :: (List.replicate (α := (ℒ).SortSymbol) n .set ++ Δ)))}
    (hφ : entry_m D φ ∈ Φ) (hη : ∀ v : Variable Γ .set, member_l ℳ (η.boundVal v) A)
    (h : closed_l Φ (PowerlessSourceClass.free_l η) A P)
    (h₀ : ∃ y, P y ∧ (PowerlessSourceClass.form_m D φ).satisfies (η.pushBound y)) :
    ∃ y, member_l ℳ y A ∧ (PowerlessSourceClass.form_m D φ).satisfies (η.pushBound y) := by
  obtain ⟨y, hy, h₀⟩ := h₀
  obtain ⟨z, hz, h₁⟩ := h Γ.length _ hφ (PowerlessSourceOpening.values_l η)
    (PowerlessSourceOpening.bounded_l η A hη)
    ⟨y, hy, (PowerlessSourceOpening.witness_l (PowerlessSourceClass.form_m D φ) η y).mpr h₀⟩
  exact ⟨z, hz, (PowerlessSourceOpening.witness_l (PowerlessSourceClass.form_m D φ) η z).mp h₁⟩

/-- 对实际子公式请求关闭的集合，反射该原公式的类相对化真值。 -/
theorem reflection_l {A : carrier_l ℳ} {hA : ∃ x, member_l ℳ x A}
    (P : carrier_l ℳ → Prop) (hAP : ∀ x, member_l ℳ x A → P x)
    {Γ Δ : SortContext ℒ} (D : Formula ℒ [] (.set :: Δ)) (φ : Formula ℒ Γ Δ)
    (η : Env (PowerlessSourceClass.structure_l (fun x => member_l ℳ x A) hA) Γ Δ)
    (hD : ∀ x, D.satisfies ((PowerlessSourceClass.free_l (PowerlessSourceClass.env_l η)).pushFree x) ↔ P x)
    (h : closed_l (requests_m D φ) (PowerlessSourceClass.free_l (PowerlessSourceClass.env_l η)) A P) :
    (PowerlessSourceClass.form_m D φ).satisfies (PowerlessSourceClass.env_l η) ↔ φ.satisfies η := by
  classical
  match φ with
  | .falsum => exact Iff.rfl
  | .truth => exact Iff.rfl
  | .rel .membership (.cons s (.cons t .nil)) =>
    change member_l ℳ (s.eval (PowerlessSourceClass.env_l η)) (t.eval (PowerlessSourceClass.env_l η)) ↔
      member_l ℳ (s.eval η).val (t.eval η).val
    rw [PowerlessSourceClass.term_l, PowerlessSourceClass.term_l]
  | .equal (sort := .set) s t =>
    change s.eval (PowerlessSourceClass.env_l η) = t.eval (PowerlessSourceClass.env_l η) ↔ s.eval η = t.eval η
    rw [PowerlessSourceClass.term_l, PowerlessSourceClass.term_l]
    exact ⟨Subtype.ext, fun h => congrArg Subtype.val h⟩
  | .neg φ => exact not_congr (reflection_l P hAP D φ η hD h)
  | .conj φ ψ =>
    exact and_congr
      (reflection_l P hAP D φ η hD (subset_l (fun _ hφ => List.mem_append_left _ hφ) h))
      (reflection_l P hAP D ψ η hD (subset_l (fun _ hψ => List.mem_append_right _ hψ) h))
  | .disj φ ψ =>
    exact or_congr
      (reflection_l P hAP D φ η hD (subset_l (fun _ hφ => List.mem_append_left _ hφ) h))
      (reflection_l P hAP D ψ η hD (subset_l (fun _ hψ => List.mem_append_right _ hψ) h))
  | .imp φ ψ =>
    exact imp_congr
      (reflection_l P hAP D φ η hD (subset_l (fun _ hφ => List.mem_append_left _ hφ) h))
      (reflection_l P hAP D ψ η hD (subset_l (fun _ hψ => List.mem_append_right _ hψ) h))
  | .iff φ ψ =>
    exact iff_congr
      (reflection_l P hAP D φ η hD (subset_l (fun _ hφ => List.mem_append_left _ hφ) h))
      (reflection_l P hAP D ψ η hD (subset_l (fun _ hψ => List.mem_append_right _ hψ) h))
  | .existsE .set φ =>
    have h₀ := subset_l (Ψ := requests_m D φ) (fun _ hφ => List.mem_cons_of_mem _ hφ) h
    have h₁ (x : {x : carrier_l ℳ // member_l ℳ x A}) :
        (PowerlessSourceClass.form_m D φ).satisfies ((PowerlessSourceClass.env_l η).pushBound x.val) ↔
          φ.satisfies (η.pushBound x) := by
      rw [← PowerlessSourceClass.push_l]
      exact reflection_l P hAP D φ (η.pushBound x) hD h₀
    have h₂ (x : carrier_l ℳ) :
        (PowerlessSourceClass.domain_m D (.bvar .here)).satisfies
          ((PowerlessSourceClass.env_l η).pushBound (sort := SetTheory.SetSort.set) x) ↔ P x :=
      (PowerlessSourceClass.domain_formula_l D _ _).trans (hD x)
    change (∃ x, (PowerlessSourceClass.domain_m D (.bvar .here)).satisfies
      ((PowerlessSourceClass.env_l η).pushBound x) ∧
      (PowerlessSourceClass.form_m D φ).satisfies ((PowerlessSourceClass.env_l η).pushBound x)) ↔
        ∃ x, φ.satisfies (η.pushBound x)
    constructor
    · rintro ⟨x, hx, hφ⟩
      obtain ⟨z, hz, hψ⟩ := witness_l D φ (PowerlessSourceClass.env_l η) A P
        List.mem_cons_self (fun v => (η.boundVal v).property) h ⟨x, (h₂ x).mp hx, hφ⟩
      exact ⟨⟨z, hz⟩, (h₁ ⟨z, hz⟩).mp hψ⟩
    · rintro ⟨x, hφ⟩
      exact ⟨x.val, (h₂ x.val).mpr (hAP x.val x.property), (h₁ x).mpr hφ⟩
  | .forallE .set φ =>
    have h₀ := subset_l (Ψ := requests_m D φ) (fun _ hφ => List.mem_cons_of_mem _ hφ) h
    have h₁ (x : {x : carrier_l ℳ // member_l ℳ x A}) :
        (PowerlessSourceClass.form_m D φ).satisfies ((PowerlessSourceClass.env_l η).pushBound x.val) ↔
          φ.satisfies (η.pushBound x) := by
      rw [← PowerlessSourceClass.push_l]
      exact reflection_l P hAP D φ (η.pushBound x) hD h₀
    have h₂ (x : carrier_l ℳ) :
        (PowerlessSourceClass.domain_m D (.bvar .here)).satisfies
          ((PowerlessSourceClass.env_l η).pushBound (sort := SetTheory.SetSort.set) x) ↔ P x :=
      (PowerlessSourceClass.domain_formula_l D _ _).trans (hD x)
    change (∀ x, (PowerlessSourceClass.domain_m D (.bvar .here)).satisfies
      ((PowerlessSourceClass.env_l η).pushBound x) →
      (PowerlessSourceClass.form_m D φ).satisfies ((PowerlessSourceClass.env_l η).pushBound x)) ↔
        ∀ x, φ.satisfies (η.pushBound x)
    constructor
    · intro hφ x
      exact (h₁ x).mp (hφ x.val ((h₂ x.val).mpr (hAP x.val x.property)))
    · intro hφ x hx
      by_contra hxφ
      obtain ⟨z, hz, hψ⟩ := witness_l D (.neg φ) (PowerlessSourceClass.env_l η) A P
        List.mem_cons_self (fun v => (η.boundVal v).property) h ⟨x, (h₂ x).mp hx, hxφ⟩
      exact hψ ((h₁ ⟨z, hz⟩).mpr (hφ ⟨z, hz⟩))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceRequests
