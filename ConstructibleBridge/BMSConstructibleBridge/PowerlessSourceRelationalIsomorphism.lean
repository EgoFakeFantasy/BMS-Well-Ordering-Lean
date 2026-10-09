import BMSConstructibleBridge.PowerlessSourceClass

/-! # 纯隶属公式沿总同构关系的传输

只消费两个方向的存在见证、等式及隶属双向对应。不从存在唯一性
抽取 Type 同构函数；公式量词分支在 Prop 中逐次使用关系见证。
这里的递归对象是原外部公式 AST，不是模型内部 ω 或集合的外部秩。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceRelationalIsomorphism

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u v

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  {𝒩 : FirstOrder.Structure.{0, 0, 0, v} ℒ}

def related_l {Γ Δ : SortContext ℒ} (R : carrier_l ℳ → carrier_l 𝒩 → Prop)
    (η : Env ℳ Γ Δ) (ξ : Env 𝒩 Γ Δ) : Prop :=
  (∀ x : Variable Γ .set, R (η.boundVal x) (ξ.boundVal x)) ∧
    ∀ x : Variable Δ .set, R (η.freeVal x) (ξ.freeVal x)

theorem term_l {Γ Δ : SortContext ℒ} (R : carrier_l ℳ → carrier_l 𝒩 → Prop)
    (η : Env ℳ Γ Δ) (ξ : Env 𝒩 Γ Δ) (h : related_l R η ξ)
    (t : Term ℒ Γ Δ .set) : R (t.eval η) (t.eval ξ) := by
  match t with
  | .bvar x => exact h.1 x
  | .fvar x => exact h.2 x
  | .app f _ => nomatch f

theorem push_l {Γ Δ : SortContext ℒ} (R : carrier_l ℳ → carrier_l 𝒩 → Prop)
    (η : Env ℳ Γ Δ) (ξ : Env 𝒩 Γ Δ) (h : related_l R η ξ)
    {x : carrier_l ℳ} {y : carrier_l 𝒩} (hxy : R x y) :
    related_l R (η.pushBound x) (ξ.pushBound y) := by
  constructor
  · intro z
    cases z with
    | here => exact hxy
    | there z => exact h.1 z
  · exact h.2

/-- 满域关系保持每个原公式，包括两个方向的量词见证。 -/
theorem formula_l {Γ Δ : SortContext ℒ} (R : carrier_l ℳ → carrier_l 𝒩 → Prop)
    (hTotal : ∀ x, ∃ y, R x y) (hOnto : ∀ y, ∃ x, R x y)
    (hEq : ∀ {x z y w}, R x y → R z w → (x = z ↔ y = w))
    (hMem : ∀ {x z y w}, R x y → R z w → (member_l ℳ x z ↔ member_l 𝒩 y w))
    (φ : Formula ℒ Γ Δ) (η : Env ℳ Γ Δ) (ξ : Env 𝒩 Γ Δ) (h : related_l R η ξ) :
    φ.satisfies η ↔ φ.satisfies ξ := by
  match φ with
  | .falsum | .truth => exact Iff.rfl
  | .rel .membership (.cons s (.cons t .nil)) =>
    exact hMem (term_l R η ξ h s) (term_l R η ξ h t)
  | .equal (sort := .set) s t => exact hEq (term_l R η ξ h s) (term_l R η ξ h t)
  | .neg φ => exact not_congr (formula_l R hTotal hOnto hEq hMem φ η ξ h)
  | .conj φ ψ =>
    exact and_congr (formula_l R hTotal hOnto hEq hMem φ η ξ h)
      (formula_l R hTotal hOnto hEq hMem ψ η ξ h)
  | .disj φ ψ =>
    exact or_congr (formula_l R hTotal hOnto hEq hMem φ η ξ h)
      (formula_l R hTotal hOnto hEq hMem ψ η ξ h)
  | .imp φ ψ =>
    exact imp_congr (formula_l R hTotal hOnto hEq hMem φ η ξ h)
      (formula_l R hTotal hOnto hEq hMem ψ η ξ h)
  | .iff φ ψ =>
    exact iff_congr (formula_l R hTotal hOnto hEq hMem φ η ξ h)
      (formula_l R hTotal hOnto hEq hMem ψ η ξ h)
  | .forallE .set φ =>
    change (∀ x, φ.satisfies (η.pushBound x)) ↔ ∀ y, φ.satisfies (ξ.pushBound y)
    constructor
    · intro hφ y
      obtain ⟨x, hxy⟩ := hOnto y
      exact (formula_l R hTotal hOnto hEq hMem φ _ _ (push_l R η ξ h hxy)).mp (hφ x)
    · intro hφ x
      obtain ⟨y, hxy⟩ := hTotal x
      exact (formula_l R hTotal hOnto hEq hMem φ _ _ (push_l R η ξ h hxy)).mpr (hφ y)
  | .existsE .set φ =>
    change (∃ x, φ.satisfies (η.pushBound x)) ↔ ∃ y, φ.satisfies (ξ.pushBound y)
    constructor
    · rintro ⟨x, hφ⟩
      obtain ⟨y, hxy⟩ := hTotal x
      exact ⟨y, (formula_l R hTotal hOnto hEq hMem φ _ _ (push_l R η ξ h hxy)).mp hφ⟩
    · rintro ⟨y, hφ⟩
      obtain ⟨x, hxy⟩ := hOnto y
      exact ⟨x, (formula_l R hTotal hOnto hEq hMem φ _ _ (push_l R η ξ h hxy)).mpr hφ⟩

#print axioms term_l
#print axioms push_l
#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceRelationalIsomorphism
