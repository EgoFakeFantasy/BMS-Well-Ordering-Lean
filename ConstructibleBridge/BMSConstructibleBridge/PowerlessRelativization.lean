import BMSConstructibleBridge.PowerlessMemberStructure

/-!
# 原纯集合公式对成员域的相对化

只在原 Formula 中增加一个自由域参数，并限制原量词的取值。
不增加语法树、满足关系公理或内部核心前提；域参数不被当成域内元素。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativization

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

def formula_m {Γ Δ : SortContext ℒ} : Formula ℒ Γ Δ → Formula ℒ Γ (.set :: Δ)
  | .falsum => .falsum
  | .truth => .truth
  | .rel r a => .rel r (a.weakenFree SetTheory.SetSort.set)
  | .equal s t => .equal (s.weakenFree SetTheory.SetSort.set) (t.weakenFree SetTheory.SetSort.set)
  | .neg φ => .neg (formula_m φ)
  | .conj φ ψ => .conj (formula_m φ) (formula_m ψ)
  | .disj φ ψ => .disj (formula_m φ) (formula_m ψ)
  | .imp φ ψ => .imp (formula_m φ) (formula_m ψ)
  | .iff φ ψ => .iff (formula_m φ) (formula_m ψ)
  | .forallE .set φ => .forallE .set (.imp
      (SecondOrderObjectSyntax.member_m (.bvar .here) (.fvar .here)) (formula_m φ))
  | .existsE .set φ => .existsE .set (.conj
      (SecondOrderObjectSyntax.member_m (.bvar .here) (.fvar .here)) (formula_m φ))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {A : carrier_l ℳ}
  {hA : ∃ x, member_l ℳ x A} {Γ Δ : SortContext ℒ}

def env_l (η : Env (structure_l A hA) Γ Δ) : Env ℳ Γ Δ where
  boundVal {s} v := match s with | .set => (η.boundVal v).val
  freeVal {s} v := match s with | .set => (η.freeVal v).val

theorem term_l (η : Env (structure_l A hA) Γ Δ) (t : Term ℒ Γ Δ .set) :
    (t.weakenFree SetTheory.SetSort.set).eval ((env_l η).pushFree A) = (t.eval η).val := by
  match t with
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .app f _ => nomatch f

theorem push_l (η : Env (structure_l A hA) Γ Δ) (x : type_l A) :
    (env_l (η.pushBound (sort := SetTheory.SetSort.set) x)).pushFree A =
      ((env_l η).pushFree A).pushBound (sort := SetTheory.SetSort.set) x.val := by
  apply Env.ext
  · intro s v
    cases s
    cases v <;> rfl
  · intro s v
    cases s
    cases v <;> rfl

theorem formula_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ Γ Δ) (η : Env (structure_l A hA) Γ Δ) :
    (formula_m φ).satisfies ((env_l η).pushFree A) ↔ φ.satisfies η := by
  match φ with
  | .falsum => rfl
  | .truth => rfl
  | .rel .membership (.cons s (.cons t .nil)) =>
      change member_l ℳ ((s.weakenFree SetTheory.SetSort.set).eval ((env_l η).pushFree A))
        ((t.weakenFree SetTheory.SetSort.set).eval ((env_l η).pushFree A)) ↔ member_l ℳ (s.eval η).val (t.eval η).val
      rw [term_l, term_l]
  | .equal (sort := SetTheory.SetSort.set) s t =>
      change (s.weakenFree SetTheory.SetSort.set).eval ((env_l η).pushFree A) =
        (t.weakenFree SetTheory.SetSort.set).eval ((env_l η).pushFree A) ↔ s.eval η = t.eval η
      rw [term_l, term_l]
      exact ⟨Subtype.ext, congrArg Subtype.val⟩
  | .neg φ => exact not_congr (formula_l φ η)
  | .conj φ ψ => exact and_congr (formula_l φ η) (formula_l ψ η)
  | .disj φ ψ => exact or_congr (formula_l φ η) (formula_l ψ η)
  | .imp φ ψ => exact imp_congr (formula_l φ η) (formula_l ψ η)
  | .iff φ ψ => exact iff_congr (formula_l φ η) (formula_l ψ η)
  | .forallE .set φ =>
      change (∀ x : carrier_l ℳ, member_l ℳ x A →
        (formula_m φ).satisfies (((env_l η).pushFree A).pushBound x)) ↔
        ∀ x : type_l A, φ.satisfies (η.pushBound x)
      have h (x : type_l A) := formula_l φ (η.pushBound x)
      simp only [push_l] at h
      exact ⟨fun hφ x => (h x).mp (hφ x.val x.property),
        fun hφ x hx => (h ⟨x, hx⟩).mpr (hφ ⟨x, hx⟩)⟩
  | .existsE .set φ =>
      change (∃ x : carrier_l ℳ, member_l ℳ x A ∧
        (formula_m φ).satisfies (((env_l η).pushFree A).pushBound x)) ↔
        ∃ x : type_l A, φ.satisfies (η.pushBound x)
      have h (x : type_l A) := formula_l φ (η.pushBound x)
      simp only [push_l] at h
      constructor
      · rintro ⟨x, hx, hφ⟩
        exact ⟨⟨x, hx⟩, (h ⟨x, hx⟩).mp hφ⟩
      · rintro ⟨x, hφ⟩
        exact ⟨x.val, x.property, (h x).mpr hφ⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativization
