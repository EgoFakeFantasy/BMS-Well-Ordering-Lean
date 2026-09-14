import BMSConstructibleBridge.PowerlessFunction

/-!
# 集合关系的精确定义域与值域

有序对两坐标都落在关系的二次并内，再由实际纯公式分离得到坐标集合。
这为不同局部递归图提供集合值域界，不预设共同值域或任意幂集。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCoordinates

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem bounds_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (f : carrier_l ℳ) :
    ∃ B, ∀ x y, value_l f x y → member_l ℳ x B ∧ member_l ℳ y B := by
  obtain ⟨A, hA⟩ := PowerlessBasic.union_l hℳ f
  obtain ⟨B, hB⟩ := PowerlessBasic.union_l hℳ A
  refine ⟨B, ?_⟩
  rintro x y ⟨p, hp, s, t, _, ht, h⟩
  have h₀ : member_l ℳ t A := (hA t).mpr ⟨p, hp, (h t).mpr (Or.inr rfl)⟩
  exact ⟨(hB x).mpr ⟨t, h₀, (ht x).mpr (Or.inl rfl)⟩,
    (hB y).mpr ⟨t, h₀, (ht y).mpr (Or.inr rfl)⟩⟩

def domain_m {Γ Δ : SortContext ℒ} (f x : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set (SecondOrderObjectSyntax.value_m (f.weakenBound SetTheory.SetSort.set)
    (x.weakenBound SetTheory.SetSort.set) (.bvar .here))

def range_m {Γ Δ : SortContext ℒ} (f y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set (SecondOrderObjectSyntax.value_m (f.weakenBound SetTheory.SetSort.set)
    (.bvar .here) (y.weakenBound SetTheory.SetSort.set))

theorem domain_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (f x : Term ℒ Γ Δ .set) :
    Formula.satisfies η (domain_m f x) ↔ ∃ y, value_l (f.eval η) (x.eval η) y := by
  simp only [domain_m, Formula.satisfies, value_formula_l, Term.eval_weakenBound]
  rfl

theorem range_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (f y : Term ℒ Γ Δ .set) :
    Formula.satisfies η (range_m f y) ↔ ∃ x, value_l (f.eval η) x (y.eval η) := by
  simp only [range_m, Formula.satisfies, value_formula_l, Term.eval_weakenBound]
  rfl

theorem domain_exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (f : carrier_l ℳ) :
    ∃ A, ∀ x, member_l ℳ x A ↔ ∃ y, value_l f x y := by
  obtain ⟨B, hB⟩ := bounds_l hℳ f
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 1 :=
    { bound := fun _ => f, free := fun _ => f }
  let φ : Formula ℒ [] [.set, .set] := domain_m (.fvar (.there .here)) (.fvar .here)
  have h : ∀ x, φ.satisfies ((PowerlessComprehension.env_l η).pushFree x) ↔ ∃ y, value_l f x y := by
    intro x
    dsimp only [φ]
    rw [domain_formula_l]
    rfl
  obtain ⟨A, hA⟩ := PowerlessComprehension.separation_l hℳ φ η B
  refine ⟨A, fun x => (hA x).trans ?_⟩
  constructor
  · exact fun hx => (h x).mp hx.2
  · rintro ⟨y, hy⟩
    exact ⟨(hB x y hy).1, (h x).mpr ⟨y, hy⟩⟩

theorem range_exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (f : carrier_l ℳ) :
    ∃ B, ∀ y, member_l ℳ y B ↔ ∃ x, value_l f x y := by
  obtain ⟨A, hA⟩ := bounds_l hℳ f
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 1 :=
    { bound := fun _ => f, free := fun _ => f }
  let φ : Formula ℒ [] [.set, .set] := range_m (.fvar (.there .here)) (.fvar .here)
  have h : ∀ y, φ.satisfies ((PowerlessComprehension.env_l η).pushFree y) ↔ ∃ x, value_l f x y := by
    intro y
    dsimp only [φ]
    rw [range_formula_l]
    rfl
  obtain ⟨B, hB⟩ := PowerlessComprehension.separation_l hℳ φ η A
  refine ⟨B, fun y => (hB y).trans ?_⟩
  constructor
  · exact fun hy => (h y).mp hy.2
  · rintro ⟨x, hx⟩
    exact ⟨(hA x y hx).2, (h y).mpr ⟨x, hx⟩⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCoordinates
