import BMSConstructibleBridge.PowerlessAssignmentUpdate

/-!
# 保留原坐标的赋值填充

把 f:k→A 扩展到任意包含 k 的 J；旧坐标保持，新增坐标均取给定 a∈A。
使用实际纯关系的总唯一性构造集合函数，不需要 J 外部有限。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessAssignmentPadding

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def value_m {Γ Δ : SortContext ℒ} (f k a x y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (.conj (SecondOrderObjectSyntax.member_m x k) (SecondOrderObjectSyntax.value_m f x y))
    (.conj (.neg (SecondOrderObjectSyntax.member_m x k)) (.equal y a))

theorem value_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (f k a x y : Term ℒ Γ Δ .set) :
    (value_m f k a x y).satisfies η ↔
      (member_l ℳ (x.eval η) (k.eval η) ∧ value_l (f.eval η) (x.eval η) (y.eval η)) ∨
        (¬member_l ℳ (x.eval η) (k.eval η) ∧ y.eval η = a.eval η) := by
  simp only [value_m, Formula.satisfies, ThirdOrderSemantics.value_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {f k J A a : carrier_l ℳ} (hf : map_l f k A) (hJ : subset_l k J) (ha : member_l ℳ a A) :
    ∃ g, map_l g J A ∧
      (∀ x, member_l ℳ x J → ∀ y,
        value_l g x y ↔ (member_l ℳ x k ∧ value_l f x y) ∨ (¬member_l ℳ x k ∧ y = a)) ∧
      ∀ x y, value_l f x y → value_l g x y := by
  classical
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 3 :=
    { bound := Fin.cases f (Fin.cases k (fun _ => a)), free := fun _ => A }
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] :=
    value_m (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here))))) (.fvar (.there .here)) (.fvar .here)
  have h : ∀ x y, φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) ↔
      (member_l ℳ x k ∧ value_l f x y) ∨ (¬member_l ℳ x k ∧ y = a) := by
    intro x y
    exact value_formula_l _ _ _ _ _ _
  obtain ⟨g, B, hg, _, h₀⟩ := PowerlessMapping.exists_l hℳ φ η J
    (fun x _ => by
      by_cases hx : member_l ℳ x k
      · obtain ⟨y, hy, _⟩ := hf.2 x hx
        exact ⟨y, (h x y).mpr (Or.inl ⟨hx, hy.2⟩)⟩
      · exact ⟨a, (h x a).mpr (Or.inr ⟨hx, rfl⟩)⟩)
    (fun x _ y z hy hz => by
      rcases (h x y).mp hy with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · rcases (h x z).mp hz with ⟨_, hz⟩ | ⟨hx₀, _⟩
        · exact PowerlessFunction.value_unique_l hℳ hf hy hz
        · exact (hx₀ hx).elim
      · rcases (h x z).mp hz with ⟨hx₀, _⟩ | ⟨_, hz⟩
        · exact (hx hx₀).elim
        · exact hy.trans hz.symm)
  have h₁ : ∀ x, member_l ℳ x J → ∀ y,
      value_l g x y ↔ (member_l ℳ x k ∧ value_l f x y) ∨ (¬member_l ℳ x k ∧ y = a) :=
    fun x hx y => (h₀ x hx y).trans (h x y)
  refine ⟨g, PowerlessFunction.range_l hℳ hg ?_, h₁, ?_⟩
  · intro x y hy
    rcases (h₁ x (PowerlessFunction.value_mem_l hℳ hg hy).1 y).mp hy with ⟨_, hy⟩ | ⟨_, hy⟩
    · exact (PowerlessFunction.value_mem_l hℳ hf hy).2
    · exact hy.symm ▸ ha
  intro x y hy
  have hx := (PowerlessFunction.value_mem_l hℳ hf hy).1
  exact (h₁ x (hJ x hx) y).mpr (Or.inl ⟨hx, hy⟩)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessAssignmentPadding
