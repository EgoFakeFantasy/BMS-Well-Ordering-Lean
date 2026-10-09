import BMSConstructibleBridge.ThirdOrderSemantics
import BMSConstructibleBridge.SecondOrderOmegaSyntax

/-!
# 原纯集合语言中的有限闭包规格

有限集合表示为与某个内部自然数序数双射的集合。有限子集闭包是包含原集合
的最小有限子集闭合超集；公式及模式均在原 ℒ 中，不引入新函数符号。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteClosureSyntax

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def subset_m {Γ Δ : SortContext ℒ} (a b : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.imp (member_m (.bvar .here) (a.weakenBound SetTheory.SetSort.set))
    (member_m (.bvar .here) (b.weakenBound SetTheory.SetSort.set)))

def cover_l (f k a : carrier_l ℳ) : Prop :=
  ∀ y, member_l ℳ y a → ∃ x, member_l ℳ x k ∧ value_l f x y

def cover_m {Γ Δ : SortContext ℒ} (f k a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.imp (member_m (.bvar .here) (a.weakenBound SetTheory.SetSort.set))
    (.existsE .set (.conj (member_m (.bvar .here)
      ((k.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set))
      (value_m ((f.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set)
        (.bvar .here) (.bvar (.there .here))))))

def finite_l (ω a : carrier_l ℳ) : Prop :=
  ∃ k, member_l ℳ k ω ∧ ∃ f, map_l f k a ∧ cover_l f k a ∧ injective_l f

def finite_m {Γ Δ : SortContext ℒ} (ω a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set (.conj (member_m (.bvar .here) (ω.weakenBound SetTheory.SetSort.set))
    (.existsE .set (.conj (map_m (.bvar .here) (.bvar (.there .here))
      ((a.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set))
      (.conj (cover_m (.bvar .here) (.bvar (.there .here))
        ((a.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set))
        (injective_m (.bvar .here))))))

def closed_l (ω b : carrier_l ℳ) : Prop :=
  ∀ a, finite_l ω a → subset_l a b → member_l ℳ a b

def closed_m {Γ Δ : SortContext ℒ} (ω b : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.imp
    (.conj (finite_m (ω.weakenBound SetTheory.SetSort.set) (.bvar .here))
      (subset_m (.bvar .here) (b.weakenBound SetTheory.SetSort.set)))
    (member_m (.bvar .here) (b.weakenBound SetTheory.SetSort.set)))

def closure_l (ω x c : carrier_l ℳ) : Prop :=
  subset_l x c ∧ closed_l ω c ∧ ∀ b, subset_l x b → closed_l ω b → subset_l c b

def closure_m {Γ Δ : SortContext ℒ} (ω x c : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (subset_m x c) (.conj (closed_m ω c)
    (.forallE .set (.imp
      (.conj (subset_m (x.weakenBound SetTheory.SetSort.set) (.bvar .here))
        (closed_m (ω.weakenBound SetTheory.SetSort.set) (.bvar .here)))
      (subset_m (c.weakenBound SetTheory.SetSort.set) (.bvar .here)))))

theorem subset_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (a b : Term ℒ Γ Δ .set) :
    (subset_m a b).satisfies η ↔ subset_l (a.eval η) (b.eval η) := by
  simp only [subset_m, Formula.satisfies, member_m, Arguments.eval, Term.eval,
    Term.eval_weakenBound]
  rfl

theorem cover_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (f k a : Term ℒ Γ Δ .set) :
    (cover_m f k a).satisfies η ↔ cover_l (f.eval η) (k.eval η) (a.eval η) := by
  simp only [cover_m, Formula.satisfies, member_m, Arguments.eval, Term.eval,
    Term.eval_weakenBound, value_formula_l]
  rfl

theorem finite_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω a : Term ℒ Γ Δ .set) :
    (finite_m ω a).satisfies η ↔ finite_l (ω.eval η) (a.eval η) := by
  simp only [finite_m, Formula.satisfies, member_m, Arguments.eval, Term.eval,
    Term.eval_weakenBound, map_formula_l, cover_formula_l, injective_formula_l]
  rfl

theorem closed_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω b : Term ℒ Γ Δ .set) :
    (closed_m ω b).satisfies η ↔ closed_l (ω.eval η) (b.eval η) := by
  simp only [closed_m, Formula.satisfies, finite_formula_l, subset_formula_l,
    member_m, Arguments.eval, Term.eval, Term.eval_weakenBound, and_imp]
  rfl

theorem closure_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω x c : Term ℒ Γ Δ .set) :
    (closure_m ω x c).satisfies η ↔ closure_l (ω.eval η) (x.eval η) (c.eval η) := by
  simp only [closure_m, Formula.satisfies, subset_formula_l, closed_formula_l,
    Term.eval, Term.eval_weakenBound, and_imp]
  rfl

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteClosureSyntax
