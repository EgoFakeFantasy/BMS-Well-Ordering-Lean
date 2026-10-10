import BMSConstructibleBridge.ThirdOrderTheory
import YesMetaZFC.Automation.ModelClosure

/-!
# 三阶背景的实际集合、函数和统一实数界

在任意纯集合论模型中核验新公理语义，不要求标准性或外部良基。良序的
极小元条款只量化模型内部子集。所有规模单射统一落到同一个 P(ω)。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderSemantics

open Logic FirstOrder

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

attribute [local implicit_reducible] SetTheory.signature

abbrev carrier_l (ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ) := ℳ.Carrier .set

def member_l (ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ) (a b : carrier_l ℳ) : Prop :=
  ℳ.relInterp .membership (.cons a (.cons b .nil))

def subset_l (a b : carrier_l ℳ) : Prop := ∀ x, member_l ℳ x a → member_l ℳ x b

def power_l (a p : carrier_l ℳ) : Prop := ∀ x, member_l ℳ x p ↔ subset_l x a

def pair_l (a b p : carrier_l ℳ) : Prop := ∀ x, member_l ℳ x p ↔ x = a ∨ x = b

def ordered_l (a b p : carrier_l ℳ) : Prop := ∃ x y, pair_l a a x ∧ pair_l a b y ∧ pair_l x y p

def value_l (f a b : carrier_l ℳ) : Prop := ∃ p, member_l ℳ p f ∧ ordered_l a b p

def map_l (f a b : carrier_l ℳ) : Prop :=
  (∀ p, member_l ℳ p f → ∃ x y, member_l ℳ x a ∧ member_l ℳ y b ∧ ordered_l x y p) ∧
  ∀ x, member_l ℳ x a → ∃! y, member_l ℳ y b ∧ value_l f x y

def injective_l (f : carrier_l ℳ) : Prop :=
  ∀ x z y, value_l f x y → value_l f z y → x = z

def inductive_l (a : carrier_l ℳ) : Prop :=
  Formula.satisfies ((Env.empty (M := ℳ)).pushFree a) SecondOrderOmegaSyntax.inductive_template_m

def omega_l (a : carrier_l ℳ) : Prop := inductive_l a ∧ ∀ b, inductive_l b → subset_l a b

def wellOrder_l (a r : carrier_l ℳ) : Prop :=
  (∀ x, member_l ℳ x a → ¬value_l r x x) ∧
  (∀ x y z, member_l ℳ x a ∧ member_l ℳ y a ∧ member_l ℳ z a →
    value_l r x y → value_l r y z → value_l r x z) ∧
  (∀ x y, member_l ℳ x a ∧ member_l ℳ y a → value_l r x y ∨ x = y ∨ value_l r y x) ∧
  ∀ b, subset_l b a ∧ (∃ x, member_l ℳ x b) →
    ∃ x, member_l ℳ x b ∧ ∀ y, member_l ℳ y b → ¬value_l r y x

theorem subset_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (a b : Term ℒ Γ Δ .set) :
    Formula.satisfies η (ThirdOrderTheory.subset_m a b) ↔ subset_l (a.eval η) (b.eval η) := by
  simp only [ThirdOrderTheory.subset_m, SecondOrderObjectSyntax.member_m, Formula.satisfies,
    Arguments.eval, Term.eval_weakenBound]
  rfl

theorem power_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (a p : Term ℒ Γ Δ .set) :
    Formula.satisfies η (ThirdOrderTheory.power_m a p) ↔ power_l (a.eval η) (p.eval η) := by
  simp only [ThirdOrderTheory.power_m, SecondOrderObjectSyntax.member_m, Formula.satisfies,
    Arguments.eval, subset_formula_l, Term.eval_weakenBound]
  rfl

theorem pair_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (a b p : Term ℒ Γ Δ .set) :
    Formula.satisfies η (SecondOrderObjectSyntax.pair_m a b p) ↔ pair_l (a.eval η) (b.eval η) (p.eval η) := by
  rw [SecondOrderObjectSyntax.pair_m, Formula.satisfies_substitute]
  rfl

theorem ordered_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (a b p : Term ℒ Γ Δ .set) :
    Formula.satisfies η (SecondOrderObjectSyntax.ordered_m a b p) ↔
      ordered_l (a.eval η) (b.eval η) (p.eval η) := by
  simp only [SecondOrderObjectSyntax.ordered_m, Formula.satisfies_substitute,
    SecondOrderObjectSyntax.ordered_template_m, Formula.satisfies, pair_formula_l]
  rfl

theorem value_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (f a b : Term ℒ Γ Δ .set) :
    Formula.satisfies η (SecondOrderObjectSyntax.value_m f a b) ↔
      value_l (f.eval η) (a.eval η) (b.eval η) := by
  simp only [SecondOrderObjectSyntax.value_m, Formula.satisfies_substitute,
    SecondOrderObjectSyntax.value_template_m, Formula.satisfies, ordered_formula_l]
  rfl

theorem map_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (f a b : Term ℒ Γ Δ .set) :
    Formula.satisfies η (SecondOrderObjectSyntax.map_m f a b) ↔ map_l (f.eval η) (a.eval η) (b.eval η) := by
  simp only [SecondOrderObjectSyntax.map_m, Formula.satisfies_substitute,
    SecondOrderObjectSyntax.map_template_m, Formula.satisfies, ordered_formula_l, value_formula_l]
  rfl

theorem injective_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (f : Term ℒ Γ Δ .set) :
    Formula.satisfies η (SecondOrderObjectSyntax.injective_m f) ↔ injective_l (f.eval η) := by
  simp only [SecondOrderObjectSyntax.injective_m, Formula.satisfies_substitute,
    SecondOrderObjectSyntax.injective_template_m, Formula.satisfies, value_formula_l]
  rfl

theorem inductive_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (a : Term ℒ Γ Δ .set) :
    Formula.satisfies η (SecondOrderOmegaSyntax.inductive_m a) ↔ inductive_l (a.eval η) := by
  rw [SecondOrderOmegaSyntax.inductive_m, Formula.satisfies_substitute]
  apply Iff.of_eq
  apply congrArg (fun η => Formula.satisfies η SecondOrderOmegaSyntax.inductive_template_m)
  apply Env.ext (bound := []) (fun {_} v => nomatch v)
  · intro s v
    match v with
    | .here => rfl

theorem omega_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (a : Term ℒ Γ Δ .set) :
    Formula.satisfies η (SecondOrderOmegaSyntax.omega_m a) ↔ omega_l (a.eval η) := by
  simp only [SecondOrderOmegaSyntax.omega_m, Formula.satisfies_substitute,
    SecondOrderOmegaSyntax.omega_template_m, Formula.satisfies, inductive_formula_l]
  rfl

theorem wellOrder_formula_l (η : Env ℳ [] [.set, .set]) :
    Formula.satisfies η ThirdOrderTheory.wellOrder_template_m ↔
      wellOrder_l (η.freeVal .here) (η.freeVal (.there .here)) := by
  simp only [ThirdOrderTheory.wellOrder_template_m, Formula.satisfies, value_formula_l, subset_formula_l]
  rfl

theorem omega_unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {a b : carrier_l ℳ} (ha : omega_l a) (hb : omega_l b) : a = b := by
  apply (PowerlessTheory.ext_l hℳ).eq_of_same_members
  intro x
  exact ⟨ha.2 b hb.1 x, hb.2 a ha.1 x⟩

theorem power_unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {a p q : carrier_l ℳ} (hp : power_l a p) (hq : power_l a q) : p = q := by
  apply (PowerlessTheory.ext_l hℳ).eq_of_same_members
  intro x
  exact (hp x).trans (hq x).symm

/-- 实数集合存在闭句的准确语义；此处不消费全集规模界或选择。 -/
theorem reals_formula_l : ThirdOrderTheory.reals_m.TrueIn ℳ ↔
    ∃ w p : carrier_l ℳ, omega_l w ∧ power_l w p := by
  simp only [ThirdOrderTheory.reals_m, Formula.TrueIn, Formula.satisfies,
    omega_formula_l, power_formula_l]
  rfl

/-- 同一个实数对象作为所有模型集合的大小上界，不按集合另选不相关的界。 -/
theorem bounds_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m) :
    ∃ w p : carrier_l ℳ, omega_l w ∧ power_l w p ∧ ∀ a, ∃ f, map_l f a p ∧ injective_l f := by
  obtain ⟨w, p, hw, hp⟩ := reals_formula_l.mp (ThirdOrderTheory.reals_l hℳ)
  refine ⟨w, p, hw, hp, ?_⟩
  have h₁ := ThirdOrderTheory.bound_l hℳ
  simp only [ThirdOrderTheory.bound_m, Formula.TrueIn, Formula.satisfies,
    omega_formula_l, power_formula_l, map_formula_l, injective_formula_l] at h₁
  intro a
  obtain ⟨w', p', f, hw', hp', hf⟩ := h₁ a
  have h₂ := omega_unique_l (ThirdOrderTheory.core_l hℳ) hw' hw
  change w' = w at h₂
  subst w'
  have h₃ := power_unique_l (ThirdOrderTheory.core_l hℳ) hp' hp
  change p' = p at h₃
  subst p'
  exact ⟨f, hf⟩

theorem choice_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m) (a : carrier_l ℳ) :
    ∃ r, wellOrder_l a r := by
  have h := hℳ _ ThirdOrderTheory.axiom_m.choice
  rw [ThirdOrderTheory.choice_m, Formula.TrueIn,
    _root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff] at h
  have h₀ := h ((Env.empty (M := ℳ)).pushFree a)
  simp only [Formula.satisfies, Formula.satisfies_substitute, wellOrder_formula_l] at h₀
  exact h₀

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderSemantics
