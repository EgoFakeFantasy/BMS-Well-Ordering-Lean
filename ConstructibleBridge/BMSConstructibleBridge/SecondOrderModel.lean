import BMSConstructibleBridge.SecondOrderSubstitution

/-!
# 任意二阶算术模型中的可定义理解和归纳

数域与集合域均保留为模型载体，不假设数域为标准自然数，也不假设所有外部
子集都在集合域中。理解和归纳只用于有实际纯语言公式及其指定环境的性质。
这给后续图操作的非标准模型验证提供入口，不从内部良基性推出外部 `Acc`。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderModel

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic

set_option autoImplicit false

universe u

abbrev num_l (ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m) := ℳ.Carrier sort_m.num
abbrev set_l (ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m) := ℳ.Carrier sort_m.set

def zero_l (ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m) : num_l ℳ :=
  ℳ.funcInterp .zero .nil

def succ_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m} (n : num_l ℳ) : num_l ℳ :=
  ℳ.funcInterp .succ (.cons n .nil)

def add_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m} (m n : num_l ℳ) : num_l ℳ :=
  ℳ.funcInterp .add (.cons m (.cons n .nil))

def mul_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m} (m n : num_l ℳ) : num_l ℳ :=
  ℳ.funcInterp .mul (.cons m (.cons n .nil))

def mem_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m} (n : num_l ℳ) (X : set_l ℳ) : Prop :=
  ℳ.relInterp .mem (.cons n (.cons X .nil))

theorem nonzero_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (n : num_l ℳ) : succ_l n ≠ zero_l ℳ :=
  hℳ _ (axiom_m.base .nonzero) n

theorem injective_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) : Function.Injective (succ_l (ℳ := ℳ)) :=
  hℳ _ (axiom_m.base .injective)

theorem predecessor_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (n : num_l ℳ) : n = zero_l ℳ ∨ ∃ m, n = succ_l m :=
  hℳ _ (axiom_m.base .predecessor) n

theorem add_zero_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (n : num_l ℳ) : add_l n (zero_l ℳ) = n :=
  hℳ _ (axiom_m.base .add_zero) n

theorem add_succ_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (m n : num_l ℳ) : add_l m (succ_l n) = succ_l (add_l m n) :=
  hℳ _ (axiom_m.base .add_succ) m n

theorem mul_zero_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (n : num_l ℳ) : mul_l n (zero_l ℳ) = zero_l ℳ :=
  hℳ _ (axiom_m.base .mul_zero) n

theorem mul_succ_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (m n : num_l ℳ) : mul_l m (succ_l n) = add_l (mul_l m n) m :=
  hℳ _ (axiom_m.base .mul_succ) m n

theorem ext_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (X Y : set_l ℳ) :
    (∀ n, mem_l n X ↔ mem_l n Y) → X = Y :=
  hℳ _ (axiom_m.base .extensionality) X Y

/-- 对象理解推导在任意模型中产生内部集合；不要求该模型为 β 模型。 -/
theorem comprehension_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: Δ)) (hφ : language_m φ = true)
    (η : Env ℳ [] Δ) :
    ∃ X : set_l ℳ, ∀ n : num_l ℳ, mem_l n X ↔ Formula.satisfies (η.pushFree n) φ := by
  have h := (comprehension_derives_m φ hφ).sound hℳ η (by intro ψ h; cases h)
  obtain ⟨X, h⟩ := h
  refine ⟨X, fun n => (h n).trans ?_⟩
  refine (Formula.satisfies_substitute _ _ φ).trans ?_
  apply Iff.of_eq
  apply congrArg (fun η => Formula.satisfies η φ)
  apply Env.ext
  · intro s v
    nomatch v
  · intro s v
    cases v <;> rfl

/-- 仅对实际纯公式的性质归纳；所有对象数（包括非标准数）均在结论范围内。 -/
theorem induction_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: Δ)) (hφ : language_m φ = true)
    (η : Env ℳ [] Δ)
    (h₀ : Formula.satisfies (η.pushFree (zero_l ℳ)) φ)
    (h₁ : ∀ n, Formula.satisfies (η.pushFree n) φ → Formula.satisfies (η.pushFree (succ_l n)) φ) :
    ∀ n : num_l ℳ, Formula.satisfies (η.pushFree n) φ := by
  obtain ⟨X, hX⟩ := comprehension_l hℳ φ hφ η
  have h : (mem_l (zero_l ℳ) X ∧ ∀ n, mem_l n X → mem_l (succ_l n) X) →
      ∀ n, mem_l n X := hℳ _ (axiom_m.base .induction) X
  have h₂ := h ⟨(hX _).mpr h₀, fun n h => (hX _).mpr (h₁ n ((hX n).mp h))⟩
  exact fun n => (hX n).mp (h₂ n)

/-- 语义形式的可定义归纳；调用者必须给出同一个实际公式的逐数真值对应。 -/
theorem induct_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: Δ)) (hφ : language_m φ = true)
    (η : Env ℳ [] Δ) (P : num_l ℳ → Prop)
    (hP : ∀ n, Formula.satisfies (η.pushFree n) φ ↔ P n)
    (h₀ : P (zero_l ℳ)) (h₁ : ∀ n, P n → P (succ_l n)) : ∀ n, P n := by
  have h := induction_l hℳ φ hφ η ((hP _).mpr h₀)
    (fun n h => (hP _).mpr (h₁ n ((hP n).mp h)))
  exact fun n => (hP n).mp (h n)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderModel
