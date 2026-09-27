import BMSConstructibleBridge.PowerlessArithmetic
import YesMetaZFC.Automation.RelationalEnvironment

/-!
# 内部算术项的纯集合图

保留原双排序项与实际运算，不另建算术语法。子项的共同值列由原绑定块工具处理，
每个项图精确给出显式算术结构中的值；ω、零和全部原参数一直保持同一解释。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessArithmeticTerms

open Logic FirstOrder ThirdOrderSemantics
open Automation.RelationalTranslation (weakenTerm witnesses existsBlock pushBlock
  weakenTerm_eval witnesses_eval existsBlock_satisfies)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessArithmetic.structure_l

universe u

abbrev context_m (Γ : SortContext SecondOrderSyntax.signature_m) : SortContext ℒ :=
  Γ.map (fun _ => SetTheory.SetSort.set)

abbrev assignment_m (Γ : SortContext SecondOrderSyntax.signature_m) (Δ Θ : SortContext ℒ) :=
  {s : SecondOrderSyntax.sort_m} → Variable Γ s → Term ℒ Δ Θ .set

def weaken_m {Γ : SortContext SecondOrderSyntax.signature_m} {Δ Θ : SortContext ℒ}
    (Λ : SortContext ℒ) (ρ : assignment_m Γ Δ Θ) : assignment_m Γ (Λ ++ Δ) Θ :=
  fun v => weakenTerm Λ (ρ v)

/-- 只在已经给定的参数值上读取原函数图；附加配对槽与所选算术结构的缺省值一致。 -/
def function_m {Γ Δ : SortContext ℒ} (ω e z : Term ℒ Γ Δ .set) :
    (f : SecondOrderSyntax.func_m) →
      Arguments ℒ Γ Δ (context_m (SecondOrderSyntax.signature_m.funcDomain f)) → Formula ℒ Γ Δ
  | .zero, .nil => .equal z e
  | .succ, .cons x .nil => PowerlessNaturalStep.successor_m x z
  | .add, .cons x (.cons y .nil) => PowerlessAdditionSyntax.addition_m ω e x y z
  | .mul, .cons x (.cons y .nil) => PowerlessMultiplication.multiplication_m ω e x y z
  | .pair, .cons _ (.cons _ .nil) => .equal z e

mutual
def term_m {Γ Δ : SortContext SecondOrderSyntax.signature_m} {Θ Λ : SortContext ℒ}
    (ω e : Term ℒ Θ Λ .set) (ρ : assignment_m Γ Θ Λ) (τ : assignment_m Δ Θ Λ)
    {s : SecondOrderSyntax.sort_m} : Term SecondOrderSyntax.signature_m Γ Δ s →
      Term ℒ Θ Λ .set → Formula ℒ Θ Λ
  | .bvar v, z => .equal z (ρ v)
  | .fvar v, z => .equal z (τ v)
  | .app f a, z =>
      let Ξ := context_m (SecondOrderSyntax.signature_m.funcDomain f)
      existsBlock Ξ (.conj
        (arguments_m (weakenTerm Ξ ω) (weakenTerm Ξ e) (weaken_m Ξ ρ) (weaken_m Ξ τ) a (witnesses Ξ))
        (function_m (weakenTerm Ξ ω) (weakenTerm Ξ e) (weakenTerm Ξ z) f (witnesses Ξ)))

def arguments_m {Γ Δ : SortContext SecondOrderSyntax.signature_m} {Θ Λ : SortContext ℒ}
    (ω e : Term ℒ Θ Λ .set) (ρ : assignment_m Γ Θ Λ) (τ : assignment_m Δ Θ Λ)
    {Ξ : SortContext SecondOrderSyntax.signature_m} : Arguments SecondOrderSyntax.signature_m Γ Δ Ξ →
      Arguments ℒ Θ Λ (context_m Ξ) → Formula ℒ Θ Λ
  | .nil, .nil => .truth
  | .cons a b, .cons x y => .conj (term_m ω e ρ τ a x) (arguments_m ω e ρ τ b y)
end

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

abbrev sort_l (ω : carrier_l ℳ) : SecondOrderSyntax.sort_m → Type u
  | .num => PowerlessArithmetic.num_l ω
  | .set => PowerlessArithmetic.set_l ω

def val_l {ω : carrier_l ℳ} : {s : SecondOrderSyntax.sort_m} → sort_l ω s → carrier_l ℳ
  | .num, a => a.val
  | .set, A => A.val

theorem val_injective_l {ω : carrier_l ℳ} {s : SecondOrderSyntax.sort_m} :
    Function.Injective (val_l (ℳ := ℳ) (ω := ω) (s := s)) := by
  cases s <;> exact Subtype.val_injective

def values_l {ω : carrier_l ℳ} : {Γ : SortContext SecondOrderSyntax.signature_m} →
    Values (sort_l ω) Γ → Values ℳ.Carrier (context_m Γ)
  | _, .nil => .nil
  | _, .cons a b => .cons (val_l a) (values_l b)

def agrees_l {ω : carrier_l ℳ} {Γ : SortContext SecondOrderSyntax.signature_m} {Δ Θ : SortContext ℒ}
    (η : Env ℳ Δ Θ) (ρ : assignment_m Γ Δ Θ)
    (ξ : {s : SecondOrderSyntax.sort_m} → Variable Γ s → sort_l ω s) : Prop :=
  ∀ {s} (v : Variable Γ s), (ρ v).eval η = val_l (ξ v)

theorem weaken_l {ω : carrier_l ℳ} {Γ : SortContext SecondOrderSyntax.signature_m} {Δ Θ Λ : SortContext ℒ}
    {η : Env ℳ Δ Θ} {ρ : assignment_m Γ Δ Θ}
    {ξ : {s : SecondOrderSyntax.sort_m} → Variable Γ s → sort_l ω s}
    (h : agrees_l η ρ ξ) (a : Values ℳ.Carrier Λ) : agrees_l (pushBlock η a) (weaken_m Λ ρ) ξ :=
  fun v => (weakenTerm_eval η a (ρ v)).trans (h v)

variable (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
  {h₀ : member_l ℳ e ω} (F : PowerlessArithmetic.operations_l ω e)

local notation "𝒩" => PowerlessArithmetic.structure_l he h₀ F

include hℳ hω

theorem function_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ)
    (w z y : Term ℒ Γ Δ .set) (hw : w.eval η = ω) (hz : z.eval η = e)
    (f : SecondOrderSyntax.func_m)
    (a : Arguments ℒ Γ Δ (context_m (SecondOrderSyntax.signature_m.funcDomain f)))
    (b : Values (sort_l ω) (SecondOrderSyntax.signature_m.funcDomain f))
    (ha : a.eval η = values_l b) :
    (function_m w z y f a).satisfies η ↔
      y.eval η = val_l (ω := ω) (s := SecondOrderSyntax.signature_m.funcCodomain f) ((𝒩).funcInterp f b) := by
  match f, a, b with
  | .zero, .nil, .nil => exact Iff.of_eq (congrArg (fun e => y.eval η = e) hz)
  | .pair, .cons _ (.cons _ .nil), .cons _ (.cons _ .nil) =>
    exact Iff.of_eq (congrArg (fun e => y.eval η = e) hz)
  | .succ, .cons x .nil, .cons b .nil =>
    have hx := (Values.cons.inj ha).1
    simp only [function_m, PowerlessNaturalStep.successor_formula_l, hx]
    change PowerlessNatural.successor_l b.val (y.eval η) ↔ y.eval η = (F.succ_l b).val
    exact ⟨fun h => PowerlessNatural.successor_unique_l hℳ h (F.succ_graph_l b),
      fun h => h.symm ▸ F.succ_graph_l b⟩
  | .add, .cons x (.cons t .nil), .cons b (.cons c .nil) =>
    obtain ⟨hx, ht⟩ := Values.cons.inj ha
    have ht := (Values.cons.inj ht).1
    simp only [function_m, PowerlessAdditionSyntax.addition_formula_l, hw, hz, hx, ht]
    change PowerlessAddition.addition_l ω e b.val c.val (y.eval η) ↔ y.eval η = (F.add_l b c).val
    exact ⟨fun h => PowerlessAddition.unique_l hℳ hω he h (F.add_graph_l b c),
      fun h => h.symm ▸ F.add_graph_l b c⟩
  | .mul, .cons x (.cons t .nil), .cons b (.cons c .nil) =>
    obtain ⟨hx, ht⟩ := Values.cons.inj ha
    have ht := (Values.cons.inj ht).1
    simp only [function_m, PowerlessMultiplication.multiplication_formula_l, hw, hz, hx, ht]
    change PowerlessMultiplication.multiplication_l ω e b.val c.val (y.eval η) ↔ y.eval η = (F.mul_l b c).val
    exact ⟨fun h => PowerlessMultiplication.unique_l hℳ hω he h (F.mul_graph_l b c),
      fun h => h.symm ▸ F.mul_graph_l b c⟩

omit hℳ hω

mutual
/-- 对全部原项成立，参数见证不改变源项的实际求值。 -/
theorem term_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    (he : PowerlessNatural.zero_l e) (F : PowerlessArithmetic.operations_l ω e)
    {Γ Δ : SortContext SecondOrderSyntax.signature_m} {Θ Λ : SortContext ℒ}
    (ξ : Env (PowerlessArithmetic.structure_l he h₀ F) Γ Δ) (η : Env ℳ Θ Λ) (w z : Term ℒ Θ Λ .set)
    (ρ : assignment_m Γ Θ Λ) (τ : assignment_m Δ Θ Λ)
    (hw : w.eval η = ω) (hz : z.eval η = e)
    (hρ : agrees_l η ρ ξ.boundVal) (hτ : agrees_l η τ ξ.freeVal)
    {s : SecondOrderSyntax.sort_m} (a : Term SecondOrderSyntax.signature_m Γ Δ s)
    (b : Term ℒ Θ Λ .set) : (term_m w z ρ τ a b).satisfies η ↔
      b.eval η = val_l (ω := ω) (s := s) (a.eval ξ) := by
  match a with
  | .bvar v => exact Iff.of_eq (congrArg (fun x => b.eval η = x) (hρ v))
  | .fvar v => exact Iff.of_eq (congrArg (fun x => b.eval η = x) (hτ v))
  | .app f a =>
    rw [term_m, existsBlock_satisfies]
    constructor
    · rintro ⟨c, hc, h⟩
      have h₁ := (arguments_formula_l hℳ hω he F ξ (pushBlock η c) _ _ _ _
        ((weakenTerm_eval η c w).trans hw) ((weakenTerm_eval η c z).trans hz)
        (weaken_l hρ c) (weaken_l hτ c) a _).mp hc
      rw [witnesses_eval] at h₁
      subst c
      have h₂ := (function_formula_l hℳ hω he (h₀ := h₀) F (pushBlock η (values_l (a.eval ξ))) _ _ _
        ((weakenTerm_eval η _ w).trans hw) ((weakenTerm_eval η _ z).trans hz) f _ (a.eval ξ)
        (witnesses_eval η _)).mp h
      simpa only [weakenTerm_eval, Term.eval] using h₂
    · intro h
      refine ⟨values_l (a.eval ξ), ?_, ?_⟩
      · apply (arguments_formula_l hℳ hω he F ξ _ _ _ _ _
          ((weakenTerm_eval η _ w).trans hw) ((weakenTerm_eval η _ z).trans hz)
          (weaken_l hρ _) (weaken_l hτ _) a _).mpr
        exact witnesses_eval η _
      · apply (function_formula_l hℳ hω he (h₀ := h₀) F _ _ _ _
          ((weakenTerm_eval η _ w).trans hw) ((weakenTerm_eval η _ z).trans hz) f _ (a.eval ξ)
          (witnesses_eval η _)).mpr
        simpa only [weakenTerm_eval, Term.eval] using h

theorem arguments_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    (he : PowerlessNatural.zero_l e) (F : PowerlessArithmetic.operations_l ω e)
    {Γ Δ Ξ : SortContext SecondOrderSyntax.signature_m} {Θ Λ : SortContext ℒ}
    (ξ : Env (PowerlessArithmetic.structure_l he h₀ F) Γ Δ) (η : Env ℳ Θ Λ) (w z : Term ℒ Θ Λ .set)
    (ρ : assignment_m Γ Θ Λ) (τ : assignment_m Δ Θ Λ)
    (hw : w.eval η = ω) (hz : z.eval η = e)
    (hρ : agrees_l η ρ ξ.boundVal) (hτ : agrees_l η τ ξ.freeVal)
    (a : Arguments SecondOrderSyntax.signature_m Γ Δ Ξ) (b : Arguments ℒ Θ Λ (context_m Ξ)) :
    (arguments_m w z ρ τ a b).satisfies η ↔ b.eval η = values_l (a.eval ξ) := by
  match a, b with
  | .nil, .nil => exact ⟨fun _ => rfl, fun _ => True.intro⟩
  | .cons a c, .cons b d =>
    simp only [arguments_m, Formula.satisfies, term_formula_l hℳ hω he F ξ η w z ρ τ hw hz hρ hτ,
      arguments_formula_l hℳ hω he F ξ η w z ρ τ hw hz hρ hτ, Arguments.eval, values_l]
    exact ⟨fun ⟨h, h₁⟩ => (by rw [h, h₁]), Values.cons.inj⟩
end

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessArithmeticTerms
