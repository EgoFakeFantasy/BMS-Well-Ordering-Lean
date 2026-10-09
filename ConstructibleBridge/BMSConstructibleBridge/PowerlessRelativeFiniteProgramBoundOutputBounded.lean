import BMSConstructibleBridge.PowerlessRelativeFiniteProgramOutputBounded
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramBoundOutput

/-! # 量化程序参数的纯有界求值桥

开放绑定词、长度与坐标时，只在算子原参数尾加入槽，输入／输出首两槽不变。
有界真实 run 和含缺省分支的总输出均回到原 BoundOutput 语义。
本模块是整体求值矩阵的绑定辅助层；其语义桥不能代替最终对象推导。
Δ₀ 分类只要求原算子为 Δ₀，不把任意规范选择关系直接视为 Δ₀。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramBoundOutputBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_l parameters_empty_l)
open PowerlessRelativeFiniteProgramBoundOutput (prefix_m prefix_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private theorem lift_delta_l {Δ : SortContext ℒ}
    {φ : Formula ℒ [] (.set :: .set :: Δ)} (hφ : Formula.IsDelta0 membershipLevyBound φ) :
    Formula.IsDelta0 membershipLevyBound (PowerlessDefinableFiniteTrace.lift_m φ) := by
  unfold PowerlessDefinableFiniteTrace.lift_m
  exact Formula.IsDelta0.substituteMapped
    (boundSubstitution := fun {s} (v : Variable ([] : SortContext ℒ) s) => nomatch v)
    (freeSubstitution := _) hφ

theorem prefix_delta_l {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) (n : Nat) :
    Formula.IsDelta0 membershipLevyBound (prefix_m n φ) := by
  induction n with
  | zero => exact hφ
  | succ n ih => exact lift_delta_l ih

private theorem rebind_delta_l {Γ Δ : SortContext ℒ}
    {φ : Formula ℒ [] (List.replicate Γ.length .set ++ Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) :
    Formula.IsDelta0 membershipLevyBound (PowerlessSourceRebinding.formula_m φ) := by
  unfold PowerlessSourceRebinding.formula_m PowerlessSourceRebinding.binding_m
  exact Formula.IsDelta0.substituteMapped
    (boundSubstitution := fun {s} (v : Variable ([] : SortContext ℒ) s) => nomatch v)
    (freeSubstitution := _) hφ

def run_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C W ω w e t₀ t₁ t₂ a n k y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let t := @PowerlessSourceRebinding.term_m Γ Δ
  PowerlessSourceRebinding.formula_m <|
    PowerlessRelativeFiniteProgramRunBounded.run_m (prefix_m Γ.length φ)
      (t B) (t C) (t W) (t ω) (t w) (t e) (t t₀) (t t₁) (t t₂)
        (t a) (t n) (t k) (t y)

def output_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C W ω w e t₀ t₁ t₂ a n k y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let t := @PowerlessSourceRebinding.term_m Γ Δ
  PowerlessSourceRebinding.formula_m <|
    PowerlessRelativeFiniteProgramOutputBounded.output_m (prefix_m Γ.length φ)
      (t B) (t C) (t W) (t ω) (t w) (t e) (t t₀) (t t₁) (t t₂)
        (t a) (t n) (t k) (t y)

theorem run_delta_l {Γ Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (B C W ω w e t₀ t₁ t₂ a n k y : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (run_m φ B C W ω w e t₀ t₁ t₂ a n k y) := by
  unfold run_m
  exact rebind_delta_l <| PowerlessRelativeFiniteProgramRunBounded.run_delta_l
    (prefix_delta_l hφ Γ.length) _ _ _ _ _ _ _ _ _ _ _ _ _

theorem output_delta_l {Γ Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (B C W ω w e t₀ t₁ t₂ a n k y : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (output_m φ B C W ω w e t₀ t₁ t₂ a n k y) := by
  unfold output_m
  exact rebind_delta_l <| PowerlessRelativeFiniteProgramOutputBounded.output_delta_l
    (prefix_delta_l hφ Γ.length) _ _ _ _ _ _ _ _ _ _ _ _ _

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem output_member_l {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B C W ω w e t₀ t₁ t₂ a n k y : Term ℒ Γ Δ .set)
    (h : (output_m φ B C W ω w e t₀ t₁ t₂ a n k y).satisfies η) :
    mem_l hℳ (y.eval η) (W.eval η) := by
  rw [output_m, PowerlessSourceRebinding.formula_l] at h
  have h₀ := PowerlessRelativeFiniteProgramOutputBounded.output_member_l
    (prefix_m Γ.length φ) (PowerlessSourceOpening.env_l η)
      (PowerlessSourceRebinding.term_m B) (PowerlessSourceRebinding.term_m C)
      (PowerlessSourceRebinding.term_m W) (PowerlessSourceRebinding.term_m ω)
      (PowerlessSourceRebinding.term_m w) (PowerlessSourceRebinding.term_m e)
      (PowerlessSourceRebinding.term_m t₀) (PowerlessSourceRebinding.term_m t₁)
      (PowerlessSourceRebinding.term_m t₂) (PowerlessSourceRebinding.term_m a)
      (PowerlessSourceRebinding.term_m n) (PowerlessSourceRebinding.term_m k)
      (PowerlessSourceRebinding.term_m y) h
  simpa only [parameters_empty_l, PowerlessSourceRebinding.term_l] using h₀

private theorem guard_open_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 Γ Δ) (B β C W ω w N Q e t₀ t₁ t₂ a n : Term ℒ Γ Δ .set)
    (h : PowerlessRelativeFiniteProgramOutputBounded.guard_l φ (parameters_l η)
      (B.eval η) (β.eval η) (C.eval η) (W.eval η) (ω.eval η) (w.eval η)
      (N.eval η) (Q.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (n.eval η)) :
    let t := @PowerlessSourceRebinding.term_m Γ Δ
    let ξ := PowerlessSourceOpening.env_l η
    PowerlessRelativeFiniteProgramOutputBounded.guard_l (prefix_m Γ.length φ) ξ
      ((t B).eval ξ) ((t β).eval ξ) ((t C).eval ξ) ((t W).eval ξ) ((t ω).eval ξ)
      ((t w).eval ξ) ((t N).eval ξ) ((t Q).eval ξ) ((t e).eval ξ) ((t t₀).eval ξ)
      ((t t₁).eval ξ) ((t t₂).eval ξ) ((t a).eval ξ) ((t n).eval ξ) := by
  simpa only [PowerlessRelativeFiniteProgramOutputBounded.guard_l,
    PowerlessSourceRebinding.term_l, PowerlessRelativeFiniteProgramInstruction.functional_l,
    PowerlessRelativeFiniteProgramLimitStep.closed_l, prefix_formula_l] using h

theorem run_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B β C W ω w N Q e t₀ t₁ t₂ a n k y : Term ℒ Γ Δ .set)
    (h : PowerlessRelativeFiniteProgramOutputBounded.guard_l φ (parameters_l η)
      (B.eval η) (β.eval η) (C.eval η) (W.eval η) (ω.eval η) (w.eval η)
      (N.eval η) (Q.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (n.eval η)) :
    (run_m φ B C W ω w e t₀ t₁ t₂ a n k y).satisfies η ↔
      PowerlessRelativeFiniteProgramBoundOutput.run_l φ (parameters_l η)
        (B.eval η) (C.eval η) (ω.eval η) (w.eval η) (e.eval η) (t₀.eval η)
          (t₁.eval η) (t₂.eval η) (a.eval η) (n.eval η) (k.eval η) (y.eval η) := by
  rw [run_m, PowerlessSourceRebinding.formula_l]
  let t := @PowerlessSourceRebinding.term_m Γ Δ
  have h' := guard_open_l φ η B β C W ω w N Q e t₀ t₁ t₂ a n h
  have h₀ := PowerlessRelativeFiniteProgramOutputBounded.run_formula_l K
    (prefix_m Γ.length φ) (PowerlessSourceOpening.env_l η)
      (t B) (t β) (t C) (t W) (t ω) (t w) (t N) (t Q) (t e)
        (t t₀) (t t₁) (t t₂) (t a) (t n) (t k) (t y)
          (by simpa only [parameters_empty_l] using h')
  simp only [t, parameters_empty_l, PowerlessSourceRebinding.term_l] at h₀
  exact h₀.trans (PowerlessRelativeFiniteProgramBoundOutput.run_open_l K
    φ η B C ω w e t₀ t₁ t₂ a n k (y.eval η))

theorem output_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B β C W ω w N Q e t₀ t₁ t₂ a n k y : Term ℒ Γ Δ .set)
    (h : PowerlessRelativeFiniteProgramOutputBounded.guard_l φ (parameters_l η)
      (B.eval η) (β.eval η) (C.eval η) (W.eval η) (ω.eval η) (w.eval η)
      (N.eval η) (Q.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (n.eval η)) :
    (output_m φ B C W ω w e t₀ t₁ t₂ a n k y).satisfies η ↔
      PowerlessRelativeFiniteProgramBoundOutput.output_l φ (parameters_l η)
        (B.eval η) (C.eval η) (ω.eval η) (w.eval η) (e.eval η) (t₀.eval η)
          (t₁.eval η) (t₂.eval η) (a.eval η) (n.eval η) (k.eval η) (y.eval η) := by
  rw [output_m, PowerlessSourceRebinding.formula_l]
  let t := @PowerlessSourceRebinding.term_m Γ Δ
  have h' := guard_open_l φ η B β C W ω w N Q e t₀ t₁ t₂ a n h
  have h₀ := PowerlessRelativeFiniteProgramOutputBounded.output_formula_l K
    (prefix_m Γ.length φ) (PowerlessSourceOpening.env_l η)
      (t B) (t β) (t C) (t W) (t ω) (t w) (t N) (t Q) (t e)
        (t t₀) (t t₁) (t t₂) (t a) (t n) (t k) (t y)
          (by simpa only [parameters_empty_l] using h')
  simp only [t, parameters_empty_l, PowerlessSourceRebinding.term_l] at h₀
  have hRun (z : type_l hℳ) := PowerlessRelativeFiniteProgramBoundOutput.run_open_l K
    φ η B C ω w e t₀ t₁ t₂ a n k z
  have hOut : PowerlessRelativeFiniteProgramOutput.output_l
      (PowerlessRelativeFiniteProgramBoundOutput.step_m φ B C ω w e t₀ t₁ t₂)
      (PowerlessSourceOpening.env_l η) (B.eval η) (ω.eval η) (e.eval η)
        (a.eval η) (n.eval η) (k.eval η) (y.eval η) ↔
      PowerlessRelativeFiniteProgramBoundOutput.output_l φ (parameters_l η)
        (B.eval η) (C.eval η) (ω.eval η) (w.eval η) (e.eval η) (t₀.eval η)
          (t₁.eval η) (t₂.eval η) (a.eval η) (n.eval η) (k.eval η) (y.eval η) := by
    simp only [PowerlessRelativeFiniteProgramOutput.output_l,
      PowerlessRelativeFiniteProgramBoundOutput.output_l, hRun]
  exact h₀.trans hOut

#print axioms prefix_delta_l
#print axioms run_delta_l
#print axioms output_delta_l
#print axioms output_member_l
#print axioms run_formula_l
#print axioms output_formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramBoundOutputBounded
