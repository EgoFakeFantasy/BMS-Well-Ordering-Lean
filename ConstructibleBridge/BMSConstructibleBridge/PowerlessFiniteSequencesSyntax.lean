import BMSConstructibleBridge.PowerlessFiniteClosureSyntax

/-! # 任意母集上的内部有限序列集合规格

序列是定义域为某个内部自然数序数的实际集合函数；长度不要求外部标准。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteSequencesSyntax

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def sequence_l (ω x f : carrier_l ℳ) : Prop :=
  ∃ k, member_l ℳ k ω ∧ map_l f k x

def sequence_m {Γ Δ : SortContext ℒ} (ω x f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set (.conj (member_m (.bvar .here) (ω.weakenBound SetTheory.SetSort.set))
    (map_m (f.weakenBound SetTheory.SetSort.set) (.bvar .here) (x.weakenBound SetTheory.SetSort.set)))

def spec_l (ω x s : carrier_l ℳ) : Prop :=
  ∀ f, member_l ℳ f s ↔ sequence_l ω x f

def spec_m {Γ Δ : SortContext ℒ} (ω x s : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.iff (member_m (.bvar .here) (s.weakenBound SetTheory.SetSort.set))
    (sequence_m (ω.weakenBound SetTheory.SetSort.set) (x.weakenBound SetTheory.SetSort.set) (.bvar .here)))

theorem sequence_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ)
    (ω x f : Term ℒ Γ Δ .set) : (sequence_m ω x f).satisfies η ↔
      sequence_l (ω.eval η) (x.eval η) (f.eval η) := by
  simp only [sequence_m, Formula.satisfies, member_m, map_formula_l,
    Arguments.eval, Term.eval, Term.eval_weakenBound]
  rfl

theorem spec_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ)
    (ω x s : Term ℒ Γ Δ .set) : (spec_m ω x s).satisfies η ↔
      spec_l (ω.eval η) (x.eval η) (s.eval η) := by
  simp only [spec_m, Formula.satisfies, member_m, sequence_formula_l,
    Arguments.eval, Term.eval, Term.eval_weakenBound]
  rfl

def sentence_m : Sentence ℒ :=
  .forallE .set (.imp (SecondOrderOmegaSyntax.omega_m (.bvar .here))
    (.forallE .set (.existsE .set (spec_m (.bvar (.there (.there .here)))
      (.bvar (.there .here)) (.bvar .here)))))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteSequencesSyntax
