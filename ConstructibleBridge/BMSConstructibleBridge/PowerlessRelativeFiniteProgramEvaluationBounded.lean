import BMSConstructibleBridge.PowerlessRelativeFiniteProgramBoundOutputBounded
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramEvaluation
import BMSConstructibleBridge.PowerlessRelativeLimitFiniteMaps

/-! # 全部内部程序码的纯有界求值矩阵

词限制到 W，长度和输出坐标限制到实际内部 ω。字母表只需包含于 W；
原内部有限图定理回收实际词，不要求 Q∈W，也不假定内部长度外部标准。
真实执行与含缺省值的原总化求值分别精确保持。对象出口证明两矩阵等价，
不预设整个求值像的集合性，不把算子的 Δ₀ 和保层性质当作最终附加公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramEvaluationBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)
open PowerlessBMSQuotientSubsetImageDerives
  (parameters_l parameters_pushBound_l parameters_empty_l)
open PowerlessRelativeFiniteProgramInstruction (functional_l functional_m tags_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)

def body_m {Γ Δ : SortContext ℒ} (actual : Bool) (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C W ω Q e t₀ t₁ t₂ a p y w k n : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessPairBounded.ordered_m w k p) <|
    .conj (PowerlessMapBounded.formula_m w n Q) <|
      if actual then PowerlessRelativeFiniteProgramBoundOutputBounded.run_m
        φ B C W ω w e t₀ t₁ t₂ a n k y
      else PowerlessRelativeFiniteProgramBoundOutputBounded.output_m
        φ B C W ω w e t₀ t₁ t₂ a n k y

def matrix_m {Γ Δ : SortContext ℒ} (actual : Bool) (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C W ω Q e t₀ t₁ t₂ a p y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists W <|
    membershipLevyBound.boundedExists (up ω) <|
      membershipLevyBound.boundedExists (up₂ ω) <|
        body_m actual φ (up₃ B) (up₃ C) (up₃ W) (up₃ ω) (up₃ Q) (up₃ e)
          (up₃ t₀) (up₃ t₁) (up₃ t₂) (up₃ a) (up₃ p) (up₃ y)
          (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)

theorem body_delta_l {Γ Δ : SortContext ℒ} (actual : Bool)
    {φ : Formula ℒ [] (.set :: .set :: Δ)} (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (B C W ω Q e t₀ t₁ t₂ a p y w k n : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (body_m actual φ B C W ω Q e t₀ t₁ t₂ a p y w k n) := by
  cases actual
  · exact .conj (PowerlessPairBounded.ordered_delta_l _ _ _) <|
      .conj (PowerlessMapBounded.delta_l _ _ _) <|
        PowerlessRelativeFiniteProgramBoundOutputBounded.output_delta_l hφ _ _ _ _ _ _ _ _ _ _ _ _ _
  · exact .conj (PowerlessPairBounded.ordered_delta_l _ _ _) <|
      .conj (PowerlessMapBounded.delta_l _ _ _) <|
        PowerlessRelativeFiniteProgramBoundOutputBounded.run_delta_l hφ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem matrix_delta_l {Γ Δ : SortContext ℒ} (actual : Bool)
    {φ : Formula ℒ [] (.set :: .set :: Δ)} (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (B C W ω Q e t₀ t₁ t₂ a p y : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (matrix_m actual φ B C W ω Q e t₀ t₁ t₂ a p y) :=
  .bounded_exists W <| .bounded_exists (up ω) <| .bounded_exists (up₂ ω) <|
    body_delta_l actual hφ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

def guard_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β C W ω Q e t₀ t₁ t₂ a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .conj (PowerlessRelativeHierarchySyntax.limit_m β) <|
      .conj (PowerlessRelativeHierarchySyntax.level_m B β W) <|
        .conj (SecondOrderObjectSyntax.member_m B W) <|
          .conj (PowerlessRelativeHierarchySyntax.class_m B C) <|
            .conj (ThirdOrderTheory.subset_m C W) <|
              .conj (SecondOrderOmegaSyntax.omega_m ω) <|
                .conj (SecondOrderObjectSyntax.member_m ω W) <|
                  .conj (ThirdOrderTheory.subset_m Q W) <|
                    .conj (PowerlessDefinableFiniteTraceDerives.zero_m e) <|
                      .conj (PowerlessRelativeFiniteProgramStep.record_m e e e a) <|
                        .conj (tags_m t₀ t₁ t₂) <| .conj (functional_m φ B)
                          (PowerlessRelativeFiniteProgramLimitStep.closed_m φ B W)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 总化矩阵的任意读数都在 W；非法坐标的缺省值也由输出守卫覆盖。 -/
theorem matrix_member_l {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B C W ω Q e t₀ t₁ t₂ a p y : Term ℒ Γ Δ .set)
    (h : (matrix_m false φ B C W ω Q e t₀ t₁ t₂ a p y).satisfies η) :
    mem_l hℳ (y.eval η) (W.eval η) := by
  simp only [matrix_m, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, Arguments.eval] at h
  obtain ⟨w, _, k, _, n, _, h⟩ := h
  have h₀ := PowerlessRelativeFiniteProgramBoundOutputBounded.output_member_l φ
    (((η.pushBound w).pushBound k).pushBound n)
    (up₃ B) (up₃ C) (up₃ W) (up₃ ω) (.bvar (.there (.there .here)))
    (up₃ e) (up₃ t₀) (up₃ t₁) (up₃ t₂) (up₃ a) (.bvar .here)
    (.bvar (.there .here)) (up₃ y) h.2.2
  simpa only [up₃, up₂, up, Term.eval_weakenBound] using h₀

def guard_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (B β C W ω Q e t₀ t₁ t₂ a : type_l hℳ) : Prop :=
  (∀ x, mem_l hℳ x B → ∀ z, mem_l hℳ z x → mem_l hℳ z B) ∧ limit_l hℳ β ∧
    level_l hℳ B β W ∧ mem_l hℳ B W ∧ PowerlessRelativeClassCorrespondence.member_l hℳ B C ∧
    (∀ x, mem_l hℳ x C → mem_l hℳ x W) ∧ SecondOrderOmega.omega_l hℳ ω ∧
    mem_l hℳ ω W ∧ (∀ q, mem_l hℳ q Q → mem_l hℳ q W) ∧ (∀ x, ¬mem_l hℳ x e) ∧
    PowerlessRelativeFiniteProgramStep.record_l e e e a ∧
    (t₀ ≠ t₁ ∧ t₀ ≠ t₂ ∧ t₁ ≠ t₂) ∧ functional_l φ η B ∧
    PowerlessRelativeFiniteProgramLimitStep.closed_l φ η B W

theorem guard_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B β C W ω Q e t₀ t₁ t₂ a : Term ℒ Γ Δ .set) :
    (guard_m φ B β C W ω Q e t₀ t₁ t₂ a).satisfies η ↔
      guard_l φ (parameters_l η) (B.eval η) (β.eval η) (C.eval η) (W.eval η) (ω.eval η)
        (Q.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) := by
  simp only [guard_m, guard_l, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ,
    PowerlessRelativeHierarchySemantics.limit_formula_l, PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeHierarchySemantics.class_formula_l K, subset_formula_l, SecondOrderOmegaSyntax.omega_l,
    PowerlessDefinableFiniteTraceDerives.zero_formula_l, PowerlessRelativeFiniteProgramStep.record_formula_l,
    tags_m, PowerlessRelativeFiniteProgramInstruction.functional_formula_l K,
    PowerlessRelativeFiniteProgramLimitStep.closed_formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  rfl

theorem matrix_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ} (actual : Bool)
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B β C W ω Q e t₀ t₁ t₂ a p y : Term ℒ Γ Δ .set)
    (h : guard_l φ (parameters_l η) (B.eval η) (β.eval η) (C.eval η) (W.eval η)
      (ω.eval η) (Q.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η)) :
    (matrix_m actual φ B C W ω Q e t₀ t₁ t₂ a p y).satisfies η ↔
      PowerlessRelativeFiniteProgramEvaluation.matrix_l actual φ (parameters_l η)
        (B.eval η) (C.eval η) (ω.eval η) (Q.eval η) (e.eval η) (t₀.eval η)
          (t₁.eval η) (t₂.eval η) (a.eval η) (p.eval η) (y.eval η) := by
  obtain ⟨hB, hβ, hW, hBW, hC, hCW, hω, hωW, hQW, he, ha, ht, hφ, hφW⟩ := h
  have hBody (w k n : type_l hℳ) (hwW : mem_l hℳ w (W.eval η))
      (hn : mem_l hℳ n (ω.eval η)) :
      (body_m actual φ (up₃ B) (up₃ C) (up₃ W) (up₃ ω) (up₃ Q) (up₃ e)
        (up₃ t₀) (up₃ t₁) (up₃ t₂) (up₃ a) (up₃ p) (up₃ y)
        (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)).satisfies
          (((η.pushBound w).pushBound k).pushBound n) ↔
        ordered_l (ℳ := 𝒱) w k (p.eval η) ∧ map_l (ℳ := 𝒱) w n (Q.eval η) ∧
          if actual then PowerlessRelativeFiniteProgramBoundOutput.run_l φ (parameters_l η)
            (B.eval η) (C.eval η) (ω.eval η) w (e.eval η) (t₀.eval η) (t₁.eval η)
              (t₂.eval η) (a.eval η) n k (y.eval η)
          else PowerlessRelativeFiniteProgramBoundOutput.output_l φ (parameters_l η)
            (B.eval η) (C.eval η) (ω.eval η) w (e.eval η) (t₀.eval η) (t₁.eval η)
              (t₂.eval η) (a.eval η) n k (y.eval η) := by
    let ξ : Env 𝒱 (.set :: .set :: .set :: Γ) Δ := ((η.pushBound w).pushBound k).pushBound n
    have hEval (t : Term ℒ Γ Δ .set) : (up₃ t).eval ξ = t.eval η := by
      simp only [ξ, up₃, up₂, up, Term.eval_weakenBound]
    simp only [body_m, Formula.satisfies, PowerlessPairBounded.ordered_formula_l,
      PowerlessMapBounded.formula_l, up₃, up₂, up, Term.eval_weakenBound, Term.eval,
      Env.pushBound_bound_here, Env.pushBound_bound_there]
    apply and_congr_right
    intro _
    apply and_congr_right
    intro hw
    have h₀ : PowerlessRelativeFiniteProgramOutputBounded.guard_l φ (parameters_l ξ)
        ((up₃ B).eval ξ) ((up₃ β).eval ξ) ((up₃ C).eval ξ) ((up₃ W).eval ξ) ((up₃ ω).eval ξ)
        w n ((up₃ Q).eval ξ) ((up₃ e).eval ξ) ((up₃ t₀).eval ξ) ((up₃ t₁).eval ξ)
        ((up₃ t₂).eval ξ) ((up₃ a).eval ξ) n := by
      simp only [hEval, ξ, parameters_pushBound_l]
      exact ⟨hB, hβ, hW, hBW, hC, hCW, hω, hωW, hwW, he, ha, hw, ht, hφ, hφW, hn⟩
    cases actual
    · simpa only [Bool.false_eq_true, if_false, hEval, ξ, parameters_pushBound_l,
        Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there] using
        PowerlessRelativeFiniteProgramBoundOutputBounded.output_formula_l K φ ξ
          (up₃ B) (up₃ β) (up₃ C) (up₃ W) (up₃ ω) (.bvar (.there (.there .here)))
          (.bvar .here) (up₃ Q) (up₃ e) (up₃ t₀) (up₃ t₁) (up₃ t₂) (up₃ a)
          (.bvar .here) (.bvar (.there .here)) (up₃ y)
          (by simpa only [ξ, Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there] using h₀)
    · simpa only [if_true, hEval, ξ, parameters_pushBound_l,
        Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there] using
        PowerlessRelativeFiniteProgramBoundOutputBounded.run_formula_l K φ ξ
          (up₃ B) (up₃ β) (up₃ C) (up₃ W) (up₃ ω) (.bvar (.there (.there .here)))
          (.bvar .here) (up₃ Q) (up₃ e) (up₃ t₀) (up₃ t₁) (up₃ t₂) (up₃ a)
          (.bvar .here) (.bvar (.there .here)) (up₃ y)
          (by simpa only [ξ, Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there] using h₀)
  simp only [matrix_m, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, Arguments.eval, up₃, up₂, up, Term.eval_weakenBound, Term.eval]
  change (∃ w, mem_l hℳ w (W.eval η) ∧ ∃ k, mem_l hℳ k (ω.eval η) ∧
    ∃ n, mem_l hℳ n (ω.eval η) ∧
      (body_m actual φ (up₃ B) (up₃ C) (up₃ W) (up₃ ω) (up₃ Q) (up₃ e)
        (up₃ t₀) (up₃ t₁) (up₃ t₂) (up₃ a) (up₃ p) (up₃ y)
        (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)).satisfies
          (((η.pushBound w).pushBound k).pushBound n)) ↔ _
  constructor
  · rintro ⟨w, hwW, k, hk, n, hn, h⟩
    obtain ⟨hCode, hw, hRead⟩ := (hBody w k n hwW hn).mp h
    exact ⟨w, k, n, hCode, hk, hn, hw, hRead⟩
  · rintro ⟨w, k, n, hCode, hk, hn, hw, hRead⟩
    have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
    have hwW := PowerlessRelativeLimitFiniteMaps.subset_member_l hℳ hB hβ hW K
      (hωEq ▸ hωW) hQW (hωEq ▸ hn) hw
    exact ⟨w, hwW, k, hk, n, hn, (hBody w k n hwW hn).mpr ⟨hCode, hw, hRead⟩⟩

def schema_m {Δ : SortContext ℒ} (actual : Bool) (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β C W ω Q e t₀ t₁ t₂ a p y : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (guard_m φ B β C W ω Q e t₀ t₁ t₂ a) <|
    .iff (matrix_m actual φ B C W ω Q e t₀ t₁ t₂ a p y)
      (PowerlessRelativeFiniteProgramEvaluation.matrix_m actual φ B C ω Q e t₀ t₁ t₂ a p y)

def sentence_m {Δ : SortContext ℒ} (actual : Bool) (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β C W ω Q e t₀ t₁ t₂ a p y : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m actual φ B β C W ω Q e t₀ t₁ t₂ a p y)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (actual : Bool) (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β C W ω Q e t₀ t₁ t₂ a p y : Term ℒ [] Δ .set) :
    (sentence_m actual φ B β C W ω Q e t₀ t₁ t₂ a p y).TrueIn
      (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, guard_formula_l K,
    PowerlessRelativeFiniteProgramEvaluation.matrix_formula_l K]
  intro η h
  exact matrix_formula_l K actual φ η B β C W ω Q e t₀ t₁ t₂ a p y h

theorem derives_m {Δ : SortContext ℒ} (actual : Bool) (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β C W ω Q e t₀ t₁ t₂ a p y : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m actual φ B β C W ω Q e t₀ t₁ t₂ a p y)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ h𝒩 => models_l h𝒩 actual φ B β C W ω Q e t₀ t₁ t₂ a p y)

#print axioms matrix_delta_l
#print axioms matrix_member_l
#print axioms matrix_formula_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramEvaluationBounded
