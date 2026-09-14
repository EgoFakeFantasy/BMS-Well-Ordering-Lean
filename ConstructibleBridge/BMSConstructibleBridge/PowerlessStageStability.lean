import BMSConstructibleBridge.PowerlessStageEvaluation
import BMSConstructibleBridge.PowerlessLevyComposition
import BMSConstructibleBridge.PowerlessStagePair

/-!
# 实际层端点的内部有限层初等关系

内部 n 是证书分类的真实界；两端要求 ω < α < β 且为非零极限。
先给未经 BM4 复杂度重编号的关系，不声称已满足反射框架的全部合同。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageStability

open Logic FirstOrder ThirdOrderSemantics
open PowerlessStageEvaluation (system_l system_m system_formula_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def stable_l (ω e T t₁ t₂ t₃ n α β : carrier_l ℳ) : Prop :=
  member_l ℳ n ω ∧ PowerlessStagePair.proper_l ω α β ∧
    ∃ A B S R F G, system_l ω e T t₁ t₂ t₃ α A S F ∧
      system_l ω e T t₁ t₂ t₃ β B R G ∧
      PowerlessLevyAgreement.agreement_l ω e T t₁ t₂ t₃ A G F n

def stable_m {Γ Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ n α β : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (s : Term ℒ Γ Δ .set) := ((((((s.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set)
  .conj (SecondOrderObjectSyntax.member_m n ω) (.conj (PowerlessStagePair.proper_m ω α β)
    (.existsE .set (.existsE .set (.existsE .set (.existsE .set (.existsE .set (.existsE .set (.conj (system_m (w ω) (w e) (w T) (w t₁) (w t₂) (w t₃) (w α) (.bvar (.there (.there (.there (.there (.there .here)))))) (.bvar (.there (.there (.there .here)))) (.bvar (.there .here)))
      (.conj (system_m (w ω) (w e) (w T) (w t₁) (w t₂) (w t₃) (w β) (.bvar (.there (.there (.there (.there .here))))) (.bvar (.there (.there .here))) (.bvar .here))
        (PowerlessLevyAgreement.agreement_m (w ω) (w e) (w T) (w t₁) (w t₂) (w t₃) (.bvar (.there (.there (.there (.there (.there .here)))))) (.bvar .here) (.bvar (.there .here)) (w n)))))))))))

theorem stable_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ n α β : Term ℒ Γ Δ .set) :
    (stable_m ω e T t₁ t₂ t₃ n α β).satisfies η ↔
      stable_l (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
        (n.eval η) (α.eval η) (β.eval η) := by
  simp only [stable_m, stable_l, Formula.satisfies, PowerlessStagePair.proper_formula_l hℳ,
    system_formula_l hℳ, PowerlessLevyAgreement.agreement_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

-- 任意指定的实际系统都读取同一个稳定关系，不依赖存在见证的选择。
theorem compare_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ n α β A B S R F G : carrier_l ℳ} (hω : omega_l ω)
    (hA : system_l ω e T t₁ t₂ t₃ α A S F) (hB : system_l ω e T t₁ t₂ t₃ β B R G) :
    stable_l ω e T t₁ t₂ t₃ n α β ↔ member_l ℳ n ω ∧ PowerlessStagePair.proper_l ω α β ∧
      PowerlessLevyAgreement.agreement_l ω e T t₁ t₂ t₃ A G F n := by
  constructor
  · rintro ⟨hn, hp, C, D, Q, V, H, J, hC, hD, h⟩
    obtain ⟨h₁, h₂, h₃⟩ := PowerlessStageEvaluation.unique_l hℳ hω hC hA
    subst C
    subst Q
    subst H
    obtain ⟨h₁, h₂, h₃⟩ := PowerlessStageEvaluation.unique_l hℳ hω hD hB
    subst D
    subst V
    subst J
    exact ⟨hn, hp, h⟩
  · rintro ⟨hn, hp, h⟩
    exact ⟨hn, hp, A, B, S, R, F, G, hA, hB, h⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageStability
