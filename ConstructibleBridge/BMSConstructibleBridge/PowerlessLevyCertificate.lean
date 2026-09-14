import BMSConstructibleBridge.PowerlessLevyRule

/-!
# 全内部有限层级证书

D 是有内部自然数界的实际记录集；其中每个可读取判断都须满足极性
与生成规则。分类量化实际 D 和实际 n，不是外部 Nat 索引的证明模式。
没有判断的填充值不产生结论；依赖按公式码、层号的字典序严格下降。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLevyCertificate

open Logic FirstOrder ThirdOrderSemantics PowerlessLevyEntry PowerlessLevyRule

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def certificate_l (ω e T t₁ t₂ t₃ D : carrier_l ℳ) : Prop :=
  (∃ N, member_l ℳ N ω ∧ subset_l D N) ∧ ∀ c n p, entry_l ω e T D c n p →
    polarity_l e t₁ p ∧ step_l ω e T t₁ t₂ t₃ D c n p

def certificate_m {Γ Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ D : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (s : Term ℒ Γ Δ .set) := s.weakenBound SetTheory.SetSort.set
  let v (s : Term ℒ Γ Δ .set) := ((w s).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .conj (.existsE .set (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) (w ω))
    (ThirdOrderTheory.subset_m (w D) (.bvar .here))))
    (.forallE .set (.forallE .set (.forallE .set (.imp
      (entry_m (v ω) (v e) (v T) (v D) (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))
      (.conj (polarity_m (v e) (v t₁) (.bvar .here))
        (step_m (v ω) (v e) (v T) (v t₁) (v t₂) (v t₃) (v D)
          (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)))))))

theorem certificate_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ D : Term ℒ Γ Δ .set) :
    (certificate_m ω e T t₁ t₂ t₃ D).satisfies η ↔
      certificate_l (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (D.eval η) := by
  simp only [certificate_m, certificate_l, Formula.satisfies, subset_formula_l, entry_formula_l,
    polarity_formula_l, step_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

def class_l (ω e T t₁ t₂ t₃ c n p : carrier_l ℳ) : Prop :=
  ∃ D, certificate_l ω e T t₁ t₂ t₃ D ∧ entry_l ω e T D c n p

def class_m {Γ Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ c n p : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (s : Term ℒ Γ Δ .set) := s.weakenBound SetTheory.SetSort.set
  .existsE .set (.conj (certificate_m (w ω) (w e) (w T) (w t₁) (w t₂) (w t₃) (.bvar .here))
    (entry_m (w ω) (w e) (w T) (.bvar .here) (w c) (w n) (w p)))

theorem class_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ c n p : Term ℒ Γ Δ .set) :
    (class_m ω e T t₁ t₂ t₃ c n p).satisfies η ↔
      class_l (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
        (c.eval η) (n.eval η) (p.eval η) := by
  simp only [class_m, class_l, Formula.satisfies, certificate_formula_l, entry_formula_l, Term.eval_weakenBound]
  rfl

theorem natural_l {ω e T t₁ t₂ t₃ c n p : carrier_l ℳ} (h : class_l ω e T t₁ t₂ t₃ c n p) :
    member_l ℳ c ω ∧ member_l ℳ n ω ∧ member_l ℳ p ω ∧ polarity_l e t₁ p := by
  obtain ⟨D, hD, hc⟩ := h
  obtain ⟨hc₀, hn, hp⟩ := PowerlessLevyEntry.natural_l hc
  exact ⟨hc₀, hn, hp, (hD.2 c n p hc).1⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLevyCertificate
