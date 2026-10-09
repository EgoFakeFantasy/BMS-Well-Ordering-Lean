import BMSConstructibleBridge.PowerlessLegacyTranslationGraph
import BMSConstructibleBridge.PowerlessHierarchyLightHistory

/-! # 旧五标签语法图的纯数字读数资格

对象语言只有隶属。合法图 V 与旧翻译图 Q 的读数仅在内部 ω 两个
坐标上约束；不声称它们在非数字输入上没有额外图值。第四标签用
真实后继公式限定，全部检查器和图值均为纯 Δ₀。这是共同族捕获
实际编码包所需的资格矩阵，不预设完整源模型或外部标准自然数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyNumericSyntax

open Logic FirstOrder ThirdOrderSemantics StabilityFrame

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)

def spec_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e t₁ t₂ t₃ t₄ P N V Q : carrier_l 𝒩) : Prop :=
  PowerlessHierarchyLightHistory.successor_holds_l t₃ t₄ ∧
    (∀ c, member_l 𝒩 c ω → ∀ l, member_l 𝒩 l ω →
      (value_l (ℳ := 𝒩) V c l ↔ PowerlessLegacyValidityBounded.certificate_holds_l
        (𝒩 := 𝒩) ω e N t₁ t₂ t₃ t₄ c l)) ∧
    (∀ c, member_l 𝒩 c ω → ∀ s, member_l 𝒩 s ω →
      (value_l (ℳ := 𝒩) Q c s ↔ PowerlessLegacyTranslationGraph.holds_l
        (𝒩 := 𝒩) ω e N P t₁ t₂ t₃ t₄ V c s))

def formula_m {Γ Δ : SortContext ℒ}
    (ω e t₁ t₂ t₃ t₄ P N V Q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessHierarchyLightHistory.successor_m t₃ t₄) <| .conj
    (membershipLevyBound.boundedForall ω <|
      membershipLevyBound.boundedForall (up ω) <|
        .iff (PowerlessValueBounded.formula_m (up₂ V) (.bvar (.there .here)) (.bvar .here))
          (PowerlessLegacyValidityBounded.certificate_m (up₂ ω) (up₂ e) (up₂ N)
            (up₂ t₁) (up₂ t₂) (up₂ t₃) (up₂ t₄) (.bvar (.there .here)) (.bvar .here)))
    (membershipLevyBound.boundedForall ω <|
      membershipLevyBound.boundedForall (up ω) <|
        .iff (PowerlessValueBounded.formula_m (up₂ Q) (.bvar (.there .here)) (.bvar .here))
          (PowerlessLegacyTranslationGraph.formula_m (up₂ ω) (up₂ e) (up₂ N) (up₂ P)
            (up₂ t₁) (up₂ t₂) (up₂ t₃) (up₂ t₄) (up₂ V)
            (.bvar (.there .here)) (.bvar .here)))

theorem delta_l {Γ Δ : SortContext ℒ}
    (ω e t₁ t₂ t₃ t₄ P N V Q : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m ω e t₁ t₂ t₃ t₄ P N V Q) :=
  .conj (PowerlessHierarchyLightHistory.successor_delta_l _ _) <| .conj
    (.bounded_forall ω <| .bounded_forall (up ω) <|
      .iff (PowerlessValueBounded.delta_l _ _ _)
        (PowerlessLegacyValidityBounded.certificate_delta_l _ _ _ _ _ _ _ _ _))
    (.bounded_forall ω <| .bounded_forall (up ω) <|
      .iff (PowerlessValueBounded.delta_l _ _ _)
        (PowerlessLegacyTranslationGraph.delta_l _ _ _ _ _ _ _ _ _ _ _))

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e t₁ t₂ t₃ t₄ P N V Q : Term ℒ Γ Δ .set) :
    (formula_m ω e t₁ t₂ t₃ t₄ P N V Q).satisfies η ↔
      spec_l (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (t₄.eval η)
        (P.eval η) (N.eval η) (V.eval η) (Q.eval η) := by
  simp only [formula_m, spec_l, Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessHierarchyLightHistory.successor_formula_l, PowerlessValueBounded.formula_l,
    PowerlessLegacyValidityBounded.certificate_formula_l,
    PowerlessLegacyTranslationGraph.formula_l, Arguments.eval, up₂, up,
    Term.eval_weakenBound, Term.eval]
  rfl

#print axioms delta_l
#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyNumericSyntax
