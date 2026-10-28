import BMSConstructibleBridge.PowerlessEvaluationClause
import BMSConstructibleBridge.PowerlessValueBounded
import BMSConstructibleBridge.SecondOrderAxioms

/-! # 求值历史查询的纯 Δ₀ 公式

真值列 Y 是历史图的有序对坐标，故可用图内两层成员量词界定。
不预设历史是函数，也不把全部可能真值列的幂集作为界；非法查询仍保持
原关系的精确真假。公式等价的闭句有原 Z₂ 推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationQueryBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def formula_m {Γ Δ : SortContext ℒ} (H n f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists H <|
    membershipLevyBound.boundedExists (.bvar .here) <|
      membershipLevyBound.boundedExists (.bvar .here) <|
        .conj (PowerlessValueBounded.formula_m (up (up (up H))) (up (up (up n))) (.bvar .here))
          (SecondOrderObjectSyntax.member_m (up (up (up f))) (.bvar .here))

theorem delta_l {Γ Δ : SortContext ℒ} (H n f : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m H n f) :=
  .bounded_exists H (.bounded_exists (.bvar .here) (.bounded_exists (.bvar .here)
    (.conj (PowerlessValueBounded.delta_l _ _ _) (.rel _ _))))

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (H n f : Term ℒ Γ Δ .set) :
    (formula_m H n f).satisfies η ↔ PowerlessEvaluationClause.query_l (H.eval η) (n.eval η) (f.eval η) := by
  have h : (formula_m H n f).satisfies η ↔
      ∃ p, member_l 𝒩 p (H.eval η) ∧ ∃ t, member_l 𝒩 t p ∧ ∃ Y, member_l 𝒩 Y t ∧
        value_l (ℳ := 𝒩) (H.eval η) (n.eval η) Y ∧ member_l 𝒩 (f.eval η) Y := by
    simp only [formula_m, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
      membershipLevyBound, Formula.satisfies, PowerlessValueBounded.formula_l,
      SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
    rfl
  rw [h]
  constructor
  · rintro ⟨_, _, _, _, Y, _, hValue, hMember⟩
    exact ⟨Y, hValue, hMember⟩
  · rintro ⟨Y, hValue, hMember⟩
    obtain ⟨p, hp, s, t, hs, ht, hPair⟩ := hValue
    exact ⟨p, hp, t, (hPair t).mpr (Or.inr rfl), Y, (ht Y).mpr (Or.inr rfl),
      ⟨p, hp, s, t, hs, ht, hPair⟩, hMember⟩

def schema_m : Formula ℒ [] [.set, .set, .set] := .iff
  (formula_m (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here))))
  (PowerlessEvaluationClause.query_m (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here))))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) := by
  apply SecondOrderAxioms.interpretation_m
  intro ℳ hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  exact (formula_l η (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))).trans
    (PowerlessEvaluationClause.query_formula_l η (.fvar .here) (.fvar (.there .here))
      (.fvar (.there (.there .here)))).symm

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationQueryBounded
