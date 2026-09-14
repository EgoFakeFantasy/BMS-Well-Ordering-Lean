import BMSConstructibleBridge.PowerlessEvaluationEntry
import BMSConstructibleBridge.PowerlessEvaluationPrefixAbsolute

/-!
# 有限前缀成员公式在小层中接受的真实证书

只解释已经在域内的候选证书；外部总图的实际证书是否落在域内另行证明。
有限长度 guard 提供原 recursion_m 所需关系图，不对小层使用核心公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationEntrySource

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem stage_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ β B : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hB : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ β B)
    (hωβ : member_l ℳ ω β) (hβ : PowerlessStagePair.limit_l β)
    {hB₀ : ∃ x, member_l ℳ x B} {Γ Δ : SortContext ℒ} (η : Env (structure_l B hB₀) Γ Δ)
    (w z U A s₁ s₂ s₃ S p : Term ℒ Γ Δ .set)
    (hw : (w.eval η).val = ω) (hz : (z.eval η).val = e) (hU : (U.eval η).val = T)
    (h₁ : (s₁.eval η).val = t₁) (h₂ : (s₂.eval η).val = t₂) (h₃ : (s₃.eval η).val = t₃) :
    (PowerlessEvaluationEntry.entry_m w z U A s₁ s₂ s₃ S p).satisfies η ↔
      ∃ m G n Y : type_l B, member_l ℳ m.val ω ∧
        PowerlessEvaluationPrefix.prefix_l ω e T (A.eval η).val t₁ t₂ t₃ (S.eval η).val G.val m.val ∧
        value_l G.val n.val Y.val ∧ ordered_l n.val Y.val (p.eval η).val := by
  have hBT := PowerlessStageStructure.transitive_l hℳ hω ht hT hB
  simp only [PowerlessEvaluationEntry.entry_m, Formula.satisfies, value_formula_l, ordered_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  apply exists_congr
  intro m
  apply exists_congr
  intro G
  apply exists_congr
  intro n
  apply exists_congr
  intro Y
  change (member_l ℳ m.val (w.eval η).val ∧ _) ↔ (member_l ℳ m.val ω ∧ _)
  rw [hw]
  apply and_congr_right
  intro hm
  apply and_congr
  · let q (t : Term ℒ Γ Δ .set) := (((t.weakenBound SetTheory.SetSort.set).weakenBound
      SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
    have h := PowerlessEvaluationPrefixAbsolute.stage_l hℳ hω ht hT hB hωβ hβ
        ((((η.pushBound m).pushBound G).pushBound n).pushBound Y)
        (q w) (q z) (q U) (q A) (q s₁) (q s₂) (q s₃) (q S)
        (.bvar (.there (.there .here))) (.bvar (.there (.there (.there .here))))
        (by simpa only [q, Term.eval_weakenBound] using hw)
        (by simpa only [q, Term.eval_weakenBound] using hz)
        (by simpa only [q, Term.eval_weakenBound] using hU)
        (by simpa only [q, Term.eval_weakenBound] using h₁)
        (by simpa only [q, Term.eval_weakenBound] using h₂)
        (by simpa only [q, Term.eval_weakenBound] using h₃) hm
    simp only [q, Term.eval_weakenBound] at h
    simpa only [Term.eval, Env.pushBound, Assignment.push] using h
  · exact and_congr (PowerlessSourceGraphAbsolute.value_l hBT) (PowerlessSourceGraphAbsolute.ordered_l hBT)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationEntrySource
