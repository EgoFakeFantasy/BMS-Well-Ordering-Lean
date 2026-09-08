import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Delta1ProofPresentation

/-! # 公理行的直接正负表示接口

可靠性和完备性针对公理成员关系，而非其演绎闭包。此接口可供完整证明树
检查器消费；单独的公理实例不构成 `Delta1ProofPresentation`。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT
open Nonlogical.BasicSetTheory QuineEncoding
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

structure Delta1AxiomPresentation (Trepresent Taxes : SetTheory) where
  condition : FormulaTemplate.Binary
  delta0 : ∀ {bound free : SetContext} (packet output : SetTerm bound free),
    Formula.IsDelta0 set_levy_bound (condition packet output)
  checked : Nat → SetSentence → Bool
  checked_sound : ∀ {packet formula}, checked packet formula = true → Taxes formula
  checked_complete : ∀ {formula}, Taxes formula → ∃ packet, checked packet formula = true
  condition_positive : ∀ {packet formula}, checked packet formula = true →
    Derives Trepresent [] (condition (numₘ(packet)) (IntrinsicQuotation.quote formula))
  condition_negative : ∀ {packet formula}, checked packet formula = false →
    Derives Trepresent [] (¬ₘ condition (numₘ(packet)) (IntrinsicQuotation.quote formula))

namespace Delta1AxiomPresentation

/-- 两个具体公理表示以同一证书域上的析取合并，包含全部接受与拒绝分支。 -/
def union {Trepresent T U : SetTheory}
    (left : Delta1AxiomPresentation Trepresent T) (right : Delta1AxiomPresentation Trepresent U) :
    Delta1AxiomPresentation Trepresent (Theory.union T U) where
  condition := ⟨.disj left.condition.body right.condition.body⟩
  delta0 packet output := .disj (left.delta0 packet output) (right.delta0 packet output)
  checked packet φ := left.checked packet φ || right.checked packet φ
  checked_sound h := by
    rcases Bool.or_eq_true_iff.mp h with h | h
    · exact Or.inl (left.checked_sound h)
    · exact Or.inr (right.checked_sound h)
  checked_complete h := by
    rcases h with h | h
    · obtain ⟨packet, hPacket⟩ := left.checked_complete h
      exact ⟨packet, Bool.or_eq_true_iff.mpr (Or.inl hPacket)⟩
    · obtain ⟨packet, hPacket⟩ := right.checked_complete h
      exact ⟨packet, Bool.or_eq_true_iff.mpr (Or.inr hPacket)⟩
  condition_positive h := by
    rcases Bool.or_eq_true_iff.mp h with h | h
    · exact FirstOrder.Derives.disj_intro_left (left.condition_positive h)
    · exact FirstOrder.Derives.disj_intro_right (right.condition_positive h)
  condition_negative h := by
    obtain ⟨hLeft, hRight⟩ := Bool.or_eq_false_iff.mp h
    apply FirstOrder.Derives.neg_intro
    apply FirstOrder.Derives.disj_elim (FirstOrder.Derives.assumption List.mem_cons_self)
    · exact FirstOrder.Derives.neg_elim (FirstOrder.Derives.assumption List.mem_cons_self)
        (FirstOrder.Derives.context_weaken_cons (FirstOrder.Derives.context_weaken_cons (left.condition_negative hLeft)))
    · exact FirstOrder.Derives.neg_elim (FirstOrder.Derives.assumption List.mem_cons_self)
        (FirstOrder.Derives.context_weaken_cons (FirstOrder.Derives.context_weaken_cons (right.condition_negative hRight)))

theorem condition_sigma1 {Trepresent Taxes : SetTheory} (P : Delta1AxiomPresentation Trepresent Taxes)
    {bound free : SetContext} (packet output : SetTerm bound free) :
    Formula.IsSigma1 set_levy_bound (P.condition packet output) := (P.delta0 packet output).to_sigma1

theorem condition_pi1 {Trepresent Taxes : SetTheory} (P : Delta1AxiomPresentation Trepresent Taxes)
    {bound free : SetContext} (packet output : SetTerm bound free) :
    Formula.IsPi1 set_levy_bound (P.condition packet output) := (P.delta0 packet output).to_pi1

theorem member_iff_checked {Trepresent Taxes : SetTheory} (P : Delta1AxiomPresentation Trepresent Taxes)
    (formula : SetSentence) : Taxes formula ↔ ∃ packet, P.checked packet formula = true :=
  ⟨P.checked_complete, fun ⟨_, h⟩ => P.checked_sound h⟩
end Delta1AxiomPresentation

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT
