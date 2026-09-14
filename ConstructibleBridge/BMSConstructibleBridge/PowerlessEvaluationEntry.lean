import BMSConstructibleBridge.PowerlessEvaluationPrefixRestriction

/-!
# 用有限求值前缀识别整个图的一个成员

证书只包含一个内部有限初段图及其取值，不把总图 F 放入定义参数。
原递归唯一性保证任意被接受的有限证书与实际总图一致。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationEntry

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def entry_l (ω e T A t₁ t₂ t₃ S p : carrier_l ℳ) : Prop :=
  ∃ m G n Y, member_l ℳ m ω ∧ PowerlessEvaluationPrefix.prefix_l ω e T A t₁ t₂ t₃ S G m ∧
    value_l G n Y ∧ ordered_l n Y p

def entry_m {Γ Δ : SortContext ℒ} (ω e T A t₁ t₂ t₃ S p : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := (((t.weakenBound SetTheory.SetSort.set).weakenBound
    SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <|
    .conj (SecondOrderObjectSyntax.member_m (.bvar (.there (.there (.there .here)))) (w ω))
      (.conj (PowerlessEvaluationPrefix.prefix_m (w ω) (w e) (w T) (w A) (w t₁) (w t₂) (w t₃) (w S)
        (.bvar (.there (.there .here))) (.bvar (.there (.there (.there .here)))))
        (.conj (SecondOrderObjectSyntax.value_m (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))
          (SecondOrderObjectSyntax.ordered_m (.bvar (.there .here)) (.bvar .here) (w p))))

theorem entry_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T A t₁ t₂ t₃ S p : Term ℒ Γ Δ .set) :
    (entry_m ω e T A t₁ t₂ t₃ S p).satisfies η ↔
      entry_l (ω.eval η) (e.eval η) (T.eval η) (A.eval η) (t₁.eval η) (t₂.eval η)
        (t₃.eval η) (S.eval η) (p.eval η) := by
  simp only [entry_m, entry_l, Formula.satisfies, PowerlessEvaluationPrefix.prefix_formula_l hℳ,
    value_formula_l, ordered_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

theorem member_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A t₁ t₂ t₃ S F : carrier_l ℳ} (hω : omega_l ω)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F) (p : carrier_l ℳ) :
    entry_l ω e T A t₁ t₂ t₃ S p ↔ ThirdOrderSemantics.member_l ℳ p F := by
  constructor
  · rintro ⟨m, G, n, Y, hm, hG, hY, hp⟩
    have h := PowerlessEvaluationPrefixRestriction.value_l hℳ hF hG
      (PowerlessOrdinal.mem_l (PowerlessOmegaOrdinal.ordinal_l hℳ hω) hm)
      (PowerlessNaturalOrder.subset_l hℳ hω m hm)
    obtain ⟨q, hq, hq₀⟩ := ((h n Y).mp hY).2
    exact (PowerlessBasic.ordered_unique_l hℳ hq₀ hp) ▸ hq
  · intro hp
    obtain ⟨D, hD, hE⟩ := hF
    obtain ⟨n, Y, hn, _, hp₀⟩ := hD.1 p hp
    obtain ⟨m, hm⟩ := PowerlessNatural.successor_exists_l hℳ n
    have hm₀ := PowerlessNatural.successor_mem_l hℳ hω hn hm
    obtain ⟨G, hG, h⟩ := PowerlessEvaluationPrefixRestriction.exists_l hℳ ⟨D, hD, hE⟩
      (PowerlessOrdinal.mem_l (PowerlessOmegaOrdinal.ordinal_l hℳ hω) hm₀)
      (PowerlessNaturalOrder.subset_l hℳ hω m hm₀)
    exact ⟨m, G, n, Y, hm₀, hG, (h n Y).mpr ⟨(hm n).mpr (Or.inr rfl), p, hp, hp₀⟩, hp₀⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationEntry
