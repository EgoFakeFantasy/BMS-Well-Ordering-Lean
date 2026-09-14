import BMSConstructibleBridge.PowerlessStageClosure
import BMSConstructibleBridge.PowerlessAppendGraph

/-! # 非零极限层中的有序对、添元及函数图追加 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageGraphClosure

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ α A : carrier_l ℳ} (hω : omega_l ω)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
  (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A) (hα : PowerlessStagePair.limit_l α)

include hℳ hω ht hT hA hα

theorem ordered_l {a b p : carrier_l ℳ} (ha : member_l ℳ a A) (hb : member_l ℳ b A)
    (hp : ThirdOrderSemantics.ordered_l a b p) : member_l ℳ p A := by
  obtain ⟨x, y, hx, hy, hp⟩ := hp
  have hxA := PowerlessStageClosure.pair_l hℳ hω hA hα ht hT ha ha hx
  have hyA := PowerlessStageClosure.pair_l hℳ hω hA hα ht hT ha hb hy
  exact PowerlessStageClosure.pair_l hℳ hω hA hα ht hT hxA hyA hp

theorem adjoin_l {f a g : carrier_l ℳ} (hf : member_l ℳ f A) (ha : member_l ℳ a A)
    (hg : ∀ x, member_l ℳ x g ↔ member_l ℳ x f ∨ x = a) : member_l ℳ g A := by
  obtain ⟨p, hp⟩ := PowerlessBasic.pairing_l hℳ a a
  obtain ⟨q, hq⟩ := PowerlessBasic.pairing_l hℳ f p
  have hpA := PowerlessStageClosure.pair_l hℳ hω hA hα ht hT ha ha hp
  have hqA := PowerlessStageClosure.pair_l hℳ hω hA hα ht hT hf hpA hq
  apply PowerlessStageClosure.union_l hℳ hω hA hα ht hT hqA
  intro x
  refine (hg x).trans ?_
  constructor
  · rintro (hx | hx)
    · exact ⟨f, (hq f).mpr (Or.inl rfl), hx⟩
    · exact ⟨p, (hq p).mpr (Or.inr rfl), (hp x).mpr (Or.inl hx)⟩
  · rintro ⟨y, hy, hx⟩
    rcases (hq y).mp hy with hy | hy
    · exact Or.inl (hy ▸ hx)
    · exact Or.inr ((hp x).mp (hy ▸ hx) |>.elim id id)

theorem append_l {f n a g : carrier_l ℳ} (hf : member_l ℳ f A) (hn : member_l ℳ n A)
    (ha : member_l ℳ a A) (hg : PowerlessAppendGraph.append_l f n a g) : member_l ℳ g A := by
  obtain ⟨p, hp⟩ := PowerlessBasic.ordered_exists_l hℳ n a
  apply adjoin_l hℳ hω ht hT hA hα hf (ordered_l hℳ hω ht hT hA hα hn ha hp)
  intro x
  exact (hg x).trans (or_congr Iff.rfl
    ⟨fun hx => PowerlessBasic.ordered_unique_l hℳ hx hp, fun hx => hx.symm ▸ hp⟩)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageGraphClosure
