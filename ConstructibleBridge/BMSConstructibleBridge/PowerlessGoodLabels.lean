import BMSConstructibleBridge.PowerlessRelabelLevels
import BMSConstructibleBridge.PowerlessExtension

/-!
# 最小好边界以下的实际初始标签

先反射内部一上的常值图，在读取端点以下取得一个好标签；再保留该标签作低处图，
第二次反射插入另一个好标签。所有有限行的稳定关系由同一重标号消费者实际保持。
本模块给出初始标签数据，不把它误当作内部 BMS 展开或 Z₂ 良序终局。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessGoodLabels

open Logic FirstOrder ThirdOrderSemantics
open PowerlessRelabelLevels (level_m levels_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

/-- 固定高度内的全部重编号稳定关系；各数码只在命题中存在化。 -/
def stable_l (ω e T t₁ t₂ t₃ c N : carrier_l ℳ) (H : Nat) (a b : carrier_l ℳ) : Prop :=
  ∀ j, j < H → ∃ m, PowerlessNumeral.numeral_l e (level_m H j) m ∧
    PowerlessGoodBoundary.stable_l ω e T t₁ t₂ t₃ c N m a b

section StablePair

variable (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ c N n α β A B S R F G : carrier_l ℳ}
  (hω : omega_l ω) (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
  (hT : PowerlessTriangular.triangular_l ω e T)
  (hA : PowerlessStageEvaluation.system_l ω e T t₁ t₂ t₃ α A S F)
  (hB : PowerlessStageEvaluation.system_l ω e T t₁ t₂ t₃ β B R G)
  {H : Nat} (hc : PowerlessGoodBoundary.code_l ω e T t₁ t₂ t₃ c N (level_m H H))
  (hc₀ : member_l ℳ c ω) (hN : member_l ℳ N ω)
  (hn : PowerlessNumeral.numeral_l e (level_m H H) n)
  (hs : PowerlessGoodBoundary.stable_l ω e T t₁ t₂ t₃ c N n α β)

include hℳ hω ht hT hA hB hc hc₀ hN hn hs

/-- 在内部有限低处图之上插入一个好标签，同时保留它对读取端点的全部低行稳定性。 -/
theorem insert_l {p f : carrier_l ℳ} (hp : member_l ℳ p ω) (hf : map_l f p A)
    (hα : ∀ i a, value_l f i a → member_l ℳ a α) :
    ∃ b, PowerlessCodedDiagram.good_l ω e T t₁ t₂ t₃ c N b ∧ member_l ℳ b α ∧
      stable_l ω e T t₁ t₂ t₃ c N H b α ∧
      ∀ i a, value_l f i a → member_l ℳ a b ∧
        ∀ j, j < H → ∀ m, PowerlessNumeral.numeral_l e (level_m H j) m →
          PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ m a α →
          PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ m a b := by
  have heω := PowerlessNatural.zero_mem_l hℳ hω ht.1
  obtain ⟨q, hq⟩ := PowerlessNatural.successor_exists_l hℳ e
  have hqω := PowerlessNatural.successor_mem_l hℳ hω heω hq
  have heq := (hq e).mpr (Or.inr rfl)
  obtain ⟨g, C, hg, hg₀⟩ := PowerlessExtension.constant_l hℳ q α
  have hαB := (PowerlessStageOrdinal.member_l hℳ hω ht hT hB.1 hs.1.2.1.1).mpr
    hs.2.2.2.1.2.1
  have hgB : map_l g q B := PowerlessFunction.range_l hℳ hg (fun i a ha => by
    rw [((hg₀ i a).mp ha).2]
    exact hαB)
  have hG : ∀ i a, value_l g i a → PowerlessCodedDiagram.good_l ω e T t₁ t₂ t₃ c N a := by
    intro i a ha
    rw [((hg₀ i a).mp ha).2]
    exact hs.1
  have hfg : ∀ i j a b, value_l f i a → value_l g j b → member_l ℳ a b := by
    intro i j a b ha hb
    rw [((hg₀ j b).mp hb).2]
    exact hα i a ha
  have hgα : value_l g e α := (hg₀ e α).mpr ⟨heq, rfl⟩
  obtain ⟨Λ, Θ, h, hΛ, hΘ, hΛ₀, hΘ₀, hh, hI⟩ :=
    PowerlessRelabelLevels.exists_l hℳ hω ht hT hA hB (Nat.le_refl H) hc hc₀ hN hn hs
      hp hqω hf hgB hG hfg
  obtain ⟨b, ⟨_, hb⟩, _⟩ := hh.2 e heq
  have hbG := hI.labels_l e b hb
  refine ⟨b, hbG, hI.bounded_l e b hb, ?_, ?_⟩
  · intro j hj
    have h : level_m H j ∈ Θ.map Prod.fst := hΘ.symm ▸ PowerlessRelabelLevels.mem_m H hj
    obtain ⟨t, ht₀, ht₁⟩ := List.mem_map.mp h
    have hm : PowerlessNumeral.numeral_l e (level_m H j) t.2 := by
      simpa only [ht₁] using hΘ₀ t ht₀
    have hS := PowerlessGoodBoundary.monotone_l hℳ hω ht.1 hT
      (PowerlessNumeral.natural_l hℳ hω ht.1 hm)
      (PowerlessSourceStandardBudget.numeral_le_subset_l hℳ e
        (PowerlessRelabelLevels.mono_m H (Nat.le_of_lt hj)) hm hn) hs
    exact ⟨t.2, hm, hbG, hs.1, hI.top_l t ht₀ e α b hgα hS.2.2 hb⟩
  · intro i a ha
    refine ⟨hI.lower_l i e a b ha hb, ?_⟩
    intro j hj m hm hS
    have h : level_m H j ∈ Λ.map Prod.fst := hΛ.symm ▸ PowerlessRelabelLevels.mem_m H hj
    obtain ⟨t, ht₀, ht₁⟩ := List.mem_map.mp h
    have hm₀ : PowerlessNumeral.numeral_l e (level_m H j) t.2 := by
      simpa only [ht₁] using hΛ₀ t ht₀
    have hm₁ := PowerlessNumeral.unique_l hℳ hm₀ hm
    have hS₀ : PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ t.2 a α := hm₁.symm ▸ hS
    exact hm₁ ▸ hI.lower_stable_l t ht₀ i e a α b ha hgα hS₀ hb

/-- 空低处图给出读取端点以下的实际好标签及全部低行稳定关系。 -/
theorem below_l : ∃ a, PowerlessCodedDiagram.good_l ω e T t₁ t₂ t₃ c N a ∧
    member_l ℳ a α ∧ stable_l ω e T t₁ t₂ t₃ c N H a α := by
  have hf : map_l e e A :=
    ⟨fun p hp => (ht.1 p hp).elim, fun x hx => (ht.1 x hx).elim⟩
  obtain ⟨a, ha, hα, hS, _⟩ := insert_l hℳ hω ht hT hA hB hc hc₀ hN hn hs
    (PowerlessNatural.zero_mem_l hℳ hω ht.1) hf (fun i a ha =>
      (ht.1 i (PowerlessFunction.value_mem_l hℳ hf ha).1).elim)
  exact ⟨a, ha, hα, hS⟩

/-- 两次实际重标号产生初始的两个严格递增好标签，不预设该标签对存在。 -/
theorem pair_l : ∃ a b, PowerlessCodedDiagram.good_l ω e T t₁ t₂ t₃ c N a ∧
    PowerlessCodedDiagram.good_l ω e T t₁ t₂ t₃ c N b ∧ member_l ℳ a b ∧ member_l ℳ b α ∧
    stable_l ω e T t₁ t₂ t₃ c N H a b ∧ stable_l ω e T t₁ t₂ t₃ c N H b α := by
  obtain ⟨a, haG, ha, hS⟩ := below_l hℳ hω ht hT hA hB hc hc₀ hN hn hs
  have heω := PowerlessNatural.zero_mem_l hℳ hω ht.1
  obtain ⟨p, hp⟩ := PowerlessNatural.successor_exists_l hℳ e
  have hpω := PowerlessNatural.successor_mem_l hℳ hω heω hp
  obtain ⟨f, C, hf, hf₀⟩ := PowerlessExtension.constant_l hℳ p a
  have haA := (PowerlessStageOrdinal.member_l hℳ hω ht hT hA.1 haG.2.1.1).mpr ha
  have hfA : map_l f p A := PowerlessFunction.range_l hℳ hf (fun i b hb => by
    rw [((hf₀ i b).mp hb).2]
    exact haA)
  have hfα : ∀ i b, value_l f i b → member_l ℳ b α := by
    intro i b hb
    rw [((hf₀ i b).mp hb).2]
    exact ha
  obtain ⟨b, hbG, hb, hT₀, h⟩ := insert_l hℳ hω ht hT hA hB hc hc₀ hN hn hs hpω hfA hfα
  have hfa : value_l f e a := (hf₀ e a).mpr ⟨(hp e).mpr (Or.inr rfl), rfl⟩
  refine ⟨a, b, haG, hbG, (h e a hfa).1, hb, ?_, hT₀⟩
  intro j hj
  obtain ⟨m, hm, hS₀⟩ := hS j hj
  exact ⟨m, hm, haG, hbG, (h e a hfa).2 j hj m hm hS₀.2.2⟩

end StablePair

/-- 同一次支持编码的最小最高边界以下，实际存在高度 H 所需的初始标签对。 -/
theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T) (H : Nat) :
    ∃ c N n σ a b, member_l ℳ c ω ∧ member_l ℳ N ω ∧
      PowerlessGoodBoundary.code_l ω e T t₁ t₂ t₃ c N (level_m H H) ∧
      PowerlessNumeral.numeral_l e (level_m H H) n ∧
      PowerlessGoodBoundary.boundary_l ω e T t₁ t₂ t₃ c N n σ ∧
      PowerlessCodedDiagram.good_l ω e T t₁ t₂ t₃ c N a ∧
      PowerlessCodedDiagram.good_l ω e T t₁ t₂ t₃ c N b ∧ member_l ℳ a b ∧ member_l ℳ b σ ∧
      stable_l ω e T t₁ t₂ t₃ c N H a b ∧ stable_l ω e T t₁ t₂ t₃ c N H b σ := by
  obtain ⟨c, N, hc₀, hN, hc, h⟩ := PowerlessRelabelLevels.boundaries_l hℳ hω ht hT H
  obtain ⟨n, σ, hn, hσ⟩ := h H (Nat.le_refl H)
  obtain ⟨β, hs⟩ := hσ.1
  obtain ⟨A, B, S, R, F, G, hA, hB, _⟩ := hs.2.2.2.2
  obtain ⟨a, b, ha, hb, hab, hbσ, hS, hT₀⟩ := pair_l hℳ hω ht hT hA hB hc hc₀ hN hn hs
  exact ⟨c, N, n, σ, a, b, hc₀, hN, hc, hn, hσ, ha, hb, hab, hbσ, hS, hT₀⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessGoodLabels
