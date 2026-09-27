import BMSConstructibleBridge.PowerlessRelabelLevels
import BMSConstructibleBridge.PowerlessConcatenation

/-!
# 重标号后的实际两次标签拼接

旧前缀 f 后接同一反射图 h，得到界 α 以下的 u；再接回原末块 g，得到界 β 以下的 v。
这正是标签更新所需的“替换当前块、恢复原末块”布局。具名边和低行顶端迹继续
由同一个 h 保持，两个拼接图都给出精确下标规格。尚未将这些边识别为原 BMS 祖先边。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelabelAppend

open Logic FirstOrder ThirdOrderSemantics
open PowerlessRelabelLevels (level_m levels_m)
open PowerlessConcatenation (increasing_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

/-- 两张实际拼接图共用一个反射见证；各字段只记录已经构造的图的性质。 -/
structure step_l (ω e T t₁ t₂ t₃ c N α β p q r s f g h u v : carrier_l ℳ)
    (Λ Θ : List (Nat × carrier_l ℳ)) : Prop where
  natural_l : member_l ℳ r ω ∧ member_l ℳ s ω
  length_l : PowerlessAddition.addition_l ω e p q r
  next_length_l : PowerlessAddition.addition_l ω e r q s
  image_map_l : map_l h q α
  prefix_map_l : map_l u r α
  map_l : ThirdOrderSemantics.map_l v s β
  prefix_graph_l : PowerlessConcatenation.graph_l ω e p f h u
  graph_l : PowerlessConcatenation.graph_l ω e r u g v
  prefix_order_l : increasing_l u
  order_l : increasing_l v
  prefix_labels_l : ∀ i a, value_l u i a → PowerlessCodedDiagram.good_l ω e T t₁ t₂ t₃ c N a
  labels_l : ∀ i a, value_l v i a → PowerlessCodedDiagram.good_l ω e T t₁ t₂ t₃ c N a
  image_l : PowerlessRelabelPreservation.image_l ω e T t₁ t₂ t₃ c N α β f g h Λ Θ

/-- 实际重标号并拼接 f+h+g；不要求调用者提供反射图、拼接图或矩阵见证。 -/
theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ c N n α β A B S R F G p q f g : carrier_l ℳ}
    (hω : omega_l ω) (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (hA : PowerlessStageEvaluation.system_l ω e T t₁ t₂ t₃ α A S F)
    (hB : PowerlessStageEvaluation.system_l ω e T t₁ t₂ t₃ β B R G)
    {k H : Nat} (hk : k ≤ H)
    (hc : PowerlessGoodBoundary.code_l ω e T t₁ t₂ t₃ c N (level_m H H))
    (hc₀ : member_l ℳ c ω) (hN : member_l ℳ N ω)
    (hn : PowerlessNumeral.numeral_l e (level_m H k) n)
    (hs : PowerlessGoodBoundary.stable_l ω e T t₁ t₂ t₃ c N n α β)
    (hp : member_l ℳ p ω) (hq : member_l ℳ q ω) (hf : map_l f p A) (hg : map_l g q B)
    (hF : ∀ i a, value_l f i a → PowerlessCodedDiagram.good_l ω e T t₁ t₂ t₃ c N a)
    (hG : ∀ i a, value_l g i a → PowerlessCodedDiagram.good_l ω e T t₁ t₂ t₃ c N a)
    (hf₀ : increasing_l f) (hg₀ : increasing_l g)
    (hα : ∀ i a, value_l g i a → member_l ℳ α a ∨ α = a) :
    ∃ Λ Θ r s h u v, Λ.map Prod.fst = levels_m H H ∧ Θ.map Prod.fst = levels_m H k ∧
      (∀ t ∈ Λ, PowerlessNumeral.numeral_l e t.1 t.2) ∧
      (∀ t ∈ Θ, PowerlessNumeral.numeral_l e t.1 t.2) ∧
      step_l ω e T t₁ t₂ t₃ c N α β p q r s f g h u v Λ Θ := by
  have hfα : map_l f p α := PowerlessFunction.range_l hℳ hf (fun i a ha =>
    (PowerlessStageOrdinal.member_l hℳ hω ht hT hA.1 (hF i a ha).2.1.1).mp
      (PowerlessFunction.value_mem_l hℳ hf ha).2)
  have hgβ : map_l g q β := PowerlessFunction.range_l hℳ hg (fun i a ha =>
    (PowerlessStageOrdinal.member_l hℳ hω ht hT hB.1 (hG i a ha).2.1.1).mp
      (PowerlessFunction.value_mem_l hℳ hg ha).2)
  have hαg : ∀ i a b, member_l ℳ a α → value_l g i b → member_l ℳ a b := by
    intro i a b ha hb
    rcases hα i b hb with h | h
    · exact PowerlessOrdinal.transitive_l (hG i b hb).2.1.1 α a h ha
    · exact h ▸ ha
  have hfg : ∀ i j a b, value_l f i a → value_l g j b → member_l ℳ a b :=
    fun _ j _ _ ha hb => hαg j _ _ (PowerlessFunction.value_mem_l hℳ hfα ha).2 hb
  obtain ⟨Λ, Θ, h, hΛ, hΘ, hΛ₀, hΘ₀, hh, hI⟩ :=
    PowerlessRelabelLevels.exists_l hℳ hω ht hT hA hB hk hc hc₀ hN hn hs hp hq hf hg hG hfg
  have hhα := PowerlessFunction.range_l hℳ hh hI.bounded_l
  have hh₀ : increasing_l h := by
    intro i j a b hij ha hb
    obtain ⟨a₀, ⟨_, ha₀⟩, _⟩ := hg.2 i (PowerlessFunction.value_mem_l hℳ hh ha).1
    obtain ⟨b₀, ⟨_, hb₀⟩, _⟩ := hg.2 j (PowerlessFunction.value_mem_l hℳ hh hb).1
    exact hI.order_l i j a₀ b₀ a b ha₀ hb₀ (hg₀ i j a₀ b₀ hij ha₀ hb₀) ha hb
  obtain ⟨r, hrω, hr⟩ := PowerlessAddition.exists_l hℳ hω ht.1 hp hq
  obtain ⟨u, hu, hU⟩ := PowerlessConcatenation.exists_l hℳ hω ht.1 hp hq hr hfα hhα
  have hu₀ := PowerlessConcatenation.order_l hℳ hω ht.1 hp hfα hU hf₀ hh₀ hI.lower_l
  have hU₀ := PowerlessConcatenation.labels_l hU hF hI.labels_l
  have huβ : map_l u r β := PowerlessFunction.range_l hℳ hu (fun _ a ha =>
    PowerlessOrdinal.transitive_l hs.2.1.2.1.1 α a hs.2.2.2.1.2.1
      (PowerlessFunction.value_mem_l hℳ hu ha).2)
  obtain ⟨s, hsω, hs₀⟩ := PowerlessAddition.exists_l hℳ hω ht.1 hrω hq
  obtain ⟨v, hv, hV⟩ := PowerlessConcatenation.exists_l hℳ hω ht.1 hrω hq hs₀ huβ hgβ
  have huv : ∀ i j a b, value_l u i a → value_l g j b → member_l ℳ a b :=
    fun _ j _ _ ha hb => hαg j _ _ (PowerlessFunction.value_mem_l hℳ hu ha).2 hb
  exact ⟨Λ, Θ, r, s, h, u, v, hΛ, hΘ, hΛ₀, hΘ₀, ⟨⟨hrω, hsω⟩, hr, hs₀, hhα, hu, hv,
    hU, hV, hu₀, PowerlessConcatenation.order_l hℳ hω ht.1 hrω huβ hV hu₀ hg₀ huv,
    hU₀, PowerlessConcatenation.labels_l hV hU₀ hG, hI⟩⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelabelAppend
