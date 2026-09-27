import BMSConstructibleBridge.PowerlessRelabelWitness

/-!
# 从同一反射图还原原重标号的逐列结论

索引和标签始终是模型内部集合。两份外部列表分别限定具名边与顶端迹的层号。
反射图的好标签条件与读取层的序数截面给出严格上界；其余结论从原精确记录
及真实函数图的唯一取值推出，不使用宿主良基性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelabelPreservation

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

/-- 内部有限标签图的完整逐值重标号规格；这里不声称已经存在该图。 -/
structure image_l (ω e T t₁ t₂ t₃ c N α β f g h : carrier_l ℳ)
    (Λ Θ : List (Nat × carrier_l ℳ)) : Prop where
  labels_l : ∀ i a, value_l h i a → PowerlessCodedDiagram.good_l ω e T t₁ t₂ t₃ c N a
  lower_l : ∀ i j a b, value_l f i a → value_l h j b → member_l ℳ a b
  bounded_l : ∀ i a, value_l h i a → member_l ℳ a α
  order_l : ∀ i j a b a₁ b₁, value_l g i a → value_l g j b → member_l ℳ a b →
    value_l h i a₁ → value_l h j b₁ → member_l ℳ a₁ b₁
  lower_stable_l : ∀ t ∈ Λ, ∀ i j a b b₁, value_l f i a → value_l g j b →
    PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ t.2 a b → value_l h j b₁ →
    PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ t.2 a b₁
  upper_stable_l : ∀ t ∈ Λ, ∀ i j a b a₁ b₁, value_l g i a → value_l g j b →
    PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ t.2 a b → value_l h i a₁ → value_l h j b₁ →
    PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ t.2 a₁ b₁
  top_l : ∀ t ∈ Θ, ∀ i a b, value_l g i a →
    PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ t.2 a β → value_l h i b →
    PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ t.2 b α

/-- 精确记录由原图生成，条件由同一新图满足时，逐值原重标号规格全部成立。 -/
theorem extract_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ c N α β A B p q f g h D E : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hf : map_l f p A) (hg : map_l g q B) (hh : map_l h q A)
    (hfg : ∀ i j a b, value_l f i a → value_l g j b → member_l ℳ a b)
    (hD : PowerlessRelabelDiagram.edges_l (member_l ℳ) p q f g D)
    (hE : PowerlessRelabelDiagram.edges_l (member_l ℳ) q q g g E)
    (Ξ Ω : List (PowerlessRelabelWitness.entry_l ℳ)) (Λ Θ : List (Nat × carrier_l ℳ))
    (hΛ : PowerlessRelabelWitness.levels_l Ξ = Λ)
    (hΘ : PowerlessRelabelWitness.levels_l Ω = Θ)
    (hΞ : ∀ s ∈ Ξ, PowerlessRelabelWitness.records_l ω e T t₁ t₂ t₃ A β p q f g s)
    (hΩ : ∀ s ∈ Ω, PowerlessRelabelWitness.records_l ω e T t₁ t₂ t₃ A β p q f g s)
    (h₀ : PowerlessRelabelSource.conditions_l ω e T t₁ t₂ t₃ c N α f h D E
      (PowerlessRelabelWitness.edges_l Ξ) (PowerlessRelabelWitness.traces_l Ω)) :
    image_l ω e T t₁ t₂ t₃ c N α β f g h Λ Θ := by
  obtain ⟨hG, hD₁, hE₁, hS, hU⟩ := h₀
  simp only [PowerlessRelabelWitness.edges_l, List.forall_mem_map] at hS
  simp only [PowerlessRelabelWitness.traces_l, List.forall_mem_map] at hU
  have hΛ₀ (t : Nat × carrier_l ℳ) (ht : t ∈ Λ) :
      ∃ s ∈ Ξ, (s.k, s.n) = t := by
    rw [← hΛ] at ht
    exact List.mem_map.mp ht
  refine ⟨hG, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j a b ha hb
    have hi := (PowerlessFunction.value_mem_l hℳ hf ha).1
    have hj := (PowerlessFunction.value_mem_l hℳ hh hb).1
    obtain ⟨b₀, ⟨_, hb₀⟩, _⟩ := hg.2 j hj
    exact PowerlessRelabelDiagram.preserves_l hℳ hD hf hh hD₁ hi hj ha hb₀
      (hfg i j a b₀ ha hb₀) ha hb
  · intro i a ha
    exact (PowerlessStageOrdinal.member_l hℳ hω ht hT hA (hG i a ha).2.1.1).mp
      (PowerlessFunction.value_mem_l hℳ hh ha).2
  · intro i j a b a₁ b₁ ha hb hab ha₁ hb₁
    exact PowerlessRelabelDiagram.preserves_l hℳ hE hh hh hE₁
      (PowerlessFunction.value_mem_l hℳ hg ha).1 (PowerlessFunction.value_mem_l hℳ hg hb).1
      ha hb hab ha₁ hb₁
  · intro t ht i j a b b₁ ha hb hab hb₁
    obtain ⟨s, hs, hs₀⟩ := hΛ₀ t ht
    have hn : s.n = t.2 := congrArg Prod.snd hs₀
    have hD₀ := (hΞ s hs).2.2.2.1
    have hD₂ := (hS s hs).1
    rw [hn] at hD₀ hD₂
    exact PowerlessRelabelDiagram.preserves_l hℳ hD₀ hf hh hD₂
      (PowerlessFunction.value_mem_l hℳ hf ha).1 (PowerlessFunction.value_mem_l hℳ hg hb).1
      ha hb hab ha hb₁
  · intro t ht i j a b a₁ b₁ ha hb hab ha₁ hb₁
    obtain ⟨s, hs, hs₀⟩ := hΛ₀ t ht
    have hn : s.n = t.2 := congrArg Prod.snd hs₀
    have hE₀ := (hΞ s hs).2.2.2.2.1
    have hE₂ := (hS s hs).2
    rw [hn] at hE₀ hE₂
    exact PowerlessRelabelDiagram.preserves_l hℳ hE₀ hh hh hE₂
      (PowerlessFunction.value_mem_l hℳ hg ha).1 (PowerlessFunction.value_mem_l hℳ hg hb).1
      ha hb hab ha₁ hb₁
  · intro t ht i a b ha hab hb
    have ht₀ : t ∈ PowerlessRelabelWitness.levels_l Ω := hΘ.symm ▸ ht
    obtain ⟨s, hs, hs₀⟩ := List.mem_map.mp ht₀
    have hn : s.n = t.2 := congrArg Prod.snd hs₀
    have hS₀ := (hΩ s hs).2.2.2.2.2
    have hS₁ := hU s hs
    rw [hn] at hS₀ hS₁
    exact hS₁ i ((hS₀ i).mpr ⟨(PowerlessFunction.value_mem_l hℳ hg ha).1, a, ha, hab⟩) b hb

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelabelPreservation
