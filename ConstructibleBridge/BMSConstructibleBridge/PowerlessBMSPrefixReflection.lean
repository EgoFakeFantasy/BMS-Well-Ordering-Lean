import BMSConstructibleBridge.PowerlessBMSPrefixRepresentation
import BMSConstructibleBridge.PowerlessRelabelAppend

/-!
# 同一最终数组上反射当前末块

旧标签图是 f+g；实际反射步骤提供 f+h。按祖先边两端所在的块分类，
旧前缀边不变，前缀到末块以及末块内部的边由同一反射图保持。
逆向跨块不可能，因为真实祖先列严格位于目标列之前。
所得前缀图的标签全部低于 α；最后一次反射可直接用它按实际宽度封口。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSPrefixReflection

open Logic FirstOrder ThirdOrderSemantics
open PowerlessRelabelLevels (level_m levels_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  {ω e : carrier_l ℳ} {he : PowerlessNatural.zero_l e} {h₀ : member_l ℳ e ω}
  {F : PowerlessArithmetic.operations_l ω e}

/-- 反射当前末块保持该前缀内全部真实祖先边，同时把上界从 β 降至 α。 -/
theorem image_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    {T t₁ t₂ t₃ c N α β A B f g h old u v s : carrier_l ℳ} {H : Nat}
    {y p q r : PowerlessArithmetic.num_l ω} {Λ Θ : List (Nat × carrier_l ℳ)}
    (hOld : PowerlessBMSPrefixRepresentation.representation_l (he := he) (h₀ := h₀) (F := F)
      T t₁ t₂ t₃ c N H y r β old)
    (hgraph : PowerlessConcatenation.graph_l ω e p.val f g old)
    (hf : map_l f p.val A) (hg : map_l g q.val B)
    (hstep : PowerlessRelabelAppend.step_l ω e T t₁ t₂ t₃ c N α β p.val q.val r.val s f g h u v Λ Θ)
    (hΛ : Λ.map Prod.fst = levels_m (H + 1) (H + 1))
    (hΛ₀ : ∀ tag ∈ Λ, PowerlessNumeral.numeral_l e tag.1 tag.2) :
    PowerlessBMSPrefixRepresentation.representation_l (he := he) (h₀ := h₀) (F := F)
      T t₁ t₂ t₃ c N H y r α u := by
  refine ⟨hstep.prefix_map_l, hstep.prefix_labels_l, hstep.prefix_order_l, ?_⟩
  intro j hj row hrow i t hit a b ha hb
  have hlevel : level_m (H + 1) j ∈ Λ.map Prod.fst :=
    hΛ.symm ▸ PowerlessRelabelLevels.mem_m (H + 1) (Nat.lt_trans hj (Nat.lt_succ_self H))
  obtain ⟨tag, htag, htag₀⟩ := List.mem_map.mp hlevel
  have hnum : PowerlessNumeral.numeral_l e (level_m (H + 1) j) tag.2 := htag₀ ▸ hΛ₀ tag htag
  refine ⟨tag.2, hnum, ?_⟩
  have edge (a₀ b₀ : carrier_l ℳ) (ha₀ : value_l old i.val a₀) (hb₀ : value_l old t.val b₀) :
      PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ tag.2 a₀ b₀ := by
    obtain ⟨m, hm, hstable⟩ := hOld.edge_l j hj row hrow i t hit a₀ b₀ ha₀ hb₀
    exact PowerlessNumeral.unique_l hℳ hm hnum ▸ hstable
  rcases (hstep.prefix_graph_l i.val a).mp ha with ha | ⟨i₀, hi₀, ha⟩
  · rcases (hstep.prefix_graph_l t.val b).mp hb with hb | ⟨t₀, ht₀, hb⟩
    · exact edge a b ((hgraph i.val a).mpr (Or.inl ha)) ((hgraph t.val b).mpr (Or.inl hb))
    · obtain ⟨b₀, ⟨_, hb₀⟩, _⟩ := hg.2 t₀ (PowerlessFunction.value_mem_l hℳ hstep.image_map_l hb).1
      exact hstep.image_l.lower_stable_l tag htag i.val t₀ a b₀ b ha hb₀
        (edge a b₀ ((hgraph i.val a).mpr (Or.inl ha))
          ((hgraph t.val b₀).mpr (Or.inr ⟨t₀, ht₀, hb₀⟩))) hb
  · rcases (hstep.prefix_graph_l t.val b).mp hb with hb | ⟨t₀, ht₀, hb⟩
    · have hip : member_l ℳ i.val p.val := PowerlessNaturalOrder.member_transitive_l hℳ hω p.val p.property
        t.val i.val (PowerlessFunction.value_mem_l hℳ hf hb).1 (PowerlessBMSAncestor.bound_l hℳ hω hit)
      rcases PowerlessAdditionBounds.lower_l hℳ hω he p.property hi₀ with hpi | hpi
      · exact (PowerlessNatural.asymmetry_l hℳ hip hpi).elim
      · have hii : member_l ℳ i.val i.val := hpi ▸ hip
        exact (PowerlessNatural.asymmetry_l hℳ hii hii).elim
    · obtain ⟨a₀, ⟨_, ha₀⟩, _⟩ := hg.2 i₀ (PowerlessFunction.value_mem_l hℳ hstep.image_map_l ha).1
      obtain ⟨b₀, ⟨_, hb₀⟩, _⟩ := hg.2 t₀ (PowerlessFunction.value_mem_l hℳ hstep.image_map_l hb).1
      exact hstep.image_l.upper_stable_l tag htag i₀ t₀ a₀ b₀ a b ha₀ hb₀
        (edge a₀ b₀ ((hgraph i.val a₀).mpr (Or.inr ⟨i₀, hi₀, ha₀⟩))
          ((hgraph t.val b₀).mpr (Or.inr ⟨t₀, ht₀, hb₀⟩))) ha hb

/-- 实际构造同一反射图及两个拼接图；不要求调用者先提供反射见证或层系统。 -/
theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    {T t₁ t₂ t₃ c N n α β f g old : carrier_l ℳ} {H k : Nat}
    {y p q r : PowerlessArithmetic.num_l ω}
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (hk : k ≤ H + 1)
    (hc : PowerlessGoodBoundary.code_l ω e T t₁ t₂ t₃ c N (level_m (H + 1) (H + 1)))
    (hc₀ : member_l ℳ c ω) (hN : member_l ℳ N ω)
    (hn : PowerlessNumeral.numeral_l e (level_m (H + 1) k) n)
    (hs : PowerlessGoodBoundary.stable_l ω e T t₁ t₂ t₃ c N n α β)
    (hOld : PowerlessBMSPrefixRepresentation.representation_l (he := he) (h₀ := h₀) (F := F)
      T t₁ t₂ t₃ c N H y r β old)
    (hgraph : PowerlessConcatenation.graph_l ω e p.val f g old)
    (hspan : PowerlessAddition.addition_l ω e p.val q.val r.val)
    (hf : map_l f p.val α) (hg : map_l g q.val β)
    (hG : ∀ i a, value_l g i a → PowerlessCodedDiagram.good_l ω e T t₁ t₂ t₃ c N a)
    (hg₀ : PowerlessConcatenation.increasing_l g)
    (hα : ∀ i a, value_l g i a → member_l ℳ α a ∨ α = a) :
    ∃ Λ Θ s h u v, Λ.map Prod.fst = levels_m (H + 1) (H + 1) ∧
      Θ.map Prod.fst = levels_m (H + 1) k ∧
      (∀ tag ∈ Λ, PowerlessNumeral.numeral_l e tag.1 tag.2) ∧
      (∀ tag ∈ Θ, PowerlessNumeral.numeral_l e tag.1 tag.2) ∧
      PowerlessRelabelAppend.step_l ω e T t₁ t₂ t₃ c N α β p.val q.val r.val s f g h u v Λ Θ ∧
      PowerlessBMSPrefixRepresentation.representation_l (he := he) (h₀ := h₀) (F := F)
        T t₁ t₂ t₃ c N H y r α u := by
  have hF : ∀ i a, value_l f i a → PowerlessCodedDiagram.good_l ω e T t₁ t₂ t₃ c N a :=
    fun i a ha => hOld.labels_l i a ((hgraph i a).mpr (Or.inl ha))
  have hf₀ : PowerlessConcatenation.increasing_l f := fun i j a b hij ha hb =>
    hOld.order_l i j a b hij ((hgraph i a).mpr (Or.inl ha)) ((hgraph j b).mpr (Or.inl hb))
  obtain ⟨A, B, S, R, Fₐ, Fᵦ, hA, hB, _⟩ := hs.2.2.2.2
  have hfA : map_l f p.val A := PowerlessFunction.range_l hℳ hf (fun i a ha =>
    (PowerlessStageOrdinal.member_l hℳ hω ht hT hA.1 (hF i a ha).2.1.1).mpr
      (PowerlessFunction.value_mem_l hℳ hf ha).2)
  have hgB : map_l g q.val B := PowerlessFunction.range_l hℳ hg (fun i a ha =>
    (PowerlessStageOrdinal.member_l hℳ hω ht hT hB.1 (hG i a ha).2.1.1).mpr
      (PowerlessFunction.value_mem_l hℳ hg ha).2)
  obtain ⟨Λ, Θ, r₁, s, h, u, v, hΛ, hΘ, hΛ₀, hΘ₀, hstep⟩ :=
    PowerlessRelabelAppend.exists_l hℳ hω ht hT hA hB hk hc hc₀ hN hn hs
      p.property q.property hfA hgB hF hG hf₀ hg₀ hα
  have hlength : r₁ = r.val := PowerlessAddition.unique_l hℳ hω he hstep.length_l hspan
  subst r₁
  exact ⟨Λ, Θ, s, h, u, v, hΛ, hΘ, hΛ₀, hΘ₀, hstep,
    image_l hℳ hω hOld hgraph hf hg hstep hΛ hΛ₀⟩

#print axioms image_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSPrefixReflection
