import BMSConstructibleBridge.PowerlessRelabelDiagram
import BMSConstructibleBridge.PowerlessRelabelSource

/-!
# 从原标签构造全部有限关系记录及上层共同见证

外部有限列表只列出所需层号及其内部数码。每项的两个边图与顶端迹都由
实际原标签图构造，且属于同一下层；不要求原高处标签图属于下层。
给定原高处图的好标签不变量，它本身同时实现全部矩阵条件，而非分别选择图。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelabelWitness

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

universe u

/-- 一个外部层号的数码、低高边图、高高边图及顶端迹。 -/
structure entry_l (ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ) where
  k : Nat
  n : carrier_l ℳ
  D : carrier_l ℳ
  E : carrier_l ℳ
  S : carrier_l ℳ

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def levels_l (Ξ : List (entry_l ℳ)) : List (Nat × carrier_l ℳ) :=
  Ξ.map (fun s => (s.k, s.n))

def edges_l (Ξ : List (entry_l ℳ)) : List (carrier_l ℳ × carrier_l ℳ × carrier_l ℳ) :=
  Ξ.map (fun s => (s.n, s.D, s.E))

def traces_l (Ξ : List (entry_l ℳ)) : List (carrier_l ℳ × carrier_l ℳ) :=
  Ξ.map (fun s => (s.n, s.S))

def records_l (ω e T t₁ t₂ t₃ A β p q f g : carrier_l ℳ) (s : entry_l ℳ) : Prop :=
  member_l ℳ s.D A ∧ member_l ℳ s.E A ∧ member_l ℳ s.S A ∧
  PowerlessRelabelDiagram.edges_l (PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ s.n)
    p q f g s.D ∧
  PowerlessRelabelDiagram.edges_l (PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ s.n)
    q q g g s.E ∧
  PowerlessRelabelDiagram.trace_l
    (fun a => PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ s.n a β) q g s.S

/-- 层号列表保持原顺序与重数，各记录均实际构造并属于同一下层。 -/
theorem family_exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ α A p q : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hα : PowerlessStagePair.limit_l α) (hωα : subset_l ω α)
    (hp : member_l ℳ p ω) (hq : member_l ℳ q ω)
    (β f g : carrier_l ℳ) (Λ : List (Nat × carrier_l ℳ)) :
    ∃ Ξ, levels_l Ξ = Λ ∧ ∀ s ∈ Ξ, records_l ω e T t₁ t₂ t₃ A β p q f g s := by
  induction Λ with
  | nil => exact ⟨List.nil, rfl, fun _ h => (List.not_mem_nil h).elim⟩
  | cons j Λ ih =>
    obtain ⟨Ξ, hΞ, h⟩ := ih
    obtain ⟨D, hDA, hD⟩ := PowerlessRelabelDiagram.stable_exists_l hℳ hω ht hT hA hα hωα hp hq j.2 f g
    obtain ⟨E, hEA, hE⟩ := PowerlessRelabelDiagram.stable_exists_l hℳ hω ht hT hA hα hωα hq hq j.2 g g
    obtain ⟨S, hSA, hS⟩ := PowerlessRelabelDiagram.trace_exists_l hℳ hω ht hT hA hα hωα hq j.2 β g
    let s : entry_l ℳ := ⟨j.1, j.2, D, E, S⟩
    refine ⟨s :: Ξ, ?_, ?_⟩
    · change j :: levels_l Ξ = j :: Λ
      rw [hΞ]
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨hDA, hEA, hSA, hD, hE, hS⟩
      · exact h t ht

/-- 从原层号列表把数码及层号界传到每项记录；迹的子集性来自实际记录语义。
记录构造本身无需数码假设，只有后续读取顶端真值时才消费这些条件。 -/
theorem trace_bounds_l {ω e T t₁ t₂ t₃ A β p q f g : carrier_l ℳ}
    {Ξ : List (entry_l ℳ)} {Λ : List (Nat × carrier_l ℳ)} {k : Nat}
    (hΛ : levels_l Ξ = Λ)
    (h : ∀ t ∈ Λ, t.1 ≤ k ∧ PowerlessNumeral.numeral_l e t.1 t.2)
    (hΞ : ∀ s ∈ Ξ, records_l ω e T t₁ t₂ t₃ A β p q f g s) :
    ∀ s ∈ Ξ, s.k ≤ k ∧ PowerlessNumeral.numeral_l e s.k s.n ∧ subset_l s.S q := by
  intro s hs
  have ht : (s.k, s.n) ∈ Λ := by
    rw [← hΛ]
    exact List.mem_map.mpr ⟨s, hs, rfl⟩
  exact ⟨(h _ ht).1, (h _ ht).2, PowerlessRelabelDiagram.trace_subset_l (hΞ s hs).2.2.2.2.2⟩

/-- 同一原高处图同时实现所有原子记录及全部逐值好标签条件。 -/
theorem realizes_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ c N A β p q f g B D E : carrier_l ℳ}
    (hg : map_l g q B)
    (hG : ∀ i a, value_l g i a → PowerlessCodedDiagram.good_l ω e T t₁ t₂ t₃ c N a)
    (hD : PowerlessRelabelDiagram.edges_l (member_l ℳ) p q f g D)
    (hE : PowerlessRelabelDiagram.edges_l (member_l ℳ) q q g g E)
    (Ξ Ω : List (entry_l ℳ))
    (hΞ : ∀ s ∈ Ξ, records_l ω e T t₁ t₂ t₃ A β p q f g s)
    (hΩ : ∀ s ∈ Ω, records_l ω e T t₁ t₂ t₃ A β p q f g s) :
    PowerlessRelabelSource.conditions_l ω e T t₁ t₂ t₃ c N β f g D E (edges_l Ξ) (traces_l Ω) := by
  refine ⟨hG, PowerlessRelabelDiagram.realizes_l hD, PowerlessRelabelDiagram.realizes_l hE, ?_, ?_⟩
  · simp only [edges_l, List.forall_mem_map]
    intro s hs
    have h := hΞ s hs
    exact ⟨PowerlessRelabelDiagram.realizes_l h.2.2.2.1,
      PowerlessRelabelDiagram.realizes_l h.2.2.2.2.1⟩
  · simp only [traces_l, List.forall_mem_map]
    intro s hs
    exact PowerlessRelabelDiagram.trace_realizes_l hℳ hg (hΩ s hs).2.2.2.2.2

/-- 从给定的原好标签图实际构造所有记录，并得到它作为上层共同见证。
没有假定待构造的关系图、迹或整个矩阵已经存在。 -/
theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ α A p q : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hα : PowerlessStagePair.limit_l α) (hωα : subset_l ω α)
    (hp : member_l ℳ p ω) (hq : member_l ℳ q ω)
    (c N β f g B : carrier_l ℳ) (hg : map_l g q B)
    (hG : ∀ i a, value_l g i a → PowerlessCodedDiagram.good_l ω e T t₁ t₂ t₃ c N a)
    (Λ : List (Nat × carrier_l ℳ)) :
    ∃ D E Ξ, member_l ℳ D A ∧ member_l ℳ E A ∧ levels_l Ξ = Λ ∧
      PowerlessRelabelDiagram.edges_l (member_l ℳ) p q f g D ∧
      PowerlessRelabelDiagram.edges_l (member_l ℳ) q q g g E ∧
      (∀ s ∈ Ξ, records_l ω e T t₁ t₂ t₃ A β p q f g s) ∧
      PowerlessRelabelSource.conditions_l ω e T t₁ t₂ t₃ c N β f g D E (edges_l Ξ) (traces_l Ξ) := by
  obtain ⟨D, hDA, hD⟩ := PowerlessRelabelDiagram.order_exists_l hℳ hω ht hT hA hα hωα hp hq f g
  obtain ⟨E, hEA, hE⟩ := PowerlessRelabelDiagram.order_exists_l hℳ hω ht hT hA hα hωα hq hq g g
  obtain ⟨Ξ, hΛ, hΞ⟩ := family_exists_l hℳ hω ht hT hA hα hωα hp hq β f g Λ
  exact ⟨D, E, Ξ, hDA, hEA, hΛ, hD, hE, hΞ, realizes_l hℳ hg hG hD hE Ξ Ξ hΞ hΞ⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelabelWitness
