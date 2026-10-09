import BMSConstructibleBridge.PowerlessRelativeSourceSkolemFamily

/-! # 原有限见证图族的末端扩展

沿已存在的同一图族消去原存在量词，在末端加入一个实际结论。
Θ 是原装配上下文，σ 仅提升其项；Δ 始终是原矩阵参数上下文。
新图的 Class 性质来自原完整图规格，不将图加入常量种子。
标签保持在同一个种子 C。递归只遍历外部有限公式族。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceFamilyExtension

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev Entry (Ε : SortContext ℒ) := Term ℒ [] Ε .set × Term ℒ [] Ε .set
private abbrev free {Ε : SortContext ℒ} (t : Term ℒ [] Ε .set) :=
  t.weakenFree SetTheory.SetSort.set

def extension_m {Θ Δ Ε : SortContext ℒ}
    (χ : ∀ {Ε : SortContext ℒ}, (Variable Θ .set → Term ℒ [] Ε .set) →
      List (Entry Ε) → Formula ℒ [] Ε)
    (F : List (Formula ℒ [] (.set :: .set :: Δ))) (T : List (Variable Δ .set))
    (B W R : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (G : List (Entry Ε)) (σ : Variable Θ .set → Term ℒ [] Ε .set) : Formula ℒ [] Ε :=
  match F, T with
  | List.nil, _ => .conj (PowerlessRelativeSourceSkolemFamily.result_m B W G) (χ σ G)
  | List.cons _ _, List.nil => .falsum
  | List.cons φ F, List.cons v T =>
    let J : Term ℒ [] (.set :: Ε) .set := .fvar .here
    (Formula.conj (PowerlessRelativeSourceSkolemGraph.graph_m φ (free B) (free W) (free R) J
      (fun w => free (τ w)))
      (extension_m χ F T (free B) (free W) (free R) (fun w => free (τ w))
        ((free (τ v), J) :: G.map (fun p => (free p.1, free p.2)))
        (fun w => free (σ w)))).existsFreeTop .set

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem extension_l (K : source_coding_l hℳ) {Θ Δ : SortContext ℒ}
    (η : Env 𝒱 [] Θ) (b w c : SecondOrderQuotient.type_l hℳ)
    (χ : ∀ {Ε : SortContext ℒ}, (Variable Θ .set → Term ℒ [] Ε .set) →
      List (Entry Ε) → Formula ℒ [] Ε)
    (hχ : ∀ {Ε : SortContext ℒ} (ζ : Env 𝒱 [] Ε)
      (B W _R : Term ℒ [] Ε .set) (_τ : Variable Δ .set → Term ℒ [] Ε .set)
      (G : List (Entry Ε)) (σ : Variable Θ .set → Term ℒ [] Ε .set),
      (∀ v, (σ v).eval ζ = η.freeVal v) →
      B.eval ζ = b → W.eval ζ = w →
      (∀ s (v : Variable Ε s), PowerlessRelativeClassCorrespondence.member_l hℳ
        (B.eval ζ) (ζ.freeVal v)) →
      (∀ p ∈ G, mem_l hℳ (p.1.eval ζ) c) →
      (PowerlessRelativeSourceSkolemFamily.result_m B W G).satisfies ζ → (χ σ G).satisfies ζ)
    (F : List (Formula ℒ [] (.set :: .set :: Δ))) :
    ∀ (T : List (Variable Δ .set)) {Ε : SortContext ℒ} (ζ : Env 𝒱 [] Ε)
      (B W R : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
      (G : List (Entry Ε)) (σ : Variable Θ .set → Term ℒ [] Ε .set),
      (∀ v, (σ v).eval ζ = η.freeVal v) →
      B.eval ζ = b → W.eval ζ = w →
      (∀ s (v : Variable Ε s), PowerlessRelativeClassCorrespondence.member_l hℳ
        (B.eval ζ) (ζ.freeVal v)) →
      (∀ v ∈ T, mem_l hℳ ((τ v).eval ζ) c) →
      (∀ p ∈ G, mem_l hℳ (p.1.eval ζ) c) →
      (PowerlessRelativeSourceSkolemFamily.assemble_m F T B W R τ G).satisfies ζ →
      (extension_m χ F T B W R τ G σ).satisfies ζ := by
  induction F with
  | nil =>
    intro T Ε ζ B W R τ G σ hσ hB hW hClass _ hTags h
    exact ⟨h, hχ ζ B W R τ G σ hσ hB hW hClass hTags h⟩
  | cons φ F ih =>
    intro T Ε ζ B W R τ G σ hσ hB hW hClass hT hTags h
    cases T with
    | nil => exact h.elim
    | cons v T =>
      rw [PowerlessRelativeSourceSkolemFamily.assemble_m, Formula.satisfies_existsFreeTop] at h
      obtain ⟨j, hGraph, h⟩ := h
      let ξ : Env 𝒱 [] (.set :: Ε) := ζ.pushFree j
      let J : Term ℒ [] (.set :: Ε) .set := .fvar .here
      let G' : List (Entry (.set :: Ε)) :=
        (free (τ v), J) :: G.map (fun p => (free p.1, free p.2))
      have hf (t : Term ℒ [] Ε .set) : (free t).eval ξ = t.eval ζ := by
        simp only [free, Term.eval_weakenFree, ξ]
      have hj := PowerlessRelativeSourceSkolemGraph.class_l K φ ξ
        (free B) (free W) (free R) J (fun w => free (τ w)) hGraph
      have hClass' : ∀ s (w : Variable (.set :: Ε) s),
          PowerlessRelativeClassCorrespondence.member_l hℳ ((free B).eval ξ) (ξ.freeVal w) := by
        intro s w; cases s
        cases w with
        | here => exact hj
        | there w => simpa only [hf, ξ, Env.pushFree_there] using hClass _ w
      have hTags' : ∀ p ∈ G', mem_l hℳ (p.1.eval ξ) c := by
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · simpa only [hf] using hT v (by simp)
        · obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.mp hp
          simpa only [hf] using hTags p₀ hp₀
      rw [extension_m, Formula.satisfies_existsFreeTop]
      refine ⟨j, hGraph, ?_⟩
      exact ih T ξ (free B) (free W) (free R) (fun w => free (τ w)) G' (fun w => free (σ w))
        (fun w => (hf (σ w)).trans (hσ w)) ((hf B).trans hB) ((hf W).trans hW) hClass'
        (fun w hw => by simpa only [hf] using hT w (by simp [hw])) hTags' h

#print axioms extension_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceFamilyExtension
