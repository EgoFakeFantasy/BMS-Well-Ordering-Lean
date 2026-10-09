import BMSConstructibleBridge.PowerlessRelativeSourceFamilyExtension

/-! # 原有限图族末端的同见证传输

沿原 extension_m 的存在量词树保留同一批图和全部图规格，只传递
末端结论。递归仅遍历外部有限公式族，不遍历模型内部自然数或序数。
消去接口的目标为 Prop，不从存在命题抽取 Type 层的图选择函数。
本模块是原对象构造的语义装配辅助，不代替最终 Z₂ Derives。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceFamilyTransport

open Logic FirstOrder
open PowerlessRelativeSourceFamilyExtension (extension_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

private abbrev Entry (Ε : SortContext ℒ) := Term ℒ [] Ε .set × Term ℒ [] Ε .set
private abbrev free {Ε : SortContext ℒ} (t : Term ℒ [] Ε .set) :=
  t.weakenFree SetTheory.SetSort.set

variable {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}

/-- 只改变末端性质，原图量词、标签和规格保持逐项相同。 -/
theorem imp_l {Θ Δ : SortContext ℒ}
    (χ ψ : ∀ {Ε : SortContext ℒ}, (Variable Θ .set → Term ℒ [] Ε .set) →
      List (Entry Ε) → Formula ℒ [] Ε)
    (h : ∀ {Ε : SortContext ℒ} (ζ : Env 𝒩 [] Ε)
      (σ : Variable Θ .set → Term ℒ [] Ε .set) (G : List (Entry Ε)),
      (χ σ G).satisfies ζ → (ψ σ G).satisfies ζ)
    (F : List (Formula ℒ [] (.set :: .set :: Δ))) :
    ∀ (T : List (Variable Δ .set)) {Ε : SortContext ℒ} (ζ : Env 𝒩 [] Ε)
      (B W R : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
      (G : List (Entry Ε)) (σ : Variable Θ .set → Term ℒ [] Ε .set),
      (extension_m χ F T B W R τ G σ).satisfies ζ →
        (extension_m ψ F T B W R τ G σ).satisfies ζ := by
  induction F with
  | nil =>
    intro T Ε ζ B W R τ G σ h₀
    exact ⟨h₀.1, h ζ σ G h₀.2⟩
  | cons φ F ih =>
    intro T Ε ζ B W R τ G σ h₀
    cases T with
    | nil => exact h₀.elim
    | cons v T =>
      rw [extension_m, Formula.satisfies_existsFreeTop] at h₀ ⊢
      obtain ⟨j, hj, h₀⟩ := h₀
      exact ⟨j, hj, ih T (ζ.pushFree j) (free B) (free W) (free R)
        (fun w => free (τ w))
        ((free (τ v), .fvar .here) :: G.map (fun p => (free p.1, free p.2)))
        (fun w => free (σ w)) h₀⟩

/-- 传输末端时保留原环境读数；末端假设无需对无关的参数解释成立。 -/
theorem imp_read_l {Θ Δ : SortContext ℒ} (ν : Env 𝒩 [] Θ)
    (χ ψ : ∀ {Ε : SortContext ℒ}, (Variable Θ .set → Term ℒ [] Ε .set) →
      List (Entry Ε) → Formula ℒ [] Ε)
    (h : ∀ {Ε : SortContext ℒ} (ζ : Env 𝒩 [] Ε)
      (σ : Variable Θ .set → Term ℒ [] Ε .set) (G : List (Entry Ε)),
      (∀ v, (σ v).eval ζ = ν.freeVal v) → (χ σ G).satisfies ζ → (ψ σ G).satisfies ζ)
    (F : List (Formula ℒ [] (.set :: .set :: Δ))) :
    ∀ (T : List (Variable Δ .set)) {Ε : SortContext ℒ} (ζ : Env 𝒩 [] Ε)
      (B W R : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
      (G : List (Entry Ε)) (σ : Variable Θ .set → Term ℒ [] Ε .set),
      (∀ v, (σ v).eval ζ = ν.freeVal v) →
        (extension_m χ F T B W R τ G σ).satisfies ζ →
          (extension_m ψ F T B W R τ G σ).satisfies ζ := by
  induction F with
  | nil =>
    intro T Ε ζ B W R τ G σ hσ h₀
    exact ⟨h₀.1, h ζ σ G hσ h₀.2⟩
  | cons φ F ih =>
    intro T Ε ζ B W R τ G σ hσ h₀
    cases T with
    | nil => exact h₀.elim
    | cons v T =>
      rw [extension_m, Formula.satisfies_existsFreeTop] at h₀ ⊢
      obtain ⟨j, hj, h₀⟩ := h₀
      have hf (t : Term ℒ [] Ε .set) : (free t).eval (ζ.pushFree j) = t.eval ζ := by
        simp only [free, Term.eval_weakenFree]
      exact ⟨j, hj, ih T (ζ.pushFree j) (free B) (free W) (free R)
        (fun w => free (τ w))
        ((free (τ v), .fvar .here) :: G.map (fun p => (free p.1, free p.2)))
        (fun w => free (σ w)) (fun w => (hf (σ w)).trans (hσ w)) h₀⟩

/-- 在原装配参数读数保持的前提下，消费真正存在的末端，而非假设末端存在。 -/
theorem eliminate_l {Θ Δ : SortContext ℒ} (ν : Env 𝒩 [] Θ)
    (χ : ∀ {Ε : SortContext ℒ}, (Variable Θ .set → Term ℒ [] Ε .set) →
      List (Entry Ε) → Formula ℒ [] Ε) (P : Prop)
    (h : ∀ {Ε : SortContext ℒ} (ζ : Env 𝒩 [] Ε)
      (σ : Variable Θ .set → Term ℒ [] Ε .set) (G : List (Entry Ε)),
      (∀ v, (σ v).eval ζ = ν.freeVal v) → (χ σ G).satisfies ζ → P)
    (F : List (Formula ℒ [] (.set :: .set :: Δ))) :
    ∀ (T : List (Variable Δ .set)) {Ε : SortContext ℒ} (ζ : Env 𝒩 [] Ε)
      (B W R : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
      (G : List (Entry Ε)) (σ : Variable Θ .set → Term ℒ [] Ε .set),
      (∀ v, (σ v).eval ζ = ν.freeVal v) →
        (extension_m χ F T B W R τ G σ).satisfies ζ → P := by
  induction F with
  | nil =>
    intro T Ε ζ B W R τ G σ hσ h₀
    exact h ζ σ G hσ h₀.2
  | cons φ F ih =>
    intro T Ε ζ B W R τ G σ hσ h₀
    cases T with
    | nil => exact h₀.elim
    | cons v T =>
      rw [extension_m, Formula.satisfies_existsFreeTop] at h₀
      obtain ⟨j, _, h₀⟩ := h₀
      have hf (t : Term ℒ [] Ε .set) : (free t).eval (ζ.pushFree j) = t.eval ζ := by
        simp only [free, Term.eval_weakenFree]
      exact ih T (ζ.pushFree j) (free B) (free W) (free R) (fun w => free (τ w))
        ((free (τ v), .fvar .here) :: G.map (fun p => (free p.1, free p.2)))
        (fun w => free (σ w)) (fun w => (hf (σ w)).trans (hσ w)) h₀

#print axioms imp_l
#print axioms imp_read_l
#print axioms eliminate_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceFamilyTransport
