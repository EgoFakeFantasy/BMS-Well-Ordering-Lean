import BMSConstructibleBridge.PowerlessRelativeSourceFamilyExtension

/-! # 保留原图规格的有限族末端扩展

对象语言为纯隶属 ℒ，背景为原 Z₂；目标仍是原 extension_m 的同一对象公式。
本模块补充其语义装配接口，供原 GraphTranslation／Derives 出口继续消费。
沿 assemble_m 已绑定的同一存在见证递归，不再次选择图，也不改动原 AST。
H 与当前图列表 G 逐项保存原矩阵规格；末端顺序为 F.reverse ++ H。
自由槽提升只改变装配上下文，原矩阵参数 Δ 始终不变。
固定原参数环境 ν 的逐项读数随 τ 提升保持，不把它增加为对象前提。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceFamilyGraphExtension

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeSourceFamilyExtension (extension_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev Entry (Ε : SortContext ℒ) := Term ℒ [] Ε .set × Term ℒ [] Ε .set
private abbrev free {Ε : SortContext ℒ} (t : Term ℒ [] Ε .set) :=
  t.weakenFree SetTheory.SetSort.set

/-- 新自由槽不改变已有原图规格的真值。 -/
private theorem free_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ζ : Env 𝒩 [] Ε) (B W R J : Term ℒ [] Ε .set)
    (τ : Variable Δ .set → Term ℒ [] Ε .set) (j : 𝒩.Carrier .set) :
    (PowerlessRelativeSourceSkolemGraph.graph_m φ (free B) (free W) (free R)
      (free J) (fun v => free (τ v))).satisfies (ζ.pushFree j) ↔
      (PowerlessRelativeSourceSkolemGraph.graph_m φ B W R J τ).satisfies ζ := by
  let η : Env 𝒩 [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with | .set => (τ v).eval ζ }
  have hf (t : Term ℒ [] Ε .set) : (free t).eval (ζ.pushFree j) = t.eval ζ := by
    simp only [free, Term.eval_weakenFree]
  have h₀ := PowerlessRelativeSourceSkolemGraph.graph_formula_l φ ζ B W R J τ η
    (fun _ => rfl)
  have h₁ := PowerlessRelativeSourceSkolemGraph.graph_formula_l φ (ζ.pushFree j)
    (free B) (free W) (free R) (free J) (fun v => free (τ v)) η (fun v => hf (τ v))
  have h₂ : (PowerlessRelativeSourceSkolemGraph.graph_m φ (free B) (free W) (free R)
      (free J) (fun v => free (τ v))).satisfies (ζ.pushFree j) ↔
      (PowerlessRelativeSourceSkolemGraph.payload_m φ).satisfies
        ((((η.pushFree (B.eval ζ)).pushFree (R.eval ζ)).pushFree (W.eval ζ)).pushFree
          (J.eval ζ)) := by
    simpa only [hf] using h₁
  exact h₂.trans h₀.symm

/-- 逐项提升原图及其规格，不改变与原矩阵列表的对应。 -/
private theorem lift_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Ε Δ : SortContext ℒ} (ζ : Env 𝒩 [] Ε) (B W R : Term ℒ [] Ε .set)
    (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (H : List (Formula ℒ [] (.set :: .set :: Δ))) (G : List (Entry Ε))
    (j : 𝒩.Carrier .set)
    (h : List.Forall₂ (fun φ p =>
      (PowerlessRelativeSourceSkolemGraph.graph_m φ B W R p.2 τ).satisfies ζ) H G) :
    List.Forall₂ (fun φ p =>
      (PowerlessRelativeSourceSkolemGraph.graph_m φ (free B) (free W) (free R) p.2
        (fun v => free (τ v))).satisfies (ζ.pushFree j)) H
      (G.map (fun p => (free p.1, free p.2))) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons φ p H G hφ hG ih =>
    exact List.Forall₂.cons ((free_l φ ζ B W R p.2 τ j).mpr hφ) ih

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 末端回调同时消费原矩阵图规格及既有标签算子的完整性质。 -/
theorem extension_l (K : source_coding_l hℳ) {Θ Δ : SortContext ℒ}
    (η : Env 𝒱 [] Θ) (ν : Env 𝒱 [] Δ) (b w c : SecondOrderQuotient.type_l hℳ)
    (χ : ∀ {Ε : SortContext ℒ}, (Variable Θ .set → Term ℒ [] Ε .set) →
      List (Entry Ε) → Formula ℒ [] Ε)
    (F : List (Formula ℒ [] (.set :: .set :: Δ))) :
    ∀ (H : List (Formula ℒ [] (.set :: .set :: Δ)))
      (_ : ∀ {Ε : SortContext ℒ} (ζ : Env 𝒱 [] Ε)
        (B W R : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
        (G : List (Entry Ε)) (σ : Variable Θ .set → Term ℒ [] Ε .set),
        (∀ v, (σ v).eval ζ = η.freeVal v) →
        (∀ v, (τ v).eval ζ = ν.freeVal v) →
        B.eval ζ = b → W.eval ζ = w →
        (∀ s (v : Variable Ε s), PowerlessRelativeClassCorrespondence.member_l hℳ
          (B.eval ζ) (ζ.freeVal v)) →
        (∀ p ∈ G, mem_l hℳ (p.1.eval ζ) c) →
        List.Forall₂ (fun φ p =>
          (PowerlessRelativeSourceSkolemGraph.graph_m φ B W R p.2 τ).satisfies ζ)
          (F.reverse ++ H) G →
        (PowerlessRelativeSourceSkolemFamily.result_m B W G).satisfies ζ →
          (χ σ G).satisfies ζ),
    ∀ (T : List (Variable Δ .set)) {Ε : SortContext ℒ} (ζ : Env 𝒱 [] Ε)
      (B W R : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
      (G : List (Entry Ε)) (σ : Variable Θ .set → Term ℒ [] Ε .set),
      (∀ v, (σ v).eval ζ = η.freeVal v) →
      (∀ v, (τ v).eval ζ = ν.freeVal v) →
      B.eval ζ = b → W.eval ζ = w →
      (∀ s (v : Variable Ε s), PowerlessRelativeClassCorrespondence.member_l hℳ
        (B.eval ζ) (ζ.freeVal v)) →
      (∀ v ∈ T, mem_l hℳ ((τ v).eval ζ) c) →
      (∀ p ∈ G, mem_l hℳ (p.1.eval ζ) c) →
      List.Forall₂ (fun φ p =>
        (PowerlessRelativeSourceSkolemGraph.graph_m φ B W R p.2 τ).satisfies ζ) H G →
      (PowerlessRelativeSourceSkolemFamily.assemble_m F T B W R τ G).satisfies ζ →
      (extension_m χ F T B W R τ G σ).satisfies ζ := by
  induction F with
  | nil =>
    intro H hχ T Ε ζ B W R τ G σ hσ hτ hB hW hClass _ hTags hH h
    exact ⟨h, hχ ζ B W R τ G σ hσ hτ hB hW hClass hTags hH h⟩
  | cons φ F ih =>
    intro H hχ T Ε ζ B W R τ G σ hσ hτ hB hW hClass hT hTags hH h
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
        (free B) (free W) (free R) J (fun v => free (τ v)) hGraph
      have hClass' : ∀ s (v : Variable (.set :: Ε) s),
          PowerlessRelativeClassCorrespondence.member_l hℳ ((free B).eval ξ) (ξ.freeVal v) := by
        intro s v; cases s
        cases v with
        | here => exact hj
        | there v => simpa only [hf, ξ, Env.pushFree_there] using hClass _ v
      have hTags' : ∀ p ∈ G', mem_l hℳ (p.1.eval ξ) c := by
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · simpa only [hf] using hT v (by simp)
        · obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.mp hp
          simpa only [hf] using hTags p₀ hp₀
      have hH' : List.Forall₂ (fun ψ p =>
          (PowerlessRelativeSourceSkolemGraph.graph_m ψ (free B) (free W) (free R) p.2
            (fun v => free (τ v))).satisfies ξ) (φ :: H) G' :=
        List.Forall₂.cons hGraph (lift_l ζ B W R τ H G j hH)
      have hχ' : ∀ {Ε₁ : SortContext ℒ} (ζ₁ : Env 𝒱 [] Ε₁)
          (B₁ W₁ R₁ : Term ℒ [] Ε₁ .set) (τ₁ : Variable Δ .set → Term ℒ [] Ε₁ .set)
          (G₁ : List (Entry Ε₁)) (σ₁ : Variable Θ .set → Term ℒ [] Ε₁ .set),
          (∀ v, (σ₁ v).eval ζ₁ = η.freeVal v) →
          (∀ v, (τ₁ v).eval ζ₁ = ν.freeVal v) →
          B₁.eval ζ₁ = b → W₁.eval ζ₁ = w →
          (∀ s (v : Variable Ε₁ s), PowerlessRelativeClassCorrespondence.member_l hℳ
            (B₁.eval ζ₁) (ζ₁.freeVal v)) →
          (∀ p ∈ G₁, mem_l hℳ (p.1.eval ζ₁) c) →
          List.Forall₂ (fun ψ p =>
            (PowerlessRelativeSourceSkolemGraph.graph_m ψ B₁ W₁ R₁ p.2 τ₁).satisfies ζ₁)
            (F.reverse ++ (φ :: H)) G₁ →
          (PowerlessRelativeSourceSkolemFamily.result_m B₁ W₁ G₁).satisfies ζ₁ →
            (χ σ₁ G₁).satisfies ζ₁ := by
        intro Ε₁ ζ₁ B₁ W₁ R₁ τ₁ G₁ σ₁ hσ₁ hτ₁ hB₁ hW₁ hClass₁ hTags₁ hH₁ h₁
        apply hχ ζ₁ B₁ W₁ R₁ τ₁ G₁ σ₁ hσ₁ hτ₁ hB₁ hW₁ hClass₁ hTags₁ _ h₁
        simpa only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
          using hH₁
      rw [extension_m, Formula.satisfies_existsFreeTop]
      refine ⟨j, hGraph, ?_⟩
      exact ih (φ :: H) hχ' T ξ (free B) (free W) (free R) (fun v => free (τ v)) G'
        (fun v => free (σ v)) (fun v => (hf (σ v)).trans (hσ v))
        (fun v => (hf (τ v)).trans (hτ v))
        ((hf B).trans hB) ((hf W).trans hW) hClass'
        (fun u hu => by simpa only [hf] using hT u (by simp [hu])) hTags' hH' h

#print axioms extension_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceFamilyGraphExtension
