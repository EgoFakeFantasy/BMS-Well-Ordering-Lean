import BMSConstructibleBridge.PowerlessRelabelTemplate
import BMSConstructibleBridge.PowerlessRelabelPreservation
import BMSConstructibleBridge.PowerlessGoodBoundary
import BMSConstructibleBridge.PowerlessRelabelReflection
import BMSConstructibleBridge.PowerlessStageTriangular

/-!
# 内部有限标签图的实际重标号存在性

由原标签构造精确关系记录，把记录及低处参数装入同一个下层环境，再反射整个
存在式并解出共同的新标签图。调用者不需提供环境、语法记录或矩阵的可满足性。
有限公式预算及好标签类的支持上界仍显式保留；这里的背景仍为 PowerlessTheory。
具名边和顶端迹采用独立列表：只有顶端迹需要低于当前反射层号，具名边可更高。
实际预算只依赖具名边记录数和顶端迹层号，不依赖具名边层号的数值。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelabel

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

/-- 在同一好标签类的稳定对下，把原高处图重标号到低处，并保留指定的所有关系。
外部列表仅指定要保留的层号，列数 p,q 始终是模型内部自然数。 -/
theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ c N n α β A B S R F G p q f g : carrier_l ℳ}
    (hω : omega_l ω) (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (hA : PowerlessStageEvaluation.system_l ω e T t₁ t₂ t₃ α A S F)
    (hB : PowerlessStageEvaluation.system_l ω e T t₁ t₂ t₃ β B R G)
    {k l : Nat} (hc : PowerlessGoodBoundary.code_l ω e T t₁ t₂ t₃ c N l)
    (hc₀ : member_l ℳ c ω) (hN : member_l ℳ N ω) (hkl : k ≤ l)
    (hn : PowerlessNumeral.numeral_l e k n)
    (hs : PowerlessGoodBoundary.stable_l ω e T t₁ t₂ t₃ c N n α β)
    (hp : member_l ℳ p ω) (hq : member_l ℳ q ω)
    (hf : map_l f p A) (hg : map_l g q B)
    (hG : ∀ i a, value_l g i a → PowerlessCodedDiagram.good_l ω e T t₁ t₂ t₃ c N a)
    (hfg : ∀ i j a b, value_l f i a → value_l g j b → member_l ℳ a b)
    (Λ : List (Nat × carrier_l ℳ))
    (hΛ : ∀ t ∈ Λ, PowerlessNumeral.numeral_l e t.1 t.2)
    (Θ : List (Nat × carrier_l ℳ))
    (hΘ : ∀ t ∈ Θ, t.1 ≤ k ∧ PowerlessNumeral.numeral_l e t.1 t.2)
    (hφ : PowerlessRelabelTemplate.budget_m Λ.length (Θ.map Prod.fst) ≤ k) :
    ∃ h, map_l h q A ∧
      PowerlessRelabelPreservation.image_l ω e T t₁ t₂ t₃ c N α β f g h Λ Θ := by
  have hα := hs.1.2.1
  have hωα := hs.1.1
  have hω₀ : subset_l ω α := fun x hx => PowerlessOrdinal.transitive_l hα.1 ω x hωα hx
  obtain ⟨hωA, heA, hTA, h₁A, h₂A, h₃A⟩ :=
    PowerlessStageTriangular.parameters_l hℳ hω ht hT hA.1 hωα hα
  have hnat := PowerlessStageParameters.naturals_l hℳ hω ht hT hA.1 hω₀
  have hA₀ : ∃ x, member_l ℳ x A := ⟨ω, hωA⟩
  have hAB := PowerlessStageStructure.subset_l hℳ hω hA.1 hB.1 hs.2.2.2.1.2.1
  have hB₀ : ∃ x, member_l ℳ x B := ⟨ω, hAB ω hωA⟩
  have hfA := (PowerlessStageFiniteMapping.member_l hℳ hω ht hT hA.1 hα hω₀ hp hf).1
  obtain ⟨D, E, Ξ, hDA, hEA, hΞ₀, hD, hE, hΞ, _⟩ :=
    PowerlessRelabelWitness.exists_l hℳ hω ht hT hA.1 hα hω₀ hp hq c N β f g B hg hG Λ
  obtain ⟨Ω, hΩ₀, hΩ⟩ :=
    PowerlessRelabelWitness.family_exists_l hℳ hω ht hT hA.1 hα hω₀ hp hq β f g Θ
  have hΩ₁ := PowerlessRelabelWitness.trace_bounds_l hΩ₀ hΘ hΩ
  have hΞ₁ (r : PowerlessRelabelWitness.entry_l ℳ) (hr : r ∈ Ξ) : member_l ℳ r.n ω := by
    have h : (r.k, r.n) ∈ Λ := hΞ₀ ▸ List.mem_map.mpr ⟨r, hr, rfl⟩
    exact PowerlessNumeral.natural_l hℳ hω ht.1 (hΛ _ h)
  -- 具名边只装入数码与两张边图，不要求该层号具有顶端迹。
  let ξ (r : {s : PowerlessRelabelWitness.entry_l ℳ // s ∈ Ξ}) :
      PowerlessRelabelTemplate.edge_l (structure_l A hA₀) :=
    ⟨⟨r.val.n, hnat _ (hΞ₁ r.val r.property)⟩,
      ⟨r.val.D, (hΞ r.val r.property).1⟩,
      ⟨r.val.E, (hΞ r.val r.property).2.1⟩⟩
  let τ (r : {s : PowerlessRelabelWitness.entry_l ℳ // s ∈ Ω}) :
      PowerlessRelabelWitness.entry_l (structure_l A hA₀) :=
    ⟨r.val.k,
      ⟨r.val.n, hnat _ (PowerlessNumeral.natural_l hℳ hω ht.1 (hΩ₁ r.val r.property).2.1)⟩,
      ⟨r.val.D, (hΩ r.val r.property).1⟩,
      ⟨r.val.E, (hΩ r.val r.property).2.1⟩,
      ⟨r.val.S, (hΩ r.val r.property).2.2.1⟩⟩
  let Ξ₁ := Ξ.attach.map ξ
  let Ω₁ := Ω.attach.map τ
  let a : Fin 12 → type_l A :=
    Fin.cases ⟨ω, hωA⟩ (Fin.cases ⟨e, heA⟩ (Fin.cases ⟨T, hTA⟩
      (Fin.cases ⟨t₁, h₁A⟩ (Fin.cases ⟨t₂, h₂A⟩ (Fin.cases ⟨t₃, h₃A⟩
        (Fin.cases ⟨c, hnat c hc₀⟩ (Fin.cases ⟨N, hnat N hN⟩
          (Fin.cases ⟨q, hnat q hq⟩ (Fin.cases ⟨f, hfA⟩
            (Fin.cases ⟨D, hDA⟩ (Fin.cases ⟨E, hEA⟩ Fin.elim0)))))))))))
  let Φ := PowerlessRelabelTemplate.syntax_m Ξ₁.length (Ω₁.map (fun r => r.k))
  let s := Φ.parameter_m
  let η : Env (structure_l A hA₀) []
      (PowerlessRelabelTemplate.context_m Ξ₁.length
        (Ω₁.map (fun r : PowerlessRelabelWitness.entry_l (structure_l A hA₀) => r.k)).length) :=
    PowerlessRelabelTemplate.env_l a Ω₁ Ξ₁
  obtain ⟨hP, hΨ₁, hΘ₁⟩ := PowerlessRelabelTemplate.source_l a Ω₁ Ξ₁
  have h₀ (i : Fin 12) : ((s i).eval η).val = (a i).val :=
    congrArg Subtype.val (hP i)
  have hK : Ω₁.map (fun r => r.k) = Θ.map Prod.fst := by
    have h := congrArg (List.map Prod.fst) hΩ₀
    simpa only [Ω₁, τ, PowerlessRelabelWitness.levels_l, List.map_map,
      Function.comp_def, List.attach_map_val] using h
  have hd : Ξ₁.length = Λ.length := by
    have h := congrArg List.length hΞ₀
    simpa only [Ξ₁, PowerlessRelabelWitness.levels_l, List.length_map, List.length_attach] using h
  have hΨ : Φ.edges_m.map (fun t => ((t.1.eval η).val, (t.2.1.eval η).val,
      (t.2.2.eval η).val)) = PowerlessRelabelWitness.edges_l Ξ := by
    have h := congrArg (List.map (fun t : type_l A × type_l A × type_l A =>
      (t.1.val, t.2.1.val, t.2.2.val))) hΨ₁
    simp only [List.map_map, Function.comp_def] at h
    change Φ.edges_m.map (fun t => ((t.1.eval η).val, (t.2.1.eval η).val,
      (t.2.2.eval η).val)) = Ξ₁.map (fun r => (r.n.val, r.D.val, r.E.val)) at h
    refine h.trans ?_
    change (Ξ.attach.map ξ).map (fun r => (r.n.val, r.D.val, r.E.val)) =
      Ξ.map (fun r => (r.n, r.D, r.E))
    rw [List.map_map]
    exact List.attach_map_val (l := Ξ) (f := fun r => (r.n, r.D, r.E))
  have hΘ : Φ.traces_m.map (fun t => (t.1, (t.2.1.eval η).val, (t.2.2.eval η).val)) =
      Ω.map (fun r => (r.k, r.n, r.S)) := by
    have h := congrArg (List.map (fun t : Nat × type_l A × type_l A =>
      (t.1, t.2.1.val, t.2.2.val))) hΘ₁
    simp only [List.map_map, Function.comp_def] at h
    change Φ.traces_m.map (fun t => (t.1, (t.2.1.eval η).val, (t.2.2.eval η).val)) =
      Ω₁.map (fun r => (r.k, r.n.val, r.S.val)) at h
    refine h.trans ?_
    change (Ω.attach.map τ).map (fun r => (r.k, r.n.val, r.S.val)) =
      Ω.map (fun r => (r.k, r.n, r.S))
    rw [List.map_map]
    exact List.attach_map_val (l := Ω) (f := fun r => (r.k, r.n, r.S))
  have hΘ₂ : Φ.traces_m.map (fun t => ((t.2.1.eval η).val, (t.2.2.eval η).val)) =
      PowerlessRelabelWitness.traces_l Ω := by
    have h := congrArg (List.map Prod.snd) hΘ
    simpa only [PowerlessRelabelWitness.traces_l, List.map_map, Function.comp_def] using h
  have hΘ₃ : ∀ t ∈ Φ.traces_m, t.1 ≤ k ∧
      PowerlessNumeral.numeral_l e t.1 (t.2.1.eval η).val ∧ subset_l (t.2.2.eval η).val q := by
    intro t ht
    have h : (t.1, (t.2.1.eval η).val, (t.2.2.eval η).val) ∈
        Ω.map (fun r => (r.k, r.n, r.S)) := by
      rw [← hΘ]
      exact List.mem_map.mpr ⟨t, ht, rfl⟩
    obtain ⟨r, hr, heq⟩ := List.mem_map.mp h
    have h := congrArg (fun z : Nat × carrier_l ℳ × carrier_l ℳ =>
      z.1 ≤ k ∧ PowerlessNumeral.numeral_l e z.1 z.2.1 ∧ subset_l z.2.2 q) heq
    exact h.mp (hΩ₁ r hr)
  have hb : PowerlessSourceStandardBudget.budget_m
      (PowerlessRelabelMatrix.formula_m (s 0) (s 1) (s 2) (s 3) (s 4) (s 5)
        (s 6) (s 7) (s 8) (s 9) (s 10) (s 11) Φ.edges_m Φ.traces_m) ≤ k := by
    change PowerlessRelabelTemplate.budget_m Ξ₁.length (Ω₁.map (fun r => r.k)) ≤ k
    rw [hd, hK]
    exact hφ
  -- 上层原图实现整套矩阵，反射得到的是同时实现各项的新图。
  have h := PowerlessRelabelReflection.transfer_l
    (hA₀ := hA₀) (hB₀ := hB₀)
    (ω := ⟨ω, hωA⟩) (e := ⟨e, heA⟩) (T := ⟨T, hTA⟩)
    (t₁ := ⟨t₁, h₁A⟩) (t₂ := ⟨t₂, h₂A⟩) (t₃ := ⟨t₃, h₃A⟩)
    hℳ hω ht hT hA hB k n hn hs.2.2
    (PowerlessGoodBoundary.models_l hc hkl hs.1 hA₀ hA)
    (PowerlessGoodBoundary.models_l hc hkl hs.2.1 hB₀ hB)
    η (s 0) (s 1) (s 2) (s 3) (s 4) (s 5) (s 6) (s 7) (s 8) (s 9) (s 10) (s 11)
    Φ.edges_m Φ.traces_m hb (h₀ 0) (h₀ 1) (h₀ 2) (h₀ 3) (h₀ 4) (h₀ 5)
    (by simp only [h₀ 7]; exact hN) (by simp only [h₀ 8]; exact hq)
    (by simp only [h₀ 8]; exact hΘ₃)
  simp only [h₀ 6, h₀ 7, h₀ 8, h₀ 9, h₀ 10, h₀ 11, hΨ, hΘ₂] at h
  have hW := PowerlessRelabelWitness.realizes_l hℳ hg hG hD hE Ξ Ω hΞ hΩ
  obtain ⟨h, hh, hC⟩ := h.mp ⟨g, hg, hW⟩
  exact ⟨h, hh, PowerlessRelabelPreservation.extract_l hℳ hω ht hT hA.1
    hf hg hh hfg hD hE Ξ Ω Λ Θ hΞ₀ hΩ₀ hΞ hΩ hC⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelabel
