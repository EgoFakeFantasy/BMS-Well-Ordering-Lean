import BMSConstructibleBridge.PowerlessCoreStageSystem
import BMSConstructibleBridge.PowerlessLevyAgreementAbsolute
import BMSConstructibleBridge.PowerlessStageStability

/-!
# 满足核心公理的实际极限层中原有限层稳定关系的绝对性

原 stable_m 的六个系统见证由实际成员性取回；分类证书及全部赋值图
也由已证明的闭包取得。核心是显式前提；结论不替代 BM4 的复杂度重编号和有限反射。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCoreStageStability

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {U δ : carrier_l ℳ}
  {hU₀ : ∃ x, member_l ℳ x U} (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val)
  (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
  (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
  (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val δ U)
  (hδ : PowerlessStagePair.limit_l δ)
  (h𝒩 : Theory.Models (structure_l U hU₀) PowerlessTheory.theory_m)
  (hωδ : member_l ℳ ω.val δ)

include hℳ hω ht hT hU hδ h𝒩 hωδ

omit hδ hωδ in
theorem limit_l {α : type_l U} :
    PowerlessStagePair.limit_l (ℳ := structure_l U hU₀) α ↔ PowerlessStagePair.limit_l α.val := by
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  apply and_congr (PowerlessCoreStageHierarchy.ordinal_l hℳ hUT h𝒩 α)
  constructor
  · rintro ⟨⟨x, hx⟩, h⟩
    refine ⟨⟨x.val, hx⟩, ?_⟩
    intro x hx
    obtain ⟨y, hy, hxy⟩ := h ⟨x, hUT α.val x α.property hx⟩ hx
    exact ⟨y.val, hy, hxy⟩
  · rintro ⟨⟨x, hx⟩, h⟩
    refine ⟨⟨⟨x, hUT α.val x α.property hx⟩, hx⟩, ?_⟩
    intro x hx
    obtain ⟨y, hy, hxy⟩ := h x.val hx
    exact ⟨⟨y, hUT α.val y α.property hy⟩, hy, hxy⟩

omit hδ hωδ in
theorem proper_l {α β : type_l U} :
    PowerlessStagePair.proper_l (ℳ := structure_l U hU₀) ω α β ↔
      PowerlessStagePair.proper_l ω.val α.val β.val :=
  and_congr Iff.rfl (and_congr Iff.rfl (and_congr (limit_l hℳ hω ht hT hU h𝒩) (limit_l hℳ hω ht hT hU h𝒩)))

omit h𝒩 in
theorem agreement_l {A F G n : type_l U} :
    PowerlessLevyAgreement.agreement_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ A F G n ↔
      PowerlessLevyAgreement.agreement_l ω.val e.val T.val t₁.val t₂.val t₃.val A.val F.val G.val n.val := by
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  have hωδ₀ : subset_l ω.val δ := fun x hx => PowerlessOrdinal.transitive_l hδ.1 ω.val x hωδ hx
  apply PowerlessLevyAgreementAbsolute.agreement_l hℳ hUT hω ht.1 hT
  · exact fun x hx F hF => PowerlessStageAdditionIteration.limit_l hℳ hω ht hT hU hωδ hδ hx hF
  · exact PowerlessStageFiniteSubsets.finite_l hℳ hω ht hT hU hδ hωδ₀
  · intro m hm f hf
    apply PowerlessStageFiniteGraphs.finite_l hℳ hω ht hT hU hδ hωδ₀ m hm f
    exact PowerlessFunction.range_l hℳ hf
      (fun _ y hy => hUT A.val y A.property (PowerlessFunction.value_mem_l hℳ hf hy).2)

theorem stable_l {n α β : type_l U} :
    PowerlessStageStability.stable_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ n α β ↔
      PowerlessStageStability.stable_l ω.val e.val T.val t₁.val t₂.val t₃.val n.val α.val β.val := by
  constructor
  · rintro ⟨hn, hp, A, B, S, R, F, G, hA, hB, h⟩
    exact ⟨hn, (proper_l hℳ hω ht hT hU h𝒩).mp hp, A.val, B.val, S.val, R.val, F.val, G.val,
      (PowerlessCoreStageSystem.system_l hℳ hω ht hT hU hδ h𝒩 hωδ).mp hA,
      (PowerlessCoreStageSystem.system_l hℳ hω ht hT hU hδ h𝒩 hωδ).mp hB,
      (agreement_l hℳ hω ht hT hU hδ hωδ).mp h⟩
  · rintro ⟨hn, hp, A, B, S, R, F, G, hA, hB, h⟩
    have hαδ := (PowerlessStageOrdinal.member_l hℳ hω ht hT hU hp.2.2.1.1).mp α.property
    have hβδ := (PowerlessStageOrdinal.member_l hℳ hω ht hT hU hp.2.2.2.1).mp β.property
    obtain ⟨hAU, hSU, hFU⟩ := PowerlessCoreStageSystem.member_l hℳ hω ht hT hU hδ h𝒩 hωδ hαδ hA
    obtain ⟨hBU, hRU, hGU⟩ := PowerlessCoreStageSystem.member_l hℳ hω ht hT hU hδ h𝒩 hωδ hβδ hB
    exact ⟨hn, (proper_l hℳ hω ht hT hU h𝒩).mpr hp,
      ⟨A, hAU⟩, ⟨B, hBU⟩, ⟨S, hSU⟩, ⟨R, hRU⟩, ⟨F, hFU⟩, ⟨G, hGU⟩,
      (PowerlessCoreStageSystem.system_l hℳ hω ht hT hU hδ h𝒩 hωδ).mpr hA,
      (PowerlessCoreStageSystem.system_l hℳ hω ht hT hU hδ h𝒩 hωδ).mpr hB,
      (agreement_l hℳ hω ht hT hU hδ hωδ).mpr h⟩

theorem source_l
    {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (w z V s₁ s₂ s₃ n α β : Term ℒ Γ Δ .set)
    (hw : (w.eval η).val = ω.val) (hz : (z.eval η).val = e.val) (hV : (V.eval η).val = T.val)
    (hs₁ : (s₁.eval η).val = t₁.val) (hs₂ : (s₂.eval η).val = t₂.val) (hs₃ : (s₃.eval η).val = t₃.val) :
    (PowerlessStageStability.stable_m w z V s₁ s₂ s₃ n α β).satisfies η ↔
      PowerlessStageStability.stable_l ω.val e.val T.val t₁.val t₂.val t₃.val
        (n.eval η).val (α.eval η).val (β.eval η).val := by
  have h := PowerlessStageStability.stable_formula_l h𝒩
    η w z V s₁ s₂ s₃ n α β
  rw [show w.eval η = ω from Subtype.ext hw, show z.eval η = e from Subtype.ext hz,
    show V.eval η = T from Subtype.ext hV, show s₁.eval η = t₁ from Subtype.ext hs₁,
    show s₂.eval η = t₂ from Subtype.ext hs₂, show s₃.eval η = t₃ from Subtype.ext hs₃] at h
  exact h.trans (stable_l (hU₀ := hU₀) hℳ hω ht hT hU hδ h𝒩 hωδ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCoreStageStability
