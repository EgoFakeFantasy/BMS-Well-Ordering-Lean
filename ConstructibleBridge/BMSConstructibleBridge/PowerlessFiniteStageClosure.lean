import BMSConstructibleBridge.PowerlessSliceFiniteSupport
import BMSConstructibleBridge.PowerlessHistoryFiniteSupport
import BMSConstructibleBridge.PowerlessRelationFiniteSupport
import BMSConstructibleBridge.PowerlessRelativizedTheory
import BMSConstructibleBridge.PowerlessEvaluationSliceAbsolute
import BMSConstructibleBridge.PowerlessOrdinalHistoryAbsolute
import BMSConstructibleBridge.PowerlessOrdinalRelationAbsolute

/-!
# 有限核心片段保证切片、任意前史和隶属关系图的域内存在

绝对性按传递域与实际有序对闭包证明，存在见证来自三个固定有限支持。
没有把内部完整核心、图的有限性或外部良基性加入前提。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteStageClosure

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

noncomputable def basis_m : List (Sentence ℒ) :=
  PowerlessSliceFiniteSupport.support_m.sentences ++
    (PowerlessHistoryFiniteSupport.support_m.sentences ++ PowerlessRelationFiniteSupport.support_m.sentences)

def theory_m : Theory ℒ := Theory.ofList basis_m

noncomputable def condition_m {Γ Δ : SortContext ℒ} (A : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  PowerlessRelativizedTheory.instance_m basis_m A

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem core_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) : Theory.Models ℳ theory_m := by
  intro φ hφ
  obtain hφ | hφ := List.mem_append.mp hφ
  · exact hℳ φ (PowerlessSliceFiniteSupport.support_m.subset φ hφ)
  · obtain hφ | hφ := List.mem_append.mp hφ
    · exact hℳ φ (PowerlessHistoryFiniteSupport.support_m.subset φ hφ)
    · exact hℳ φ (PowerlessRelationFiniteSupport.support_m.subset φ hφ)

theorem condition_l {A : carrier_l ℳ} {hA : ∃ x, member_l ℳ x A}
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (a : Term ℒ Γ Δ .set) (h : a.eval η = A) :
    (condition_m a).satisfies η ↔ Theory.Models (structure_l A hA) theory_m :=
  PowerlessRelativizedTheory.instance_l basis_m η a h

variable {U : carrier_l ℳ} {hU₀ : ∃ x, member_l ℳ x U}

theorem history_exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (hUT : PowerlessNaturalOrder.transitive_l U)
    (h𝒩 : Theory.Models (structure_l U hU₀) theory_m) (f a : type_l U) :
    ∃ H : type_l U, PowerlessOrdinalRecursion.history_l H.val f.val a.val := by
  have h₀ : Theory.Models (structure_l U hU₀) PowerlessHistoryFiniteSupport.theory_m :=
    fun φ hφ => h𝒩 φ (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl hφ))))
  obtain ⟨H, hH⟩ := PowerlessHistoryFiniteSupport.exists_l h₀ f a
  exact ⟨H, (PowerlessOrdinalHistoryAbsolute.history_l hℳ hUT).mp hH⟩

theorem history_member_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (hUT : PowerlessNaturalOrder.transitive_l U)
    (h𝒩 : Theory.Models (structure_l U hU₀) theory_m)
    {f a H : carrier_l ℳ} (hf : member_l ℳ f U) (ha : member_l ℳ a U)
    (hH : PowerlessOrdinalRecursion.history_l H f a) : member_l ℳ H U := by
  obtain ⟨K, hK⟩ := history_exists_l hℳ hUT h𝒩 ⟨f, hf⟩ ⟨a, ha⟩
  exact (PowerlessOrdinalHistoryCut.unique_l hℳ hK hH) ▸ K.property

variable (hUT : PowerlessNaturalOrder.transitive_l U)
  (hP : ∀ {a b p : carrier_l ℳ}, member_l ℳ a U → member_l ℳ b U →
    ordered_l a b p → member_l ℳ p U)
  (h𝒩 : Theory.Models (structure_l U hU₀) theory_m)

include hUT hP h𝒩

theorem slice_exists_l (ω A F c f : type_l U) :
    ∃ Y : type_l U, PowerlessEvaluationSlice.slice_l ω.val A.val F.val c.val f.val Y.val := by
  have h₀ : Theory.Models (structure_l U hU₀) PowerlessSliceFiniteSupport.theory_m :=
    fun φ hφ => h𝒩 φ (List.mem_append.mpr (Or.inl hφ))
  obtain ⟨Y, hY⟩ := PowerlessSliceFiniteSupport.exists_l h₀ ω A F c f
  exact ⟨Y, (PowerlessEvaluationSliceAbsolute.slice_l hUT hP).mp hY⟩

theorem slice_member_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω A F c f : type_l U} {Y : carrier_l ℳ}
    (hY : PowerlessEvaluationSlice.slice_l ω.val A.val F.val c.val f.val Y) : member_l ℳ Y U := by
  obtain ⟨Z, hZ⟩ := slice_exists_l hUT hP h𝒩 ω A F c f
  exact (PowerlessEvaluationSlice.unique_l hℳ hZ hY) ▸ Z.property

theorem relation_exists_l (A : type_l U) :
    ∃ R : type_l U, PowerlessOrdinalRelation.relation_l A.val R.val := by
  have h₀ : Theory.Models (structure_l U hU₀) PowerlessRelationFiniteSupport.theory_m :=
    fun φ hφ => h𝒩 φ (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr hφ))))
  obtain ⟨R, hR⟩ := PowerlessRelationFiniteSupport.exists_l h₀ A
  refine ⟨R, (PowerlessOrdinalRelationAbsolute.relation_l hUT ?_).mp hR⟩
  rintro p ⟨x, y, hx, hy, _, hp⟩
  exact hP (hUT A.val x A.property hx) (hUT A.val y A.property hy) hp

theorem relation_member_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {A R : carrier_l ℳ} (hA : member_l ℳ A U)
    (hR : PowerlessOrdinalRelation.relation_l A R) : member_l ℳ R U := by
  obtain ⟨S, hS⟩ := relation_exists_l hUT hP h𝒩 ⟨A, hA⟩
  exact (PowerlessOrdinalRelation.unique_l hℳ hS hR) ▸ S.property

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteStageClosure
