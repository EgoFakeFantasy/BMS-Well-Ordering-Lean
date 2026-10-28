import BMSConstructibleBridge.PowerlessRelativeLimitParameterBounds
import BMSConstructibleBridge.SecondOrderMemberBounded

/-! # 指定非零极限层中的实际 Δ₀ 分离

在严格先前的共同传递层中核验有限参数及有界公式，精确切片落入其后继
Def；该后继仍严格低于指定极限。成员规格量化全部原商对象，而非仅类域。
这里只给出语义辅助接口；正式对象模式另行回传，不宣称 BMS 终局完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitDeltaSeparation

open Logic FirstOrder StabilityFrame
open SecondOrderQuotient (type_l mk_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SecondOrderMemberStructure.structure_l

universe u

private def slice_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) : Formula ℒ [.set] (.set :: Δ) :=
  .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (.fvar .here))
    (φ.abstractFreeTop.weakenFree SetTheory.SetSort.set)

private theorem slice_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) (η : Env 𝒩 [] Δ) (X x : 𝒩.Carrier .set) :
    (slice_m φ).satisfies ((η.pushFree X).pushBound x) ↔
      𝒩.relInterp .membership (.cons x (.cons X .nil)) ∧ φ.satisfies (η.pushFree x) := by
  change 𝒩.relInterp .membership (.cons x (.cons X .nil)) ∧
    (φ.abstractFreeTop.weakenFree SetTheory.SetSort.set).satisfies ((η.pushBound x).pushFree X) ↔ _
  rw [Formula.satisfies_weakenFree, Formula.satisfies_abstractFreeTop]

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B β C : type_l hℳ}

theorem exists_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ)
    {X : type_l hℳ} (hX : mem_l hℳ X C)
    (hParams : ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v) C) :
    ∃ Y, mem_l hℳ Y C ∧ ∀ x, mem_l hℳ x Y ↔ mem_l hℳ x X ∧ φ.satisfies (η.pushFree x) := by
  obtain ⟨a, c, ha, hc, hXc, hBound⟩ :=
    PowerlessRelativeLimitParameterBounds.exists_l hBase hLimit hC η hX hParams
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hc
  obtain ⟨b, d, hb, hd, hDef⟩ := PowerlessRelativeLimitClosure.def_bound_l hℳ hBase hLimit hC ha hc
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ c
  obtain ⟨k, hk, _⟩ := SecondOrderMemberDefProperties.member_root_l hℳ A hXc
  let ξ : Env (SecondOrderMemberStructure.structure_l hℳ A k hk) [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun v => ⟨η.freeVal v, hBound _ v⟩ }
  obtain ⟨z, hz, hRead⟩ := SecondOrderMemberDefProperties.coverage_l hℳ A k hk hDef
    (ξ.pushFree (sort := SetTheory.SetSort.set) ⟨X, hXc⟩) (slice_m φ)
  have hRead' n (hn : SecondOrderPairing.relation_l A.real n A.root) :
      mem_l hℳ (mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn)) z ↔
        mem_l hℳ (mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn)) X ∧
          φ.satisfies (η.pushFree (sort := SetTheory.SetSort.set)
            (mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn))) := by
    have hValue : (SecondOrderMemberStructure.value_l hℳ A k hk n).val =
        mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn) := by
      change mk_l hℳ (SecondOrderMemberNormalizer.code_l hℳ A k hk n) = _
      rw [SecondOrderMemberNormalizer.code_fixed_l hℳ A k hk n hn]
    have hEnv : SecondOrderMemberBounded.env_l
        (ξ.pushFree (sort := SetTheory.SetSort.set) (SecondOrderMemberStructure.value_l hℳ A k hk n)) =
          η.pushFree (sort := SetTheory.SetSort.set) (mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn)) := by
      apply Env.ext
      · intro _ v; nomatch v
      · intro s v
        cases s
        cases v with
        | here => exact hValue
        | there v => rfl
    have hSource := SecondOrderMemberBounded.formula_l hTrans hφ
      (ξ.pushFree (sort := SetTheory.SetSort.set) (SecondOrderMemberStructure.value_l hℳ A k hk n))
    rw [hEnv] at hSource
    have h' := (hRead n hn).trans
      (slice_formula_l φ ξ ⟨X, hXc⟩ (SecondOrderMemberStructure.value_l hℳ A k hk n))
    change mem_l hℳ (mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn)) z ↔
      mem_l hℳ (SecondOrderMemberStructure.value_l hℳ A k hk n).val X ∧
        φ.satisfies (ξ.pushFree (SecondOrderMemberStructure.value_l hℳ A k hk n)) at h'
    rw [hValue] at h'
    exact h'.trans (and_congr Iff.rfl hSource)
  refine ⟨z, (PowerlessRelativeLimitClosure.value_l hℳ hBase hLimit hC z).mpr ⟨b, d, hb, hd, hz⟩, ?_⟩
  intro x
  constructor
  · intro hxz
    obtain ⟨n, hn, hxn⟩ := SecondOrderMemberDefProperties.member_root_l hℳ A
      (SecondOrderMemberDefProperties.subset_l hℳ hDef hz x hxz)
    rw [hxn] at hxz ⊢
    exact (hRead' n hn).mp hxz
  · rintro ⟨hxX, hφx⟩
    obtain ⟨n, hn, hxn⟩ := SecondOrderMemberDefProperties.member_root_l hℳ A (hTrans X hXc x hxX)
    rw [hxn] at hxX hφx ⊢
    exact (hRead' n hn).mpr ⟨hxX, hφx⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitDeltaSeparation
