import BMSConstructibleBridge.PowerlessRelativeClassParameterBounds
import BMSConstructibleBridge.SecondOrderMemberBounded

/-! # 实际相对类子模型的 Δ₀ 分离模式

任意外部有限源参数都有共同层界。有界绝对性把类域公式传到该传递层的
成员域，精确切片进入其后继 Def，因而分离见证确实属于类。每个模式实例
都有原 Z₂ 推导；没有把此结果扩张为任意量词分离或 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassDeltaSeparation

open Logic FirstOrder StabilityFrame
open SecondOrderQuotient (mem_l mk_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
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
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem exists_l {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) (η : Env (structure_l hℳ B hBase) [] Δ) (X : type_l hℳ B) :
    ∃ Y : type_l hℳ B, ∀ x : type_l hℳ B,
      mem_l hℳ x.val Y.val ↔ mem_l hℳ x.val X.val ∧ φ.satisfies (η.pushFree x) := by
  obtain ⟨a, c, hc, hXc, hParams⟩ := PowerlessRelativeClassParameterBounds.exists_l η X
  have hCClass := PowerlessRelativeLevelClosure.class_l hℳ hBase hc
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hc
  obtain ⟨b, d, _, hd, hDef⟩ := PowerlessRelativeLevelClosure.successor_exists_l hℳ hBase hc
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ c
  obtain ⟨k, hk, _⟩ := SecondOrderMemberDefProperties.member_root_l hℳ A hXc
  let ξ : Env (SecondOrderMemberStructure.structure_l hℳ A k hk) [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun v => ⟨(η.freeVal v).val, hParams _ v⟩ }
  obtain ⟨z, hz, hRead⟩ := SecondOrderMemberDefProperties.coverage_l hℳ A k hk hDef
    (ξ.pushFree (sort := SetTheory.SetSort.set) ⟨X.val, hXc⟩) (slice_m φ)
  have hChild n (hn : SecondOrderPairing.relation_l A.real n A.root) :
      PowerlessRelativeClassCorrespondence.member_l hℳ B (mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn)) :=
    PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hCClass (SecondOrderGraph.child_mem_l hℳ A n hn)
  have hRead' n (hn : SecondOrderPairing.relation_l A.real n A.root) :
      mem_l hℳ (mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn)) z ↔
        mem_l hℳ (mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn)) X.val ∧
          φ.satisfies (η.pushFree (sort := SetTheory.SetSort.set)
            ⟨mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn), hChild n hn⟩) := by
    have hValue : (SecondOrderMemberStructure.value_l hℳ A k hk n).val =
        mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn) := by
      change mk_l hℳ (SecondOrderMemberNormalizer.code_l hℳ A k hk n) = _
      rw [SecondOrderMemberNormalizer.code_fixed_l hℳ A k hk n hn]
    have hEnv : SecondOrderMemberBounded.env_l
        (ξ.pushFree (sort := SetTheory.SetSort.set) (SecondOrderMemberStructure.value_l hℳ A k hk n)) =
        PowerlessRelativeClassRelativization.env_l (η.pushFree (sort := SetTheory.SetSort.set)
          ⟨mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn), hChild n hn⟩) := by
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
    have hClass := PowerlessRelativeClassBounded.formula_l hφ
      (η.pushFree (sort := SetTheory.SetSort.set) ⟨mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn), hChild n hn⟩)
    have h' := (hRead n hn).trans (slice_formula_l φ ξ ⟨X.val, hXc⟩ (SecondOrderMemberStructure.value_l hℳ A k hk n))
    change mem_l hℳ (mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn)) z ↔
      mem_l hℳ (SecondOrderMemberStructure.value_l hℳ A k hk n).val X.val ∧
        φ.satisfies (ξ.pushFree (SecondOrderMemberStructure.value_l hℳ A k hk n)) at h'
    rw [hValue] at h'
    exact h'.trans (and_congr Iff.rfl (hSource.trans hClass.symm))
  refine ⟨⟨z, ⟨b, d, hd, hz⟩⟩, fun x => ?_⟩
  constructor
  · intro hxz
    obtain ⟨n, hn, hxn⟩ := SecondOrderMemberDefProperties.member_root_l hℳ A
      (SecondOrderMemberDefProperties.subset_l hℳ hDef hz x.val hxz)
    have hEq : x = (⟨mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn), hChild n hn⟩ : type_l hℳ B) := Subtype.ext hxn
    rw [hEq] at hxz ⊢
    exact (hRead' n hn).mp hxz
  · rintro ⟨hxX, hφx⟩
    obtain ⟨n, hn, hxn⟩ := SecondOrderMemberDefProperties.member_root_l hℳ A (hTrans X.val hXc x.val hxX)
    have hEq : x = (⟨mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn), hChild n hn⟩ : type_l hℳ B) := Subtype.ext hxn
    rw [hEq] at hxX hφx ⊢
    exact (hRead' n hn).mpr ⟨hxX, hφx⟩

theorem models_l {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) :
    (SecondOrderSeparationAxiom.sentence_m φ).TrueIn (structure_l hℳ B hBase) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  apply (PowerlessWeakSeparationSyntax.schema_formula_l φ η).mpr
  exact exists_l hφ η

theorem derives_m {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m (SecondOrderSeparationAxiom.sentence_m φ))) :=
  PowerlessRelativeClassRelativization.derives_m _ (fun _ _ _ _ => models_l hφ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassDeltaSeparation
