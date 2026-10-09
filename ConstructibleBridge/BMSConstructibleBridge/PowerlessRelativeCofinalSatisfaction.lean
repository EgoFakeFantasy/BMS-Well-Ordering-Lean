import BMSConstructibleBridge.PowerlessRelativeCofinalLimitBounds
import BMSConstructibleBridge.PowerlessRelativeLimitFiniteSequences
import BMSConstructibleBridge.PowerlessRelativeLimitSatisfactionStatic

/-! # 共尾极限层中实际构造序列见证与 Sat

给定层中非零极限阶段共尾时，连续选取两个严格先前极限层。第一层
收纳实际参数，第二层收纳实际构造的全有限赋值集；再用已证固定层
Sat 定理。调用端不再预设 S、内层 D 或求值方程，仍明确保留共尾守卫。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCofinalSatisfaction

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B β C : SecondOrderQuotient.type_l hℳ}
    {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}
    (hC : level_l hℳ B β C) (hLimit : limit_l hℳ β)
    (hCofinal : PowerlessRelativeCofinalLimitBounds.cofinal_l β)
    {Δ : SortContext ℒ} (η : Env (structure_l hℳ B hBase) [] Δ)
    (ω e N T A t₁ t₂ t₃ : Term ℒ [] Δ .set)
    (hParams : ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v).val C)
    (hω : omega_l (ℳ := structure_l hℳ B hBase) (ω.eval η))
    {F : type_l hℳ B} (hFC : mem_l hℳ F.val C)
    (hStatic : PowerlessSatisfactionExistenceSyntax.static_l (𝒩 := structure_l hℳ B hBase)
      (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (T.eval η) (N.eval η) F) :
    ∃ R : type_l hℳ B, mem_l hℳ R.val C ∧
      PowerlessSatisfactionSpecification.spec_l (𝒩 := structure_l hℳ B hBase)
        (ω.eval η) (A.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (T.eval η) F R := by
  have hTermC (t : Term ℒ [] Δ .set) : mem_l hℳ (t.eval η).val C := by
    match t with
    | .bvar v => nomatch v
    | .fvar v => exact hParams _ v
    | .app f _ => nomatch f
  have hRawParams : ∀ s (v : Variable Δ s),
      mem_l hℳ ((PowerlessRelativeClassRelativization.env_l η).freeVal v) C := by
    intro s v
    cases s
    exact hParams _ v
  obtain ⟨δ, E, hδβ, hE, hELimit, _, hParamsE⟩ := PowerlessRelativeCofinalLimitBounds.exists_l
    hBase hLimit hC hCofinal (PowerlessRelativeClassRelativization.env_l η) (hTermC ω) hRawParams
  have hTermE (t : Term ℒ [] Δ .set) : mem_l hℳ (t.eval η).val E := by
    match t with
    | .bvar v => nomatch v
    | .fvar v => exact hParamsE _ v
    | .app f _ => nomatch f
  obtain ⟨γ, hγβ, hδγ, hDLimit⟩ := hCofinal δ hδβ
  have hγ : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)) γ := by
    apply SetTheory.Structure.IsOrdinal.mem (PowerlessRelativeLevelClosure.ordinal_l hℳ hC)
    exact hγβ
  obtain ⟨D, hD⟩ := PowerlessRelativeOrdinalCoverage.level_exists_l hℳ hBase hγ
  have hωRaw := (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) (ω.eval η)).mp hω
  obtain ⟨s, hsD, hs⟩ := PowerlessRelativeLimitFiniteSequences.exists_l hBase hELimit hE hDLimit hD hδγ
    hωRaw (hTermE ω) (hTermE A)
  let S : type_l hℳ B := ⟨s, ⟨γ, D, hD, hsD⟩⟩
  have hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := structure_l hℳ B hBase) (ω.eval η) (A.eval η) S :=
    fun f => (hs f.val).trans
      (PowerlessRelativeClassFiniteSequencesDerives.sequence_absolute_l (hBase := hBase) (ω.eval η) (A.eval η) f).symm
  let ξ := η.pushFree (sort := SetTheory.SetSort.set) S
  let w (t : Term ℒ [] Δ .set) := t.weakenFree SetTheory.SetSort.set
  have hParamsD : ∀ q (v : Variable (.set :: Δ) q), mem_l hℳ (ξ.freeVal v).val D := by
    intro q v
    cases q
    cases v with
    | here => exact hsD
    | there v => exact PowerlessRelativeLevelClosure.subset_l hℳ hBase hδγ hE hD _ (hParamsE _ v)
  obtain ⟨R, hRC, hSat⟩ := PowerlessRelativeLimitSatisfactionStatic.exists_l (F := F)
    hD hDLimit hC hLimit hγβ ξ (w ω) (w e) (w N) (w T) (w A) (.fvar .here) (w t₁) (w t₂) (w t₃)
    hParamsD (by simpa only [w, ξ, Term.eval_weakenFree] using hω)
    (by simpa only [w, ξ, Term.eval_weakenFree, Term.eval, Env.pushFree_here] using hS) hFC
    (by simpa only [w, ξ, Term.eval_weakenFree] using hStatic)
  exact ⟨R, hRC, by simpa only [w, ξ, Term.eval_weakenFree] using hSat⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCofinalSatisfaction
