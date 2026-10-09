import BMSConstructibleBridge.SecondOrderCandidateSourceClassSeed
import BMSConstructibleBridge.PowerlessRelativeCandidateBoundedCondensation

/-! # 原候选种子上的实际有限族与有界凝聚

消费 ClassSeed.exists_l 的同一精确种子、首截断及原参数赋值。全部自由
对象的 Class 资格由实际层和原参数成员性推出；初始良序与精确基底来自
原种子。没有预供程序标签、种子图族、I 或坍缩见证。
原 Z₂ 对象存在模式由 CandidateBoundedCondensation.derives_m 提供；本模块
将该模式用于真实候选，是终局源模型构造的语义中间步骤，尚非完整源公理
验证或最终 H 行 BMS 的对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCandidateBoundedCondensation

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeCandidateCondensationReading (conclusion_m)
open PowerlessRelativeSourceFamilyCandidateCondensation (base_formula_l)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev free {Δ : SortContext ℒ} (t : Term ℒ [] Δ .set) :=
  t.weakenFree SetTheory.SetSort.set
private abbrev free₃ {Δ : SortContext ℒ} (t : Term ℒ [] Δ .set) := free (free (free t))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

/-- 原参数属于实际 W 即可；不另要求全部上下文 Class 或某棵已给图族。 -/
theorem exists_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (K : source_coding_l hℳ) {t₁ t₂ t₃ Pair Valid B S Ω W : SecondOrderQuotient.type_l hℳ}
    {A : PowerlessArithmetic.set_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega}
    {X : ℳ.Carrier .set} (P₀ : PowerlessRelativeClassStructure.type_l hℳ B)
    (hSeed : SecondOrderCandidateSourcePreparation.seed_context_l
      K t₁ t₂ t₃ Pair Valid B P₀.val S A X)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B K.omega Ω)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W)
    {Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (hΦ₀ : ∀ p ∈ PowerlessRelativeFiniteHullExtensionality.family_m Δ, p ∈ Φ)
    (hΦ₁ : ∀ p ∈ PowerlessRelativeFiniteHullClosure.family_m Δ, p ∈ Φ)
    (vB vω vA : Variable Δ .set)
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ)
    (hB : η.freeVal vB = B) (hω : η.freeVal vω = K.omega)
    (hA : η.freeVal vA = A.val)
    (hParams : ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v) W) :
    (conclusion_m Φ (free (.fvar vB)) (.fvar .here) (free (.fvar vω))
      (fun v => free (.fvar v))).satisfies
        (η.pushFree (sort := SetTheory.SetSort.set) W) := by
  have hBase x hx y hy := hSeed.1.2.1.2.1 x y hx hy
  have hWC := PowerlessRelativeLevelClosure.class_l hℳ hBase hW
  have hΩC := PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase hΩ.1
  have hηC s (v : Variable Δ s) :=
    PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hWC (hParams s v)
  let Θ : SortContext ℒ := .set :: .set :: .set :: Δ
  let ζ := ((η.pushFree (sort := SetTheory.SetSort.set) P₀.val).pushFree
    (sort := SetTheory.SetSort.set) Ω).pushFree (sort := SetTheory.SetSort.set) W
  let b : Term ℒ [] Θ .set := free₃ (.fvar vB)
  let o : Term ℒ [] Θ .set := free₃ (.fvar vω)
  let d : Term ℒ [] Θ .set := free₃ (.fvar vA)
  let p : Term ℒ [] Θ .set := .fvar (.there (.there .here))
  let α : Term ℒ [] Θ .set := .fvar (.there .here)
  let w : Term ℒ [] Θ .set := .fvar .here
  let ν := fun v : Variable Δ .set => free₃ (.fvar v)
  have hv (v : Variable Δ .set) : (free₃ (.fvar v)).eval ζ = η.freeVal v := rfl
  have hClass : (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_m Θ b
      (fun v => .fvar v)).satisfies ζ := by
    apply (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_formula_l K
      Θ ζ b (fun v => .fvar v)).mpr
    intro s v
    cases s
    change PowerlessRelativeClassCorrespondence.member_l hℳ
      ((free₃ (.fvar vB)).eval ζ) (ζ.freeVal v)
    rw [hv, hB]
    dsimp only [Θ] at v
    cases v with
    | here => exact hWC
    | there v =>
      cases v with
      | here => exact hΩC
      | there v =>
        cases v with
        | here => exact P₀.property
        | there v => exact hηC _ v
  have hGuard : (SecondOrderCanonicalLevelDerives.guard_m b p).satisfies ζ := by
    apply (SecondOrderCanonicalLevelDerives.guard_formula_l ζ b p).mpr
    simpa only [b, p, hv, hB, Term.eval, ζ, Env.pushFree_here, Env.pushFree_there]
      using hSeed.1.2.1
  have hOmega : (SecondOrderOmegaSyntax.omega_m o).satisfies ζ := by
    apply (SecondOrderOmegaSyntax.omega_l hℳ ζ o).mpr
    simpa only [o, hv, hω] using K.omega_spec
  have hFirst : (PowerlessRelativeOrdinalCutoff.first_m b o α).satisfies ζ := by
    apply (PowerlessRelativeOrdinalCutoff.first_formula_l K ζ b o α).mpr
    simpa only [b, o, α, hv, hB, hω, Term.eval, ζ, Env.pushFree_here, Env.pushFree_there]
      using hΩ
  have hLevel : (PowerlessRelativeHierarchySyntax.level_m b α w).satisfies ζ := by
    apply (PowerlessRelativeHierarchySemantics.level_formula_l K ζ b α w).mpr
    simpa only [b, α, w, hv, hB, Term.eval, ζ, Env.pushFree_here, Env.pushFree_there]
      using hW
  have hBW : (SecondOrderObjectSyntax.member_m b w).satisfies ζ := by
    change mem_l hℳ (b.eval ζ) W
    simpa only [b, hv] using hParams SetTheory.SetSort.set vB
  have hParameters : (parameters_m Δ w ν).satisfies ζ := by
    apply (parameters_formula_l Δ ζ w ν).mpr
    simpa only [w, ν, hv, Term.eval, ζ, Env.pushFree_here, ThirdOrderSemantics.member_l,
      SecondOrderQuotient.structure_l] using hParams
  have hAdjoin : (SecondOrderFunctionAppendDerives.adjoin_m o d b).satisfies ζ := by
    apply (base_formula_l ζ o d b).mpr
    simpa only [b, o, d, hv, hB, hω, hA, ThirdOrderSemantics.member_l,
      SecondOrderQuotient.structure_l] using hSeed.2.1
  have hJoint := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
    (PowerlessRelativeCandidateBoundedCondensation.models_l hℳ Φ hΦ hΦ₀ hΦ₁
      vB vω vA b p o α w d ν rfl rfl rfl) ζ
      hClass hGuard hOmega hFirst hLevel hBW hParameters hAdjoin
  exact PowerlessRelativeNumeralCondensation.transport_l hℳ K Φ ζ
    (η.pushFree (sort := SetTheory.SetSort.set) W) b w o ν
    (free (.fvar vB)) (.fvar .here) (free (.fvar vω)) (fun v => free (.fvar v))
    rfl rfl rfl (fun _ => rfl) hJoint

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCandidateBoundedCondensation
