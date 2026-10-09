import BMSConstructibleBridge.SecondOrderCandidateBoundedCondensation
import BMSConstructibleBridge.PowerlessRelativeCandidateStrictCondensation

/-! # 原实际候选种子的严格凝聚

复用已验证的同一候选存在树，只加强其坍缩结论。全部程序标签、图族、
I/T/H/J 与预算仍由证明内构造；调用端不提供 ClassH、CountT 或 J<Ω。
对象消去规则来自 CandidateStrictCondensation.derives_m。本模块是实际
源模型装配的语义接口，尚未验证完整 Collection 或最终 BMS 闭句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCandidateStrictCondensation

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeSourceFamilyCandidateCondensation (base_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev free {Δ : SortContext ℒ} (t : Term ℒ [] Δ .set) :=
  t.weakenFree SetTheory.SetSort.set

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

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
    (hB : η.freeVal vB = B) (hω : η.freeVal vω = K.omega) (hA : η.freeVal vA = A.val)
    (hParams : ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v) W) :
    (PowerlessRelativeCandidateStrictCondensation.conclusion_m Φ
      (free (.fvar vB)) (.fvar .here) (free (.fvar vω)) (fun v => free (.fvar v))).satisfies
        (η.pushFree (sort := SetTheory.SetSort.set) W) := by
  let ζ := η.pushFree (sort := SetTheory.SetSort.set) W
  let b := free (.fvar vB)
  let o := free (.fvar vω)
  let d := free (.fvar vA)
  let w : Term ℒ [] (.set :: Δ) .set := .fvar .here
  have hSource : (PowerlessRelativeSourceFamilyCodedCapture.source_m b o w).satisfies ζ := by
    apply (PowerlessRelativeSourceFamilyCodedCapture.source_formula_l hℳ K ζ b o w).mpr
    simpa only [b, o, w, free, Term.eval_weakenFree, Term.eval, ζ, Env.pushFree_here, hB, hω]
      using And.intro (fun x hx y hy => hSeed.1.2.1.2.1 x y hx hy)
        (And.intro K.omega_spec (Exists.intro Ω (And.intro hΩ hW)))
  have hAdjoin : (SecondOrderFunctionAppendDerives.adjoin_m o d b).satisfies ζ := by
    apply (base_formula_l ζ o d b).mpr
    simpa only [b, o, d, free, Term.eval_weakenFree, Term.eval, ζ, hB, hω, hA,
      ThirdOrderSemantics.member_l, SecondOrderQuotient.structure_l] using hSeed.2.1
  exact PowerlessRelativeCandidateStrictCondensation.upgrade_l K Φ hΦ hΦ₁
    vB vω vA ζ b w o d (fun v => free (.fvar v)) rfl rfl rfl hSource hAdjoin
    (SecondOrderCandidateBoundedCondensation.exists_l hℳ K P₀ hSeed hΩ hW
      Φ hΦ hΦ₀ hΦ₁ vB vω vA η hB hω hA hParams)

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCandidateStrictCondensation
