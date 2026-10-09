import BMSConstructibleBridge.PowerlessRelativeFiniteProgramConstant
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramEvaluationGraph

/-! # 原总化求值的精确像具有实际程序代表

原代码域仍为 Seq(Q)×ω，求值像仍包括空词与无效坐标的缺省输出。
由 B∈C 的真实常量程序替代缺省代表，证明整个精确像等于实际执行像，
并包含常量种子 C。只更换存在见证，不删改原代码或原求值关系。
背景为原 Z₂；公开终点是原推导核中的条件对象句子，不是假设闭包成立。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramImageRealization

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeFiniteProgramInstruction (functional_l functional_m tags_m)
open PowerlessRelativeFiniteProgramEvaluation (matrix_m matrix_l matrix_formula_l)
open PowerlessBMSQuotientSubsetImageDerives
  (parameters_l parameters_pushBound_l parameters_empty_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)

private abbrev free {Δ : SortContext ℒ} (t : Term ℒ [] Δ .set) :=
  t.weakenFree SetTheory.SetSort.set

def image_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a P I : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .iff (SecondOrderObjectSyntax.member_m (.bvar .here) (up I)) <|
    membershipLevyBound.boundedExists (up P) <|
      matrix_m true φ (up₂ B) (up₂ C) (up₂ ω) (up₂ Q) (up₂ e)
        (up₂ t₀) (up₂ t₁) (up₂ t₂) (up₂ a) (.bvar .here) (.bvar (.there .here))

def conclusion_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a P I : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (.forallE .set <| .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (up C))
      (SecondOrderObjectSyntax.member_m (.bvar .here) (up I)))
    (image_m φ B C ω Q e t₀ t₁ t₂ a P I)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem image_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B C ω Q e t₀ t₁ t₂ a P I : Term ℒ Γ Δ .set) :
    (image_m φ B C ω Q e t₀ t₁ t₂ a P I).satisfies η ↔
      ∀ y, mem_l hℳ y (I.eval η) ↔ ∃ p, mem_l hℳ p (P.eval η) ∧
        matrix_l true φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η) (Q.eval η)
          (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) p y := by
  simp only [image_m, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, matrix_formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval, parameters_pushBound_l,
    up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  rfl

/-- 每个种子常量在同一原域中都有实际执行代码。 -/
theorem constant_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B C ω Q e t₀ t₁ t₂ a S P y : Term ℒ [] Δ .set)
    (hBase : ∀ z, mem_l hℳ z (B.eval η) → ∀ u, mem_l hℳ u z → mem_l hℳ u (B.eval η))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η))
    (hω : SecondOrderOmega.omega_l hℳ (ω.eval η)) (he : ∀ z, ¬mem_l hℳ z (e.eval η))
    (ha : PowerlessRelativeFiniteProgramStep.record_l (e.eval η) (e.eval η) (e.eval η) (a.eval η))
    (hQ : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (Q.eval η))
    (ht : t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η)
    (hφ : functional_l φ η (B.eval η))
    (hAlphabet : ∀ q, mem_l hℳ q (Q.eval η) ↔
      PowerlessRelativeFiniteProgramAlphabet.instruction_l (C.eval η) (ω.eval η)
        (t₀.eval η) (t₁.eval η) (t₂.eval η) q)
    (hDomain : PowerlessRelativeFiniteProgramDomain.domain_l
      (B.eval η) (ω.eval η) (Q.eval η) (S.eval η) (P.eval η))
    (hy : mem_l hℳ (y.eval η) (C.eval η)) :
    ∃ p, mem_l hℳ p (P.eval η) ∧ matrix_l true φ η
      (B.eval η) (C.eval η) (ω.eval η) (Q.eval η) (e.eval η)
        (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) p (y.eval η) := by
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  obtain ⟨N, w, _, _, hAppend, hRun⟩ := PowerlessRelativeFiniteProgramConstant.exists_l
    K φ η B C ω Q e t₀ t₁ t₂ a y hBase hC hωEq he ha hQ ht hφ hAlphabet hy
  have hZero : e.eval η = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val :=
    SecondOrderQuotient.ext_l hℳ _ _ (fun z =>
      iff_of_false (he z) (PowerlessBMSQuotientSuccessor.zero_l K z))
  have hSuc : PowerlessNatural.successor_l (ℳ := 𝒱) (e.eval η)
      (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).val :=
    hZero.symm ▸ PowerlessBMSQuotientSuccessor.successor_l K (SecondOrderModel.zero_l ℳ)
  have hN : N = (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).val :=
    SecondOrderQuotient.ext_l hℳ _ _ (fun z => (hAppend.2.2.1 z).trans (hSuc z).symm)
  have hNω : mem_l hℳ N (ω.eval η) := hωEq.symm ▸ hN.symm ▸
    (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).property
  have heω : mem_l hℳ (e.eval η) (ω.eval η) := hωEq.symm ▸ hZero.symm ▸
    (numberCode_l K (SecondOrderModel.zero_l ℳ)).property
  have hw : mem_l hℳ w (S.eval η) :=
    (hDomain.2.1 w).mpr ⟨N, hNω, hAppend.2.2.2.1⟩
  obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ w (e.eval η)
  exact ⟨p, (hDomain.2.2.2 p).mpr ⟨w, e.eval η, hw, heω, hp⟩,
    w, e.eval η, N, hp, heω, hNω, hAppend.2.2.2.1, hRun⟩

/-- 实际执行始终是原总化求值的一支；Class 输出由存储图回收。 -/
theorem actual_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {B C ω Q e t₀ t₁ t₂ a p y : type_l hℳ}
    (hBase : ∀ z, mem_l hℳ z B → ∀ u, mem_l hℳ u z → mem_l hℳ u B)
    (h : matrix_l true φ η B C ω Q e t₀ t₁ t₂ a p y) :
    matrix_l false φ η B C ω Q e t₀ t₁ t₂ a p y := by
  obtain ⟨w, k, n, hp, hk, hn, hw, hRun⟩ := h
  have hy : PowerlessRelativeClassCorrespondence.member_l hℳ B y := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hValid, hgy⟩ := hRun
    exact PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hValid.2.2.2.1
      (SecondOrderFunctionProperties.value_mem_l hℳ hValid.2.2.2.2.2 hgy).2
  exact ⟨w, k, n, hp, hk, hn, hw, hy, Or.inl hRun⟩

theorem normal_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B C ω Q e t₀ t₁ t₂ a S P : Term ℒ [] Δ .set) (I : type_l hℳ)
    (hBase : ∀ z, mem_l hℳ z (B.eval η) → ∀ u, mem_l hℳ u z → mem_l hℳ u (B.eval η))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η))
    (hω : SecondOrderOmega.omega_l hℳ (ω.eval η)) (he : ∀ z, ¬mem_l hℳ z (e.eval η))
    (ha : PowerlessRelativeFiniteProgramStep.record_l (e.eval η) (e.eval η) (e.eval η) (a.eval η))
    (hQ : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (Q.eval η))
    (ht : t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η)
    (hφ : functional_l φ η (B.eval η))
    (hAlphabet : ∀ q, mem_l hℳ q (Q.eval η) ↔
      PowerlessRelativeFiniteProgramAlphabet.instruction_l (C.eval η) (ω.eval η)
        (t₀.eval η) (t₁.eval η) (t₂.eval η) q)
    (hDomain : PowerlessRelativeFiniteProgramDomain.domain_l
      (B.eval η) (ω.eval η) (Q.eval η) (S.eval η) (P.eval η))
    (hBC : mem_l hℳ (B.eval η) (C.eval η))
    (hImage : ∀ y, mem_l hℳ y I ↔ ∃ p, mem_l hℳ p (P.eval η) ∧
      matrix_l false φ η (B.eval η) (C.eval η) (ω.eval η) (Q.eval η) (e.eval η)
        (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) p y) :
    (∀ y, mem_l hℳ y (C.eval η) → mem_l hℳ y I) ∧
      ∀ y, mem_l hℳ y I ↔ ∃ p, mem_l hℳ p (P.eval η) ∧
        matrix_l true φ η (B.eval η) (C.eval η) (ω.eval η) (Q.eval η) (e.eval η)
          (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) p y := by
  have hDefault := constant_l K φ η B C ω Q e t₀ t₁ t₂ a S P B
    hBase hC hω he ha hQ ht hφ hAlphabet hDomain hBC
  have hActual (y : type_l hℳ) : mem_l hℳ y I ↔ ∃ p, mem_l hℳ p (P.eval η) ∧
      matrix_l true φ η (B.eval η) (C.eval η) (ω.eval η) (Q.eval η) (e.eval η)
        (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) p y := by
    constructor
    · intro hy
      obtain ⟨p, hp, w, k, n, hCode, hk, hn, hw, _, hOutput⟩ := (hImage y).mp hy
      rcases hOutput with hRun | ⟨_, hEq⟩
      · exact ⟨p, hp, w, k, n, hCode, hk, hn, hw, hRun⟩
      · exact hEq.symm ▸ hDefault
    · rintro ⟨p, hp, hRun⟩
      exact (hImage y).mpr ⟨p, hp, actual_l φ η hBase hRun⟩
  refine ⟨?_, hActual⟩
  intro y hy
  let ξ : Env 𝒱 [] (.set :: Δ) := η.pushFree y
  let Y : Term ℒ [] (.set :: Δ) .set := .fvar .here
  -- 常量定理仅需增加一个原参数槽，不把求值像的成员当作种子成员。
  -- 使用已有常量代码的通用形式，统一保留全部原参数的解释。
  have hLift := constant_l K (PowerlessDefinableFiniteTrace.lift_m φ) ξ
    (free B) (free C) (free ω) (free Q) (free e) (free t₀) (free t₁) (free t₂)
    (free a) (free S) (free P) Y
    (by simpa only [free, Term.eval_weakenFree, ξ] using hBase)
    (by simpa only [free, Term.eval_weakenFree, ξ] using hC)
    (by simpa only [free, Term.eval_weakenFree, ξ] using hω)
    (by simpa only [free, Term.eval_weakenFree, ξ] using he)
    (by simpa only [free, Term.eval_weakenFree, ξ] using ha)
    (by simpa only [free, Term.eval_weakenFree, ξ] using hQ)
    (by simpa only [free, Term.eval_weakenFree, ξ] using ht)
    (by simpa only [functional_l, PowerlessDefinableFiniteTrace.lift_formula_l,
      free, Term.eval_weakenFree, ξ] using hφ)
    (by simpa only [free, Term.eval_weakenFree, ξ] using hAlphabet)
    (by simpa only [free, Term.eval_weakenFree, ξ] using hDomain)
    (by simpa only [free, Term.eval_weakenFree, Y, Term.eval, ξ, Env.pushFree_here] using hy)
  apply (hActual y).mpr
  simpa only [matrix_l, if_true, PowerlessRelativeFiniteProgramBoundOutput.run_l,
    PowerlessRelativeFiniteProgramStep.step_l, PowerlessRelativeFiniteProgramStep.good_l,
    PowerlessRelativeFiniteProgramStore.store_l,
    PowerlessRelativeFiniteProgramInstruction.computed_l,
    PowerlessRelativeFiniteProgramInstruction.good_l,
    PowerlessDefinableFiniteTrace.lift_formula_l,
    free, Term.eval_weakenFree, Y, Term.eval, ξ, Env.pushFree_here] using hLift

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a S P I : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B C) <|
      .imp (SecondOrderOmegaSyntax.omega_m ω) <|
        .imp (PowerlessDefinableFiniteTraceDerives.zero_m e) <|
          .imp (PowerlessRelativeFiniteProgramStep.record_m e e e a) <|
            .imp (PowerlessRelativeHierarchySyntax.class_m B Q) <|
              .imp (tags_m t₀ t₁ t₂) <| .imp (functional_m φ B) <|
                .imp (PowerlessRelativeFiniteProgramAlphabet.alphabet_m C ω t₀ t₁ t₂ Q) <|
                  .imp (PowerlessRelativeFiniteProgramDomain.domain_m B ω Q S P) <|
                    .imp (SecondOrderObjectSyntax.member_m B C) <|
                      .imp (PowerlessRelativeFiniteProgramEvaluationGraph.image_m φ
                        B C ω Q e t₀ t₁ t₂ a P I) (conclusion_m φ B C ω Q e t₀ t₁ t₂ a P I)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a S P I : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B C ω Q e t₀ t₁ t₂ a S P I)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a S P I : Term ℒ [] Δ .set) :
    (sentence_m φ B C ω Q e t₀ t₁ t₂ a S P I).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, conclusion_m, Formula.satisfies, tags_m,
    PowerlessRelativeFiniteProgramInstruction.functional_formula_l K,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderOmegaSyntax.omega_l,
    PowerlessDefinableFiniteTraceDerives.zero_m,
    PowerlessRelativeFiniteProgramStep.record_formula_l,
    PowerlessRelativeFiniteProgramAlphabet.alphabet_formula_l,
    PowerlessRelativeFiniteProgramDomain.domain_formula_l K,
    PowerlessRelativeFiniteProgramEvaluationGraph.image_formula_l K, image_formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval, parameters_empty_l,
    up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here]
  intro η hBase hC hω he ha hQ ht hφ hAlphabet hDomain hBC hImage
  exact normal_l K φ η B C ω Q e t₀ t₁ t₂ a S P (I.eval η)
    hBase hC hω he ha hQ ht hφ hAlphabet hDomain hBC hImage

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a S P I : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B C ω Q e t₀ t₁ t₂ a S P I)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ h𝒩 => models_l h𝒩 φ B C ω Q e t₀ t₁ t₂ a S P I)

#print axioms image_formula_l
#print axioms constant_l
#print axioms actual_l
#print axioms normal_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramImageRealization
