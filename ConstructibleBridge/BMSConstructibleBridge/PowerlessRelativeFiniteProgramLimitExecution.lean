import BMSConstructibleBridge.PowerlessRelativeLimitDefinableFiniteTrace
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramLimitStep
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramExecution

/-! # 实际程序的全部内部有限历史有共同层界

将同一个原状态转移矩阵代入同层有限轨迹构造。初态留层来自
真实空记录，W 上转移总性来自已证明的原 Step 总单值及保层定理，
不把它们留作新的程序历史假设。每个内部长度给实际 S、D、F∈W。
尚未据此断言无限求值图或整个求值像具有 Class 集合性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramLimitExecution

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)
open PowerlessRelativeFiniteProgramInstruction (functional_l functional_m tags_m)
open PowerlessBMSQuotientSubsetImageDerives
  (parameters_pushBound_l parameters_empty_l at_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

def result_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C W ω w e t₀ t₁ t₂ a n : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  PowerlessRelativeLimitDefinableFiniteTrace.finite_m
    (PowerlessRelativeFiniteProgramExecution.relation_m φ B C ω w e t₀ t₁ t₂) W e a n

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem exists_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B β W C ω w N Q e t₀ t₁ t₂ a n : Term ℒ [] Δ .set)
    (hB : ∀ x, mem_l hℳ x (B.eval η) → ∀ z, mem_l hℳ z x → mem_l hℳ z (B.eval η))
    (hβ : limit_l hℳ (β.eval η)) (hW : level_l hℳ (B.eval η) (β.eval η) (W.eval η))
    (hBW : mem_l hℳ (B.eval η) (W.eval η))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η))
    (hCW : ∀ x, mem_l hℳ x (C.eval η) → mem_l hℳ x (W.eval η))
    (hω : SecondOrderOmega.omega_l hℳ (ω.eval η))
    (hωW : mem_l hℳ (ω.eval η) (W.eval η)) (he : ∀ x, ¬mem_l hℳ x (e.eval η))
    (ha : PowerlessRelativeFiniteProgramStep.record_l
      (e.eval η) (e.eval η) (e.eval η) (a.eval η))
    (hw : map_l (ℳ := 𝒱) (w.eval η) (N.eval η) (Q.eval η))
    (ht : t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η)
    (hφ : functional_l φ η (B.eval η))
    (hφW : PowerlessRelativeFiniteProgramLimitStep.closed_l φ η (B.eval η) (W.eval η))
    (hn : mem_l hℳ (n.eval η) (ω.eval η)) : ∃ S D F,
    mem_l hℳ S (W.eval η) ∧ mem_l hℳ D (W.eval η) ∧ mem_l hℳ F (W.eval η) ∧
      PowerlessDefinableFiniteTrace.trace_l
        (PowerlessRelativeFiniteProgramExecution.relation_m φ B C ω w e t₀ t₁ t₂)
          η (e.eval η) (a.eval η) (n.eval η) S D F := by
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  have heEq : e.eval η = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val :=
    SecondOrderQuotient.ext_l hℳ _ _ (fun x => iff_of_false (he x) (PowerlessBMSQuotientSuccessor.zero_l K x))
  have heω : mem_l hℳ (e.eval η) (ω.eval η) :=
    hωEq.symm ▸ (heEq.symm ▸ (numberCode_l K (SecondOrderModel.zero_l ℳ)).property)
  have heW := PowerlessRelativeLevelClosure.transitive_l hℳ hB hW _ hωW _ heω
  have haW : mem_l hℳ (a.eval η) (W.eval η) := by
    obtain ⟨p, hep, hea⟩ := ha
    exact PowerlessRelativeLimitClosure.ordered_l hℳ hB hβ hW heW
      (PowerlessRelativeLimitClosure.ordered_l hℳ hB hβ hW heW heW hep) hea
  let ψ := PowerlessRelativeFiniteProgramExecution.relation_m φ B C ω w e t₀ t₁ t₂
  have hTotal : ∀ x, mem_l hℳ x (W.eval η) → ∃ y, mem_l hℳ y (W.eval η) ∧
      ψ.satisfies ((η.pushFree x).pushFree y) := by
    intro x hx
    obtain ⟨y, hy, _⟩ := PowerlessRelativeFiniteProgramStep.exists_unique_l
      φ η hB hC hw ht hφ x
    exact ⟨y, PowerlessRelativeFiniteProgramLimitStep.step_l φ η hB hβ hW hBW hCW hφW hx hy,
      (PowerlessRelativeFiniteProgramExecution.relation_formula_l K φ η B C ω w e t₀ t₁ t₂ x y).mpr hy⟩
  obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨n.eval η, hωEq ▸ hn⟩
  have hi' : (numberCode_l K i).val = n.eval η := congrArg Subtype.val hi
  rw [← hi']
  exact PowerlessRelativeLimitDefinableFiniteTrace.exists_l K ψ η B β W e a
    hB hβ hW (hωEq ▸ hωW) haW heEq hTotal i

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β W C ω w N Q e t₀ t₁ t₂ a n : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.limit_m β) <|
      .imp (PowerlessRelativeHierarchySyntax.level_m B β W) <|
        .imp (SecondOrderObjectSyntax.member_m B W) <|
          .imp (PowerlessRelativeHierarchySyntax.class_m B C) <|
            .imp (ThirdOrderTheory.subset_m C W) <|
              .imp (SecondOrderOmegaSyntax.omega_m ω) <|
                .imp (SecondOrderObjectSyntax.member_m ω W) <|
                  .imp (PowerlessDefinableFiniteTraceDerives.zero_m e) <|
                    .imp (PowerlessRelativeFiniteProgramStep.record_m e e e a) <|
                      .imp (SecondOrderObjectSyntax.map_m w N Q) <| .imp (tags_m t₀ t₁ t₂) <|
                        .imp (functional_m φ B) <|
                          .imp (PowerlessRelativeFiniteProgramLimitStep.closed_m φ B W) <|
                            .imp (SecondOrderObjectSyntax.member_m n ω)
                              (result_m φ B C W ω w e t₀ t₁ t₂ a n)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β W C ω w N Q e t₀ t₁ t₂ a n : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B β W C ω w N Q e t₀ t₁ t₂ a n)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (B β W C ω w N Q e t₀ t₁ t₂ a n : Term ℒ [] Δ .set) :
    (sentence_m φ B β W C ω w N Q e t₀ t₁ t₂ a n).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, result_m, tags_m, functional_m, Formula.satisfies,
    PowerlessDefinableFiniteTraceDerives.zero_m,
    PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.limit_formula_l, PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeHierarchySemantics.class_formula_l K, subset_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeFiniteProgramStep.record_formula_l,
    PowerlessRelativeFiniteProgramLimitStep.closed_formula_l K,
    PowerlessRelativeLimitDefinableFiniteTrace.finite_formula_l, map_formula_l, at_formula_l,
    parameters_pushBound_l, parameters_empty_l, SecondOrderObjectSyntax.member_m,
    Arguments.eval, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro η hB hβ hW hBW hC hCW hω hωW he ha hw ht hφ hφW hn
  exact exists_l K φ η B β W C ω w N Q e t₀ t₁ t₂ a n
    hB hβ hW hBW hC hCW hω hωW he ha hw ht hφ hφW hn

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β W C ω w N Q e t₀ t₁ t₂ a n : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B β W C ω w N Q e t₀ t₁ t₂ a n)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ h𝒩 => models_l h𝒩 φ B β W C ω w N Q e t₀ t₁ t₂ a n)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramLimitExecution
