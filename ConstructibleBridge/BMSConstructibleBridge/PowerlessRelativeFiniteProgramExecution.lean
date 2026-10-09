import BMSConstructibleBridge.PowerlessRelativeFiniteProgramStep
import BMSConstructibleBridge.PowerlessDefinableFiniteTraceUnique

/-! # 原程序的内部有限执行历史

将实际指令状态转移代入原 Z₂ 公式归纳，取得每个内部长度的实际
Class 历史图。初值是真正空计数、空陪域与空图组成的状态。
历史图唯一，任意历史陪域不必唯一；不假设无限执行图存在。
本模块尚不证明程序拼接、闭包或最终 BMS 良序句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramExecution

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessBMSQuotientSubsetImageDerives
  (parameters_pushBound_l parameters_empty_l at_formula_l)
open PowerlessRelativeFiniteProgramInstruction (functional_m functional_l tags_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private abbrev free₂ {Δ : SortContext ℒ} (t : Term ℒ [] Δ .set) :=
  (t.weakenFree SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set

def relation_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w e t₀ t₁ t₂ : Term ℒ [] Δ .set) : Formula ℒ [] (.set :: .set :: Δ) :=
  PowerlessRelativeFiniteProgramStep.step_m
    (PowerlessDefinableFiniteTrace.lift_m (PowerlessDefinableFiniteTrace.lift_m φ))
    (free₂ B) (free₂ C) (free₂ ω) (free₂ w) (free₂ e)
      (free₂ t₀) (free₂ t₁) (free₂ t₂) (.fvar (.there .here)) (.fvar .here)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem relation_formula_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B C ω w e t₀ t₁ t₂ : Term ℒ [] Δ .set) (s t : type_l hℳ) :
    (relation_m φ B C ω w e t₀ t₁ t₂).satisfies ((η.pushFree s).pushFree t) ↔
      PowerlessRelativeFiniteProgramStep.step_l φ η
        (B.eval η) (C.eval η) (ω.eval η) (w.eval η) (e.eval η)
          (t₀.eval η) (t₁.eval η) (t₂.eval η) s t := by
  simp only [relation_m, PowerlessRelativeFiniteProgramStep.step_formula_l K,
    parameters_empty_l, free₂, Term.eval_weakenFree, Term.eval,
    Env.pushFree_here, Env.pushFree_there,
    PowerlessRelativeFiniteProgramStep.step_l, PowerlessRelativeFiniteProgramStep.good_l,
    PowerlessRelativeFiniteProgramStore.store_l,
    PowerlessRelativeFiniteProgramInstruction.computed_l,
    PowerlessRelativeFiniteProgramInstruction.good_l,
    PowerlessDefinableFiniteTrace.lift_formula_l]

theorem total_unique_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B C ω w N Q e t₀ t₁ t₂ : Term ℒ [] Δ .set)
    (hBase : ∀ x, mem_l hℳ x (B.eval η) → ∀ z, mem_l hℳ z x → mem_l hℳ z (B.eval η))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η))
    (hw : map_l (ℳ := 𝒱) (w.eval η) (N.eval η) (Q.eval η))
    (hTags : t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η)
    (hFunctional : functional_l φ η (B.eval η)) (s : type_l hℳ) :
    ∃! t, PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) t ∧
      (relation_m φ B C ω w e t₀ t₁ t₂).satisfies ((η.pushFree s).pushFree t) := by
  obtain ⟨t, ht, hUnique⟩ := PowerlessRelativeFiniteProgramStep.exists_unique_l
    φ η hBase hC hw hTags hFunctional s
  exact ⟨t, ⟨ht.1, (relation_formula_l K φ η B C ω w e t₀ t₁ t₂ s t).mpr ht⟩,
    fun z hz => hUnique z ((relation_formula_l K φ η B C ω w e t₀ t₁ t₂ s z).mp hz.2)⟩

def result_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w e t₀ t₁ t₂ a n : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  let ψ := relation_m φ B C ω w e t₀ t₁ t₂
  .conj (PowerlessRelativeClassDefinableFiniteTrace.finite_m ψ B e a n)
    (PowerlessDefinableFiniteTraceUnique.conclusion_m ψ e a n)

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w N Q e t₀ t₁ t₂ a n : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B C) <|
      .imp (SecondOrderOmegaSyntax.omega_m ω) <|
        .imp (PowerlessDefinableFiniteTraceDerives.zero_m e) <|
          .imp (PowerlessRelativeFiniteProgramStep.record_m e e e a) <|
            .imp (SecondOrderObjectSyntax.map_m w N Q) <| .imp (tags_m t₀ t₁ t₂) <|
              .imp (functional_m φ B) <| .imp (SecondOrderObjectSyntax.member_m n ω)
                (result_m φ B C ω w e t₀ t₁ t₂ a n)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w N Q e t₀ t₁ t₂ a n : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B C ω w N Q e t₀ t₁ t₂ a n)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (B C ω w N Q e t₀ t₁ t₂ a n : Term ℒ [] Δ .set) :
    (sentence_m φ B C ω w N Q e t₀ t₁ t₂ a n).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, result_m, tags_m, functional_m, PowerlessDefinableFiniteTraceDerives.zero_m,
    Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeFiniteProgramStep.record_formula_l, map_formula_l,
    PowerlessRelativeClassDefinableFiniteTrace.finite_formula_l K,
    PowerlessDefinableFiniteTraceUnique.conclusion_m, PowerlessDefinableFiniteTrace.trace_formula_l,
    at_formula_l, parameters_pushBound_l, parameters_empty_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro η hBase hC hω he hInitial hw hTags hFunctional hn
  have hωEq := SecondOrderOmega.unique_l h𝒩 hω K.omega_spec
  rw [hωEq] at hn
  have hInitialValid := PowerlessRelativeFiniteProgramStep.initial_l K hBase he hInitial
  have haC := PowerlessRelativeFiniteProgramStep.record_class_l hBase
    hInitialValid.2.2.1 hInitialValid.2.2.2.1 hInitialValid.2.2.2.2.1 hInitial
  have heEq : e.eval η = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val := by
    apply SecondOrderQuotient.ext_l h𝒩
    intro x
    exact iff_of_false (he x) (PowerlessBMSQuotientSuccessor.zero_l K x)
  let ψ := relation_m φ B C ω w e t₀ t₁ t₂
  have hUnique : ∀ x y z, ψ.satisfies ((η.pushFree x).pushFree y) →
      ψ.satisfies ((η.pushFree x).pushFree z) → y = z := by
    intro x y z hy hz
    obtain ⟨v, _, hv⟩ := PowerlessRelativeFiniteProgramStep.exists_unique_l
      φ η hBase hC hw hTags hFunctional x
    exact (hv y ((relation_formula_l K φ η B C ω w e t₀ t₁ t₂ x y).mp hy)).trans
      (hv z ((relation_formula_l K φ η B C ω w e t₀ t₁ t₂ x z).mp hz)).symm
  have hTotal : ∀ x, PowerlessRelativeClassCorrespondence.member_l h𝒩 (B.eval η) x →
      ∃ y, PowerlessRelativeClassCorrespondence.member_l h𝒩 (B.eval η) y ∧
        ψ.satisfies ((η.pushFree x).pushFree y) := by
    intro x _
    obtain ⟨y, hy, _⟩ := total_unique_l K φ η B C ω w N Q e t₀ t₁ t₂
      hBase hC hw hTags hFunctional x
    exact ⟨y, hy⟩
  obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨n.eval η, hn⟩
  have hiEq : (numberCode_l K i).val = n.eval η := congrArg Subtype.val hi
  refine ⟨?_, ?_⟩
  · rw [← hiEq]
    exact PowerlessRelativeClassDefinableFiniteTrace.exists_l K ψ η B e a hBase haC heEq hTotal i
  · intro S D f T E g hF hG
    exact PowerlessDefinableFiniteTraceUnique.unique_l K ψ η hn heEq hF hG hUnique

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w N Q e t₀ t₁ t₂ a n : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B C ω w N Q e t₀ t₁ t₂ a n)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 φ B C ω w N Q e t₀ t₁ t₂ a n)

#print axioms relation_formula_l
#print axioms total_unique_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramExecution
