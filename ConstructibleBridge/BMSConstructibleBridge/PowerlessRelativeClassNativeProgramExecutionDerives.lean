import BMSConstructibleBridge.PowerlessRelativeClassNativeFiniteTraceDerives
import BMSConstructibleBridge.PowerlessRelativeClassNativeProgramStepDerives

/-! # 类内同一有限程序的内部执行及原 Z₂ 推导

对象语言纯隶属 ℒ，原 num/set Z₂ 为背景。将已证明总单值的原状态
转移矩阵代入内部有限历史模式，消去调用端的逐步总性前提。
任意 Class 初值都可执行；有效初始记录的不变式、无限程序壳图资格、
源理论和最终固定行高 BMS 良序仍须另证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassNativeProgramExecutionDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassFormulaInstances (instance_m instance_l members_m members_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_empty_l parameters_pushBound_l)
open PowerlessRelativeFiniteProgramInstruction (tags_m)
open PowerlessDefinableFiniteTraceUnique (functional_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev free₂ {Δ : SortContext ℒ} (t : Term ℒ [] Δ .set) :=
  (t.weakenFree SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set

def relation_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w e t₀ t₁ t₂ : Term ℒ [] Δ .set) : Formula ℒ [] (.set :: .set :: Δ) :=
  PowerlessFiniteProgramStepSyntax.step_m
    (PowerlessDefinableFiniteTrace.lift_m (PowerlessDefinableFiniteTrace.lift_m φ))
    (free₂ B) (free₂ C) (free₂ ω) (free₂ w) (free₂ e)
      (free₂ t₀) (free₂ t₁) (free₂ t₂) (.fvar (.there .here)) (.fvar .here)

theorem relation_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 [] Δ)
    (B C ω w e t₀ t₁ t₂ : Term ℒ [] Δ .set) (s t : carrier_l 𝒩) :
    (relation_m φ B C ω w e t₀ t₁ t₂).satisfies ((η.pushFree s).pushFree t) ↔
      PowerlessFiniteProgramStepSyntax.step_l φ η (B.eval η) (C.eval η) (ω.eval η)
        (w.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) s t := by
  simp only [relation_m, PowerlessFiniteProgramStepSyntax.step_formula_l,
    parameters_empty_l, free₂, Term.eval_weakenFree, Term.eval, Env.pushFree_here, Env.pushFree_there,
    PowerlessFiniteProgramStepSyntax.step_l, PowerlessFiniteProgramStepSyntax.good_l,
    PowerlessFiniteProgramStoreSyntax.store_l, PowerlessFiniteProgramInstructionSyntax.computed_l,
    PowerlessFiniteProgramInstructionSyntax.good_l, PowerlessDefinableFiniteTrace.lift_formula_l]

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ z, mem_l hℳ z B → ∀ t, mem_l hℳ t z → mem_l hℳ t B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => structure_l hℳ B hBase
local notation "M" => type_l hℳ B

theorem exists_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (b C ω w N Q e t₀ t₁ t₂ a n : Term ℒ [] Δ .set)
    (η : Env 𝒩₀ [] Δ) (hb : (b.eval η).val = B)
    (he : (e.eval η).val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hn : mem_l hℳ (n.eval η).val K.omega) (hw : map_l (ℳ := 𝒩₀) (w.eval η) (N.eval η) (Q.eval η))
    (hTags : t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η)
    (hFunctional : ∀ x y z : M, φ.satisfies ((η.pushFree x).pushFree y) →
      φ.satisfies ((η.pushFree x).pushFree z) → y = z) :
    ∃ S D f : M, PowerlessDefinableFiniteTrace.trace_l (relation_m φ b C ω w e t₀ t₁ t₂)
      η (e.eval η) (a.eval η) (n.eval η) S D f := by
  have hb' : b.eval η = ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ :=
    Subtype.ext hb
  have hTotal : ∀ s : M, ∃ t : M,
      (relation_m φ b C ω w e t₀ t₁ t₂).satisfies ((η.pushFree s).pushFree t) := by
    intro s
    obtain ⟨t, ht, _⟩ := PowerlessRelativeClassNativeProgramStepDerives.result_l K φ b η hb
      (C.eval η) (ω.eval η) (w.eval η) (N.eval η) (Q.eval η) (e.eval η)
      (t₀.eval η) (t₁.eval η) (t₂.eval η) s hw hTags hFunctional
    refine ⟨t, (relation_formula_l φ η b C ω w e t₀ t₁ t₂ s t).mpr ?_⟩
    simpa only [hb'] using ht
  exact PowerlessRelativeClassNativeFiniteTraceDerives.exists_l K
    (relation_m φ b C ω w e t₀ t₁ t₂) b e a n η hb he hTotal hn

def guarded_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w N Q e t₀ t₁ t₂ a n : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (SecondOrderObjectSyntax.map_m w N Q) <| .imp (tags_m t₀ t₁ t₂) <|
    .imp (functional_m φ) <| .imp (SecondOrderObjectSyntax.member_m n ω)
      (PowerlessDefinableFiniteTrace.finite_m (relation_m φ B C ω w e t₀ t₁ t₂) e a n)

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w N Q e t₀ t₁ t₂ a n : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <| .imp (PowerlessDefinableFiniteTraceDerives.zero_m e) <|
      .imp (members_m Δ B (fun v => .fvar v)) <|
        instance_m (guarded_m φ B C ω w N Q e t₀ t₁ t₂ a n) B (fun v => .fvar v)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w N Q e t₀ t₁ t₂ a n : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B C ω w N Q e t₀ t₁ t₂ a n)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (b C ω w N Q e t₀ t₁ t₂ a n : Term ℒ [] Δ .set) :
    (sentence_m φ b C ω w N Q e t₀ t₁ t₂ a n).TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ, SecondOrderOmegaSyntax.omega_l,
    PowerlessDefinableFiniteTraceDerives.zero_formula_l, members_l K]
  intro hBase hω he hMembers
  let ξ : Env (structure_l hℳ (b.eval η) hBase) [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with | .set => ⟨η.freeVal v, hMembers v⟩ }
  have hEnv : PowerlessRelativeClassRelativization.env_l ξ = η := by
    apply Env.ext
    · intro _ v; nomatch v
    · intro s v; cases s; rfl
  have hTerm (t : Term ℒ [] Δ .set) : (t.eval ξ).val = t.eval η := by
    have hRead := PowerlessRelativeClassRelativization.term_l ξ t
    simpa only [Term.eval_weakenFree, hEnv] using hRead.symm
  have he' : (e.eval ξ).val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val := by
    rw [hTerm]
    exact SecondOrderQuotient.ext_l hℳ _ _
      (fun x => iff_of_false (he x) (PowerlessBMSQuotientSuccessor.zero_l K x))
  apply (instance_l K (guarded_m φ b C ω w N Q e t₀ t₁ t₂ a n)
    η b (fun v => .fvar v) ξ rfl (fun _ => rfl)).mpr
  simp only [guarded_m, functional_m, tags_m, Formula.satisfies,
    map_formula_l, PowerlessBMSQuotientSubsetImageDerives.at_formula_l,
    parameters_pushBound_l, parameters_empty_l, PowerlessDefinableFiniteTrace.finite_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro hw hTags hFunctional hn
  change mem_l hℳ (n.eval ξ).val (ω.eval ξ).val at hn
  have hn' : mem_l hℳ (n.eval ξ).val K.omega := by
    simpa only [hTerm ω, SecondOrderOmega.unique_l hℳ hω K.omega_spec] using hn
  exact exists_l (hBase := hBase) K φ b C ω w N Q e t₀ t₁ t₂ a n ξ
    (hTerm b) he' hn' hw hTags hFunctional

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w N Q e t₀ t₁ t₂ a n : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B C ω w N Q e t₀ t₁ t₂ a n)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 φ B C ω w N Q e t₀ t₁ t₂ a n)

#print axioms relation_formula_l
#print axioms exists_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassNativeProgramExecutionDerives
