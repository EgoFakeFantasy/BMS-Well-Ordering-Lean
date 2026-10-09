import BMSConstructibleBridge.PowerlessRelativeFiniteProgramBoundOutput

/-! # 全部内部程序码上的原求值公式

代码只含程序词和输出坐标，内部长度由干净图读取且唯一。
本模块给每个实际代码唯一 Class 输出；有效坐标另有真实历史读数。
求值的全像尚未假定为集合，程序拼接和 Skolem 闭包仍须单独证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramEvaluation

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_l parameters_pushBound_l parameters_empty_l)
open PowerlessRelativeFiniteProgramInstruction (functional_l functional_m tags_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)

private def run_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w e t₀ t₁ t₂ a n k y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let t := @PowerlessSourceRebinding.term_m Γ Δ
  PowerlessSourceRebinding.formula_m <|
    PowerlessRelativeFiniteProgramOutput.run_m
      (PowerlessRelativeFiniteProgramBoundOutput.step_m φ B C ω w e t₀ t₁ t₂)
        (t B) (t ω) (t e) (t a) (t n) (t k) (t y)

def matrix_m {Γ Δ : SortContext ℒ} (actual : Bool)
    (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a p y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <|
    let w : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
    let k := .bvar (.there .here)
    let n := .bvar .here
    .conj (SecondOrderObjectSyntax.ordered_m w k (up₃ p)) <|
      .conj (SecondOrderObjectSyntax.member_m k (up₃ ω)) <|
        .conj (SecondOrderObjectSyntax.member_m n (up₃ ω)) <|
          .conj (SecondOrderObjectSyntax.map_m w n (up₃ Q)) <|
            if actual then run_m φ (up₃ B) (up₃ C) (up₃ ω) w (up₃ e)
              (up₃ t₀) (up₃ t₁) (up₃ t₂) (up₃ a) n k (up₃ y)
            else PowerlessRelativeFiniteProgramBoundOutput.output_m φ (up₃ B) (up₃ C)
              (up₃ ω) w (up₃ e) (up₃ t₀) (up₃ t₁) (up₃ t₂) (up₃ a) n k (up₃ y)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def matrix_l {Δ : SortContext ℒ} (actual : Bool)
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B C ω Q e t₀ t₁ t₂ a p y : type_l hℳ) : Prop :=
  ∃ w k n, ordered_l (ℳ := 𝒱) w k p ∧ mem_l hℳ k ω ∧ mem_l hℳ n ω ∧
    map_l (ℳ := 𝒱) w n Q ∧
      if actual then PowerlessRelativeFiniteProgramBoundOutput.run_l
        φ η B C ω w e t₀ t₁ t₂ a n k y
      else PowerlessRelativeFiniteProgramBoundOutput.output_l
        φ η B C ω w e t₀ t₁ t₂ a n k y

private theorem run_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B C ω w e t₀ t₁ t₂ a n k y : Term ℒ Γ Δ .set) :
    (run_m φ B C ω w e t₀ t₁ t₂ a n k y).satisfies η ↔
      PowerlessRelativeFiniteProgramBoundOutput.run_l φ (parameters_l η)
        (B.eval η) (C.eval η) (ω.eval η) (w.eval η) (e.eval η) (t₀.eval η)
          (t₁.eval η) (t₂.eval η) (a.eval η) (n.eval η) (k.eval η) (y.eval η) := by
  simp only [run_m, PowerlessSourceRebinding.formula_l,
    PowerlessRelativeFiniteProgramOutput.run_formula_l K, parameters_empty_l,
    PowerlessSourceRebinding.term_l, PowerlessRelativeFiniteProgramBoundOutput.run_open_l K]

theorem matrix_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (actual : Bool) (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B C ω Q e t₀ t₁ t₂ a p y : Term ℒ Γ Δ .set) :
    (matrix_m actual φ B C ω Q e t₀ t₁ t₂ a p y).satisfies η ↔
      matrix_l actual φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η) (Q.eval η)
        (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (p.eval η) (y.eval η) := by
  cases actual <;> simp only [matrix_m, matrix_l, Bool.false_eq_true, if_false, if_true,
    Formula.satisfies, ordered_formula_l, map_formula_l, SecondOrderObjectSyntax.member_m,
    Arguments.eval, PowerlessRelativeFiniteProgramBoundOutput.output_formula_l K,
    run_formula_l K, parameters_pushBound_l, up₃, up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  all_goals rfl

private theorem decoded_result_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B C ω Q e t₀ t₁ t₂ a : Term ℒ Γ Δ .set)
    (hBase : ∀ x, mem_l hℳ x (B.eval η) → ∀ z, mem_l hℳ z x → mem_l hℳ z (B.eval η))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η))
    (hω : SecondOrderOmega.omega_l hℳ (ω.eval η)) (he : ∀ x, ¬mem_l hℳ x (e.eval η))
    (hInitial : PowerlessRelativeFiniteProgramStep.record_l (e.eval η) (e.eval η) (e.eval η) (a.eval η))
    (hTags : t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η)
    (hFunctional : functional_l φ (parameters_l η) (B.eval η))
    (w k n : type_l hℳ) (hn : mem_l hℳ n (ω.eval η))
    (hw : map_l (ℳ := 𝒱) w n (Q.eval η)) :
    (∃! y, PowerlessRelativeFiniteProgramBoundOutput.output_l φ (parameters_l η)
      (B.eval η) (C.eval η) (ω.eval η) w (e.eval η) (t₀.eval η) (t₁.eval η)
        (t₂.eval η) (a.eval η) n k y) ∧
    (mem_l hℳ k n → ∃ y, PowerlessRelativeFiniteProgramBoundOutput.run_l φ (parameters_l η)
      (B.eval η) (C.eval η) (ω.eval η) w (e.eval η) (t₀.eval η) (t₁.eval η)
        (t₂.eval η) (a.eval η) n k y) := by
  let ξ : Env 𝒱 (.set :: .set :: .set :: Γ) Δ :=
    ((η.pushBound (sort := SetTheory.SetSort.set) w).pushBound
      (sort := SetTheory.SetSort.set) k).pushBound (sort := SetTheory.SetSort.set) n
  have ht (v : Term ℒ Γ Δ .set) : (up₃ v).eval ξ = v.eval η := by
    simp only [ξ, up₃, up₂, up, Term.eval_weakenBound]
  have h := PowerlessRelativeFiniteProgramBoundOutput.result_l K φ ξ
    (up₃ B) (up₃ C) (up₃ ω) (.bvar (.there (.there .here))) (up₃ Q) (up₃ e)
      (up₃ t₀) (up₃ t₁) (up₃ t₂) (up₃ a) (.bvar .here) (.bvar (.there .here))
      (by simpa only [ht] using hBase) (by simpa only [ht] using hC)
      (by simpa only [ht] using hω) (by simpa only [ht] using he)
      (by simpa only [ht] using hInitial)
      (by simpa only [ht, ξ, Term.eval, Env.pushBound_bound_here,
        Env.pushBound_bound_there] using hw)
      (by simpa only [ht] using hTags)
      (by simpa only [ht, ξ, parameters_pushBound_l] using hFunctional)
      (by simpa only [ht, ξ, Term.eval, Env.pushBound_bound_here] using hn)
  simpa only [ht, ξ, Term.eval, parameters_pushBound_l,
    Env.pushBound_bound_here, Env.pushBound_bound_there] using h

theorem result_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B C ω Q e t₀ t₁ t₂ a p : Term ℒ Γ Δ .set)
    (hBase : ∀ x, mem_l hℳ x (B.eval η) → ∀ z, mem_l hℳ z x → mem_l hℳ z (B.eval η))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η))
    (hω : SecondOrderOmega.omega_l hℳ (ω.eval η)) (he : ∀ x, ¬mem_l hℳ x (e.eval η))
    (hInitial : PowerlessRelativeFiniteProgramStep.record_l (e.eval η) (e.eval η) (e.eval η) (a.eval η))
    (hTags : t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η)
    (hFunctional : functional_l φ (parameters_l η) (B.eval η))
    {S P : type_l hℳ}
    (hDomain : PowerlessRelativeFiniteProgramDomain.domain_l (B.eval η) (ω.eval η) (Q.eval η) S P)
    (hp : mem_l hℳ (p.eval η) P) :
    (∃! y, matrix_l false φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η) (Q.eval η)
      (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (p.eval η) y) ∧
    (∀ w k n, ordered_l (ℳ := 𝒱) w k (p.eval η) → mem_l hℳ k (ω.eval η) →
      mem_l hℳ n (ω.eval η) → map_l (ℳ := 𝒱) w n (Q.eval η) → mem_l hℳ k n →
        ∃ y, matrix_l true φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η) (Q.eval η)
          (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (p.eval η) y) := by
  obtain ⟨w, k, n, hCode, hk, hn, hw⟩ := PowerlessRelativeFiniteProgramDomain.decode_l hDomain hp
  have hAt := decoded_result_l K φ η B C ω Q e t₀ t₁ t₂ a
    hBase hC hω he hInitial hTags hFunctional w k n hn hw
  obtain ⟨y, hy, hUnique⟩ := hAt.1
  constructor
  · refine ⟨y, ⟨w, k, n, hCode, hk, hn, hw, hy⟩, ?_⟩
    rintro z ⟨w', k', n', hCode', _, _, hw', hz⟩
    obtain ⟨hww, hkk⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hCode' hCode).mp rfl
    subst w'; subst k'
    have hnn := PowerlessRelativeFiniteProgramDomain.length_unique_l hw' hw
    subst n'
    exact hUnique z hz
  · intro w' k' n' hCode' hk' hn' hw' hkn
    obtain ⟨z, hz⟩ := (decoded_result_l K φ η B C ω Q e t₀ t₁ t₂ a
      hBase hC hω he hInitial hTags hFunctional w' k' n' hn' hw').2 hkn
    exact ⟨z, w', k', n', hCode', hk', hn', hw', hz⟩

def conclusion_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a p : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (.existsE .set <| .conj
      (matrix_m false φ (up B) (up C) (up ω) (up Q) (up e) (up t₀) (up t₁) (up t₂) (up a) (up p) (.bvar .here)) <|
        .forallE .set <| .imp
          (matrix_m false φ (up₂ B) (up₂ C) (up₂ ω) (up₂ Q) (up₂ e) (up₂ t₀) (up₂ t₁) (up₂ t₂) (up₂ a) (up₂ p) (.bvar .here))
          (.equal (.bvar .here) (.bvar (.there .here)))) <|
    .forallE .set <| .forallE .set <| .forallE .set <|
      let w : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
      let k := .bvar (.there .here)
      let n := .bvar .here
      .imp (SecondOrderObjectSyntax.ordered_m w k (up₃ p)) <|
        .imp (SecondOrderObjectSyntax.member_m k (up₃ ω)) <|
          .imp (SecondOrderObjectSyntax.member_m n (up₃ ω)) <|
            .imp (SecondOrderObjectSyntax.map_m w n (up₃ Q)) <|
              .imp (SecondOrderObjectSyntax.member_m k n) <|
                .existsE .set <| matrix_m true φ (up (up₃ B)) (up (up₃ C)) (up (up₃ ω))
                  (up (up₃ Q)) (up (up₃ e)) (up (up₃ t₀)) (up (up₃ t₁)) (up (up₃ t₂))
                  (up (up₃ a)) (up (up₃ p)) (.bvar .here)

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a S P : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B C) <|
      .imp (SecondOrderOmegaSyntax.omega_m ω) <|
        .imp (PowerlessDefinableFiniteTraceDerives.zero_m e) <|
          .imp (PowerlessRelativeFiniteProgramStep.record_m e e e a) <|
            .imp (tags_m t₀ t₁ t₂) <| .imp (functional_m φ B) <|
              .imp (PowerlessRelativeFiniteProgramDomain.domain_m B ω Q S P) <|
                .forallE .set <| .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (up P))
                  (conclusion_m φ (up B) (up C) (up ω) (up Q) (up e)
                    (up t₀) (up t₁) (up t₂) (up a) (.bvar .here))

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a S P : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B C ω Q e t₀ t₁ t₂ a S P)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (B C ω Q e t₀ t₁ t₂ a S P : Term ℒ [] Δ .set) :
    (sentence_m φ B C ω Q e t₀ t₁ t₂ a S P).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, conclusion_m, PowerlessDefinableFiniteTraceDerives.zero_m,
    tags_m, functional_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeFiniteProgramStep.record_formula_l,
    PowerlessRelativeFiniteProgramDomain.domain_formula_l K, matrix_formula_l K,
    ordered_formula_l, map_formula_l, parameters_pushBound_l, parameters_empty_l,
    PowerlessBMSQuotientSubsetImageDerives.at_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up₃, up₂, up, Term.eval_weakenBound,
    Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro η hBase hC hω he hInitial hTags hFunctional hDomain p hp
  have ht (v : Term ℒ [] Δ .set) : (up v).eval (η.pushBound p) = v.eval η := by
    simp only [up, Term.eval_weakenBound]
  have h := result_l K φ (η.pushBound p) (up B) (up C) (up ω) (up Q) (up e)
    (up t₀) (up t₁) (up t₂) (up a) (.bvar .here)
    (by simpa only [ht] using hBase)
    (by simpa only [ht, PowerlessRelativeClassCorrespondence.member_l] using hC)
    (by simpa only [ht] using hω)
    (by simpa only [ht, SecondOrderQuotient.structure_l] using he)
    (by simpa only [ht] using hInitial) (by simpa only [ht] using hTags)
    (by simpa only [ht, parameters_pushBound_l, parameters_empty_l, functional_l,
      PowerlessRelativeClassCorrespondence.member_l, SecondOrderQuotient.structure_l,
      ThirdOrderSemantics.carrier_l] using hFunctional)
    (by simpa only [ht] using hDomain)
    (by simpa only [Term.eval, Env.pushBound_bound_here, SecondOrderQuotient.structure_l] using hp)
  simpa only [ht, parameters_pushBound_l, parameters_empty_l, Term.eval,
    Env.pushBound_bound_here, SecondOrderQuotient.structure_l,
    ThirdOrderSemantics.carrier_l, ExistsUnique] using h

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a S P : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B C ω Q e t₀ t₁ t₂ a S P)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 φ B C ω Q e t₀ t₁ t₂ a S P)

#print axioms matrix_formula_l
#print axioms result_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramEvaluation
