import BMSConstructibleBridge.PowerlessRelativeFiniteProgramBoundAppend

/-! # 每个母集常量都有真实单指令程序

从真正空词和空存储状态取得零步 Class 历史，再追加实际指令
(t₀,y)。不要求预先存在任何程序输出；因此也可把缺省基底值
替换为母集中的合法常量程序，避免将缺省 output 当成真实 run。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramConstant

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeFiniteProgramExecution (relation_m relation_formula_l)
open PowerlessRelativeFiniteProgramInstruction (functional_l functional_m tags_m)
open PowerlessRelativeFiniteProgramBoundOutput (run_l)
open PowerlessBMSQuotientSubsetImageDerives
  (parameters_l parameters_pushBound_l parameters_empty_l at_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)

def result_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a y : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <|
    let S : Term ℒ [.set, .set, .set] Δ .set := .bvar (.there (.there .here))
    let v := .bvar (.there .here)
    let q := .bvar .here
    .conj (SecondOrderObjectSyntax.ordered_m (up₃ t₀) (up₃ y) q) <|
      .conj (PowerlessRelativeFiniteProgramWordAppend.append_m
        (up₃ B) (up₃ e) (up₃ e) (up₃ Q) q S v)
        (PowerlessRelativeFiniteProgramBoundRun.run_m φ
          (up₃ B) (up₃ C) (up₃ ω) v (up₃ e) (up₃ t₀) (up₃ t₁) (up₃ t₂)
            (up₃ a) S (up₃ e) (up₃ y))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem exists_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B C ω Q e t₀ t₁ t₂ a y : Term ℒ [] Δ .set)
    (hBase : ∀ z, mem_l hℳ z (B.eval η) → ∀ u, mem_l hℳ u z → mem_l hℳ u (B.eval η))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η))
    (hω : ω.eval η = K.omega) (he : ∀ z, ¬mem_l hℳ z (e.eval η))
    (hInitial : PowerlessRelativeFiniteProgramStep.record_l (e.eval η) (e.eval η) (e.eval η) (a.eval η))
    (hQC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (Q.eval η))
    (hTags : t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η)
    (hFunctional : functional_l φ η (B.eval η))
    (hAlphabet : ∀ q, mem_l hℳ q (Q.eval η) ↔
      PowerlessRelativeFiniteProgramAlphabet.instruction_l (C.eval η) (ω.eval η)
        (t₀.eval η) (t₁.eval η) (t₂.eval η) q)
    (hy : mem_l hℳ (y.eval η) (C.eval η)) :
    ∃ S v q, ordered_l (ℳ := 𝒱) (t₀.eval η) (y.eval η) q ∧
      PowerlessRelativeFiniteProgramWordAppend.append_l
        (B.eval η) (e.eval η) (e.eval η) (Q.eval η) q S v ∧
          run_l φ η (B.eval η) (C.eval η) (ω.eval η) v (e.eval η)
            (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) S (e.eval η) (y.eval η) := by
  have hValid := PowerlessRelativeFiniteProgramStep.initial_l K hBase he hInitial
  have haC := PowerlessRelativeFiniteProgramStep.record_class_l hBase
    hValid.2.2.1 hValid.2.2.2.1 hValid.2.2.2.2.1 hInitial
  have heEq : e.eval η = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val :=
    SecondOrderQuotient.ext_l hℳ _ _ (fun z =>
      iff_of_false (he z) (PowerlessBMSQuotientSuccessor.zero_l K z))
  have hw : map_l (ℳ := 𝒱) (e.eval η) (e.eval η) (Q.eval η) :=
    ⟨fun z hz => (he z hz).elim, fun z hz => (he z hz).elim⟩
  let ψ := relation_m φ B C ω e e t₀ t₁ t₂
  have hTotal : ∀ z, PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) z →
      ∃ t, PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) t ∧
        ψ.satisfies ((η.pushFree z).pushFree t) := by
    intro z _
    obtain ⟨t, ht, _⟩ := PowerlessRelativeFiniteProgramStep.exists_unique_l
      φ η hBase hC hw hTags hFunctional z
    exact ⟨t, ht.1, (relation_formula_l K φ η B C ω e e t₀ t₁ t₂ z t).mpr ht⟩
  obtain ⟨S, D, F, hDC, hFC, hTrace⟩ :=
    PowerlessRelativeClassDefinableFiniteTrace.exists_l K ψ η B e a
      hBase haC heEq hTotal (SecondOrderModel.zero_l ℳ)
  rw [← heEq] at hTrace
  have hF : PowerlessRelativeFiniteProgramBoundAppend.history_l φ η
      (B.eval η) (C.eval η) (ω.eval η) (e.eval η) (e.eval η) (e.eval η)
        (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) S D F := by
    simpa only [ψ, PowerlessDefinableFiniteTrace.trace_l,
      PowerlessRelativeFiniteProgramBoundAppend.history_l, relation_formula_l K,
      ThirdOrderSemantics.member_l, SecondOrderQuotient.structure_l] using hTrace
  obtain ⟨q, hqy⟩ := SecondOrderPairObjects.ordered_exists_l hℳ (t₀.eval η) (y.eval η)
  have hq := (hAlphabet q).mpr (Or.inl ⟨y.eval η, hy, hqy⟩)
  have hComputed := (PowerlessRelativeFiniteProgramInstruction.constant_l φ η
    (q := q) (a := y.eval η) (y := y.eval η)
    hBase hC hValid.2.2.2.1 hValid.2.2.2.2.2 hTags hqy hy).mpr rfl
  let ξ : Env 𝒱 [.set, .set] Δ := (η.pushBound S).pushBound q
  let σ : Term ℒ [.set, .set] Δ .set := .bvar (.there .here)
  let ρ : Term ℒ [.set, .set] Δ .set := .bvar .here
  have hu (t : Term ℒ [] Δ .set) : (up₂ t).eval ξ = t.eval η := by
    simp only [up₂, up, Term.eval_weakenBound, ξ]
  have hσ : σ.eval ξ = S := rfl
  have hρ : ρ.eval ξ = q := rfl
  have hParams : parameters_l ξ = η := by
    simp only [ξ, parameters_pushBound_l, parameters_empty_l]
  obtain ⟨v, hAppend, hNew⟩ := PowerlessRelativeFiniteProgramBoundAppend.exists_l K φ ξ
    (up₂ B) (up₂ C) (up₂ ω) (up₂ e) (up₂ e) (up₂ Q) ρ σ (up₂ e)
      (up₂ t₀) (up₂ t₁) (up₂ t₂) (up₂ a)
    (by simpa only [hu] using hBase) (by simpa only [hu] using hC)
    (by simpa only [hu] using hω) (by simpa only [hu] using he)
    (by simpa only [hu] using hInitial) (by simpa only [hu] using hValid.2.2.1)
    (by simpa only [hu] using hValid.2.2.1) (by simpa only [hu] using hQC)
    (by simpa only [hu] using hw) (by simpa only [hu, hρ] using hq)
    (by simpa only [hu] using hTags) (by simpa only [hu, hParams] using hFunctional)
    (by simpa only [hu] using hValid.2.1) (by simpa only [hu] using hDC)
    (by simpa only [hu] using hFC) (by simpa only [hu, hσ, hParams] using hF)
    (by simpa only [hu] using hTrace.2.2.1)
    (by simpa only [hu] using hω.symm ▸ hValid)
    (by simpa only [hu, hρ, hParams] using hComputed)
  refine ⟨S, v, q, hqy, ?_, ?_⟩
  · simpa only [hu, hσ, hρ] using hAppend
  · simpa only [hu, hσ, hParams] using hNew

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a y : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B C) <|
      .imp (SecondOrderOmegaSyntax.omega_m ω) <|
        .imp (PowerlessDefinableFiniteTraceDerives.zero_m e) <|
          .imp (PowerlessRelativeFiniteProgramStep.record_m e e e a) <|
            .imp (PowerlessRelativeHierarchySyntax.class_m B Q) <|
              .imp (tags_m t₀ t₁ t₂) <| .imp (functional_m φ B) <|
                .imp (PowerlessRelativeFiniteProgramAlphabet.alphabet_m C ω t₀ t₁ t₂ Q) <|
                  .imp (SecondOrderObjectSyntax.member_m y C) (result_m φ B C ω Q e t₀ t₁ t₂ a y)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a y : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B C ω Q e t₀ t₁ t₂ a y)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a y : Term ℒ [] Δ .set) :
    (sentence_m φ B C ω Q e t₀ t₁ t₂ a y).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, result_m, PowerlessDefinableFiniteTraceDerives.zero_m,
    tags_m, functional_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeFiniteProgramStep.record_formula_l,
    PowerlessRelativeFiniteProgramWordAppend.append_formula_l K,
    PowerlessRelativeFiniteProgramAlphabet.alphabet_formula_l,
    PowerlessRelativeFiniteProgramBoundRun.run_formula_l K,
    ordered_formula_l, at_formula_l, parameters_pushBound_l, parameters_empty_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up₃, up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro η hBase hC hω he hInitial hQC hTags hFunctional hAlphabet hy
  exact exists_l K φ η B C ω Q e t₀ t₁ t₂ a y hBase hC
    (SecondOrderOmega.unique_l h𝒩 hω K.omega_spec) he hInitial hQC hTags hFunctional hAlphabet hy

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a y : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B C ω Q e t₀ t₁ t₂ a y)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ h𝒩 => models_l h𝒩 φ B C ω Q e t₀ t₁ t₂ a y)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramConstant
