import BMSConstructibleBridge.PowerlessRelativeFiniteProgramEvaluation

/-! # 程序前缀读数与实际执行历史保持

原词和新词只需在执行长度 n 的全部内部坐标读数相同。
用原计数不变式识别当前指令坐标，将同一实际历史图传给新词。
保留真实读数和缺省总输出两项等价，不假定两个词全域相同。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramPrefix

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeFiniteProgramExecution (relation_m relation_formula_l)
open PowerlessRelativeFiniteProgramInstruction (functional_l functional_m tags_m)
open PowerlessDefinableFiniteTrace (trace_l trace_m trace_formula_l)
open PowerlessRelativeFiniteProgramOutput (run_l output_l run_m output_m)
open PowerlessBMSQuotientSubsetImageDerives (parameters_pushBound_l parameters_empty_l at_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)

def agree_m {Γ Δ : SortContext ℒ} (n w v : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (up n)) <|
    .forallE .set <| .iff
      (SecondOrderObjectSyntax.value_m (up₂ w) (.bvar (.there .here)) (.bvar .here))
      (SecondOrderObjectSyntax.value_m (up₂ v) (.bvar (.there .here)) (.bvar .here))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def agree_l (n w v : type_l hℳ) : Prop :=
  ∀ i, mem_l hℳ i n → ∀ q, value_l (ℳ := 𝒱) w i q ↔ value_l (ℳ := 𝒱) v i q

theorem agree_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (n w v : Term ℒ Γ Δ .set) :
    (agree_m n w v).satisfies η ↔ agree_l (n.eval η) (w.eval η) (v.eval η) := by
  simp only [agree_m, agree_l, Formula.satisfies, value_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem current_congr_l {w v e i : type_l hℳ}
    (hRead : ∀ q, value_l (ℳ := 𝒱) w i q ↔ value_l (ℳ := 𝒱) v i q) (q : type_l hℳ) :
    PowerlessRelativeFiniteProgramStep.current_l w e i q ↔
      PowerlessRelativeFiniteProgramStep.current_l v e i q := by
  simp only [PowerlessRelativeFiniteProgramStep.current_l, hRead]

private theorem good_transfer_l {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    {B C ω w v e t₀ t₁ t₂ i D f s t : type_l hℳ}
    (hRecord : PowerlessRelativeFiniteProgramStep.record_l i D f s)
    (hRead : ∀ q, value_l (ℳ := 𝒱) w i q ↔ value_l (ℳ := 𝒱) v i q)
    (hGood : PowerlessRelativeFiniteProgramStep.good_l φ η B C ω w e t₀ t₁ t₂ s t) :
    PowerlessRelativeFiniteProgramStep.good_l φ η B C ω v e t₀ t₁ t₂ s t := by
  obtain ⟨j, E, g, q, S, A, h, hValid, hCurrent, hStore, hNext⟩ := hGood
  have hji := (PowerlessRelativeFiniteProgramStep.record_coordinates_l hValid.1 hRecord).1
  subst j
  exact ⟨i, E, g, q, S, A, h, hValid, (current_congr_l hRead q).mp hCurrent, hStore, hNext⟩

theorem step_congr_l {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    {B C ω w v e t₀ t₁ t₂ i D f s : type_l hℳ}
    (hRecord : PowerlessRelativeFiniteProgramStep.record_l i D f s)
    (hRead : ∀ q, value_l (ℳ := 𝒱) w i q ↔ value_l (ℳ := 𝒱) v i q) (t : type_l hℳ) :
    PowerlessRelativeFiniteProgramStep.step_l φ η B C ω w e t₀ t₁ t₂ s t ↔
      PowerlessRelativeFiniteProgramStep.step_l φ η B C ω v e t₀ t₁ t₂ s t := by
  have hGood (z : type_l hℳ) :
      PowerlessRelativeFiniteProgramStep.good_l φ η B C ω w e t₀ t₁ t₂ s z ↔
        PowerlessRelativeFiniteProgramStep.good_l φ η B C ω v e t₀ t₁ t₂ s z :=
    ⟨good_transfer_l φ η hRecord hRead,
      good_transfer_l φ η hRecord (fun q => (hRead q).symm)⟩
  simp only [PowerlessRelativeFiniteProgramStep.step_l, hGood]

theorem trace_transfer_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B C ω w N Q v e t₀ t₁ t₂ a n : Term ℒ [] Δ .set) {S D F : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x (B.eval η) → ∀ z, mem_l hℳ z x → mem_l hℳ z (B.eval η))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η))
    (hω : ω.eval η = K.omega) (he : ∀ x, ¬mem_l hℳ x (e.eval η))
    (hInitial : PowerlessRelativeFiniteProgramStep.record_l (e.eval η) (e.eval η) (e.eval η) (a.eval η))
    (hw : map_l (ℳ := 𝒱) (w.eval η) (N.eval η) (Q.eval η))
    (hTags : t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η)
    (hFunctional : functional_l φ η (B.eval η)) (hn : mem_l hℳ (n.eval η) K.omega)
    (hAgree : agree_l (n.eval η) (w.eval η) (v.eval η))
    (hF : trace_l (relation_m φ B C ω w e t₀ t₁ t₂) η (e.eval η) (a.eval η) (n.eval η) S D F) :
    trace_l (relation_m φ B C ω v e t₀ t₁ t₂) η (e.eval η) (a.eval η) (n.eval η) S D F := by
  refine ⟨hF.1, hF.2.1, hF.2.2.1, ?_⟩
  intro i j x y hi hij hx hy
  obtain ⟨E, g, hValid⟩ := PowerlessRelativeFiniteProgramInvariant.values_l K φ η
    B C ω w N Q e t₀ t₁ t₂ a n hBase hC hω he hInitial hw hTags hFunctional hn hF i x hx
  have hStep := (relation_formula_l K φ η B C ω w e t₀ t₁ t₂ x y).mp
    (hF.2.2.2 i j x y hi hij hx hy)
  exact (relation_formula_l K φ η B C ω v e t₀ t₁ t₂ x y).mpr
    ((step_congr_l φ η hValid.1 (hAgree i hi) y).mp hStep)

private theorem run_transfer_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B C ω w N Q v e t₀ t₁ t₂ a n k : Term ℒ [] Δ .set)
    (hBase : ∀ x, mem_l hℳ x (B.eval η) → ∀ z, mem_l hℳ z x → mem_l hℳ z (B.eval η))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η))
    (hω : ω.eval η = K.omega) (he : ∀ x, ¬mem_l hℳ x (e.eval η))
    (hInitial : PowerlessRelativeFiniteProgramStep.record_l (e.eval η) (e.eval η) (e.eval η) (a.eval η))
    (hw : map_l (ℳ := 𝒱) (w.eval η) (N.eval η) (Q.eval η))
    (hTags : t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η)
    (hFunctional : functional_l φ η (B.eval η)) (hn : mem_l hℳ (n.eval η) K.omega)
    (hAgree : agree_l (n.eval η) (w.eval η) (v.eval η)) {y : type_l hℳ}
    (hy : run_l (relation_m φ B C ω w e t₀ t₁ t₂) η
      (B.eval η) (ω.eval η) (e.eval η) (a.eval η) (n.eval η) (k.eval η) y) :
    run_l (relation_m φ B C ω v e t₀ t₁ t₂) η
      (B.eval η) (ω.eval η) (e.eval η) (a.eval η) (n.eval η) (k.eval η) y := by
  obtain ⟨S, D, F, s, E, g, hDC, hFC, hTrace, hs, hValid, hy⟩ := hy
  exact ⟨S, D, F, s, E, g, hDC, hFC, trace_transfer_l K φ η
    B C ω w N Q v e t₀ t₁ t₂ a n hBase hC hω he hInitial hw hTags hFunctional hn hAgree hTrace,
      hs, hValid, hy⟩

theorem reading_congr_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B C ω w N v M Q e t₀ t₁ t₂ a n k : Term ℒ [] Δ .set)
    (hBase : ∀ x, mem_l hℳ x (B.eval η) → ∀ z, mem_l hℳ z x → mem_l hℳ z (B.eval η))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η))
    (hω : ω.eval η = K.omega) (he : ∀ x, ¬mem_l hℳ x (e.eval η))
    (hInitial : PowerlessRelativeFiniteProgramStep.record_l (e.eval η) (e.eval η) (e.eval η) (a.eval η))
    (hw : map_l (ℳ := 𝒱) (w.eval η) (N.eval η) (Q.eval η))
    (hv : map_l (ℳ := 𝒱) (v.eval η) (M.eval η) (Q.eval η))
    (hTags : t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η)
    (hFunctional : functional_l φ η (B.eval η)) (hn : mem_l hℳ (n.eval η) K.omega)
    (hAgree : agree_l (n.eval η) (w.eval η) (v.eval η)) (y : type_l hℳ) :
    (run_l (relation_m φ B C ω w e t₀ t₁ t₂) η
      (B.eval η) (ω.eval η) (e.eval η) (a.eval η) (n.eval η) (k.eval η) y ↔
      run_l (relation_m φ B C ω v e t₀ t₁ t₂) η
        (B.eval η) (ω.eval η) (e.eval η) (a.eval η) (n.eval η) (k.eval η) y) ∧
    (output_l (relation_m φ B C ω w e t₀ t₁ t₂) η
      (B.eval η) (ω.eval η) (e.eval η) (a.eval η) (n.eval η) (k.eval η) y ↔
      output_l (relation_m φ B C ω v e t₀ t₁ t₂) η
        (B.eval η) (ω.eval η) (e.eval η) (a.eval η) (n.eval η) (k.eval η) y) := by
  have hRun (z : type_l hℳ) :
      run_l (relation_m φ B C ω w e t₀ t₁ t₂) η
        (B.eval η) (ω.eval η) (e.eval η) (a.eval η) (n.eval η) (k.eval η) z ↔
      run_l (relation_m φ B C ω v e t₀ t₁ t₂) η
        (B.eval η) (ω.eval η) (e.eval η) (a.eval η) (n.eval η) (k.eval η) z :=
    ⟨run_transfer_l K φ η B C ω w N Q v e t₀ t₁ t₂ a n k
      hBase hC hω he hInitial hw hTags hFunctional hn hAgree,
      run_transfer_l K φ η B C ω v M Q w e t₀ t₁ t₂ a n k
        hBase hC hω he hInitial hv hTags hFunctional hn (fun i hi q => (hAgree i hi q).symm)⟩
  exact ⟨hRun y, by simp only [output_l, hRun]⟩

def conclusion_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w v e t₀ t₁ t₂ a n k : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  let ψ := relation_m φ B C ω w e t₀ t₁ t₂
  let χ := relation_m φ B C ω v e t₀ t₁ t₂
  .forallE .set <| .conj
    (.iff (run_m ψ B ω e a n k (.bvar .here)) (run_m χ B ω e a n k (.bvar .here)))
    (.iff (output_m ψ B ω e a n k (.bvar .here)) (output_m χ B ω e a n k (.bvar .here)))

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w N v M Q e t₀ t₁ t₂ a n k : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B C) <|
      .imp (SecondOrderOmegaSyntax.omega_m ω) <|
        .imp (PowerlessDefinableFiniteTraceDerives.zero_m e) <|
          .imp (PowerlessRelativeFiniteProgramStep.record_m e e e a) <|
            .imp (SecondOrderObjectSyntax.map_m w N Q) <|
              .imp (SecondOrderObjectSyntax.map_m v M Q) <|
                .imp (tags_m t₀ t₁ t₂) <| .imp (functional_m φ B) <|
                  .imp (SecondOrderObjectSyntax.member_m n ω) <|
                    .imp (agree_m n w v) (conclusion_m φ B C ω w v e t₀ t₁ t₂ a n k)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w N v M Q e t₀ t₁ t₂ a n k : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B C ω w N v M Q e t₀ t₁ t₂ a n k)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w N v M Q e t₀ t₁ t₂ a n k : Term ℒ [] Δ .set) :
    (sentence_m φ B C ω w N v M Q e t₀ t₁ t₂ a n k).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, conclusion_m, PowerlessDefinableFiniteTraceDerives.zero_m,
    tags_m, functional_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeFiniteProgramStep.record_formula_l, map_formula_l, agree_formula_l,
    PowerlessRelativeFiniteProgramOutput.run_formula_l K,
    PowerlessRelativeFiniteProgramOutput.output_formula_l K, at_formula_l,
    parameters_pushBound_l, parameters_empty_l, SecondOrderObjectSyntax.member_m, Arguments.eval,
    Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro η hBase hC hω he hInitial hw hv hTags hFunctional hn hAgree y
  exact reading_congr_l K φ η B C ω w N v M Q e t₀ t₁ t₂ a n k
    hBase hC (SecondOrderOmega.unique_l h𝒩 hω K.omega_spec) he hInitial hw hv hTags hFunctional
      ((SecondOrderOmega.unique_l h𝒩 hω K.omega_spec) ▸ hn) hAgree y

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w N v M Q e t₀ t₁ t₂ a n k : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B C ω w N v M Q e t₀ t₁ t₂ a n k)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ h𝒩 => models_l h𝒩 φ B C ω w N v M Q e t₀ t₁ t₂ a n k)

#print axioms trace_transfer_l
#print axioms reading_congr_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramPrefix
