import BMSConstructibleBridge.PowerlessRelativeFiniteProgramConcatBoundRead

/-! # 存在同时保留两侧全部真实输出的拼接程序

先存在量化同一加法图、重编号右词、总长度与总词，再全称量化
两侧输出坐标和值。因而新程序不依赖后来要读取的输出值；这正是
有限程序求值像闭包所需的拼接接口，仍不声称整个求值像已成集合。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramConcatExistsRead

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeFiniteProgramInstruction (functional_m functional_l tags_m)
open PowerlessRelativeFiniteProgramBoundRun (run_m run_formula_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_pushBound_l parameters_empty_l at_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)
private abbrev up₄ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up₂ (up₂ t)
private abbrev up₆ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up₃ (up₃ t)

def preserved_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω e t₀ t₁ t₂ a n w m z A c v : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj
    (.forallE .set <| .forallE .set <|
      let k : Term ℒ (.set :: .set :: Γ) Δ .set := .bvar (.there .here)
      let y := .bvar .here
      .imp (run_m φ (up₂ B) (up₂ C) (up₂ ω) (up₂ w) (up₂ e) (up₂ t₀) (up₂ t₁) (up₂ t₂)
        (up₂ a) (up₂ n) k y)
        (run_m φ (up₂ B) (up₂ C) (up₂ ω) (up₂ v) (up₂ e) (up₂ t₀) (up₂ t₁) (up₂ t₂)
          (up₂ a) (up₂ c) k y))
    (.forallE .set <| .forallE .set <| .forallE .set <|
      let k : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
      let l := .bvar (.there .here)
      let y := .bvar .here
      .imp (SecondOrderObjectSyntax.value_m (up₃ A) k l) <|
        .imp (run_m φ (up₃ B) (up₃ C) (up₃ ω) (up₃ z) (up₃ e) (up₃ t₀) (up₃ t₁) (up₃ t₂)
          (up₃ a) (up₃ m) k y)
          (run_m φ (up₃ B) (up₃ C) (up₃ ω) (up₃ v) (up₃ e) (up₃ t₀) (up₃ t₁) (up₃ t₂)
            (up₃ a) (up₃ c) l y))

def result_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω e t₀ t₁ t₂ a n w m z Q : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <|
    let A : Term ℒ [.set, .set, .set, .set] Δ .set := .bvar (.there (.there (.there .here)))
    let r := .bvar (.there (.there .here))
    let c := .bvar (.there .here)
    let v := .bvar .here
    .conj (PowerlessRelativeFiniteProgramConcat.joined_m (up₄ B) (up₄ C) (up₄ ω) (up₄ e)
      (up₄ t₀) (up₄ t₁) (up₄ t₂) (up₄ n) (up₄ w) (up₄ m) (up₄ z) (up₄ Q) A r c v)
      (preserved_m φ (up₄ B) (up₄ C) (up₄ ω) (up₄ e) (up₄ t₀) (up₄ t₁) (up₄ t₂)
        (up₄ a) (up₄ n) (up₄ w) (up₄ m) (up₄ z) A c v)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def preserved_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (B C ω e t₀ t₁ t₂ a n w m z A c v : type_l hℳ) : Prop :=
  (∀ k y, PowerlessRelativeFiniteProgramBoundOutput.run_l φ η B C ω w e t₀ t₁ t₂ a n k y →
    PowerlessRelativeFiniteProgramBoundOutput.run_l φ η B C ω v e t₀ t₁ t₂ a c k y) ∧
  (∀ k l y, value_l (ℳ := 𝒱) A k l →
    PowerlessRelativeFiniteProgramBoundOutput.run_l φ η B C ω z e t₀ t₁ t₂ a m k y →
      PowerlessRelativeFiniteProgramBoundOutput.run_l φ η B C ω v e t₀ t₁ t₂ a c l y)

theorem preserved_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B C ω e t₀ t₁ t₂ a n w m z A c v : Term ℒ Γ Δ .set) :
    (preserved_m φ B C ω e t₀ t₁ t₂ a n w m z A c v).satisfies η ↔
      preserved_l φ (PowerlessBMSQuotientSubsetImageDerives.parameters_l η)
        (B.eval η) (C.eval η) (ω.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η)
          (a.eval η) (n.eval η) (w.eval η) (m.eval η) (z.eval η) (A.eval η) (c.eval η) (v.eval η) := by
  simp only [preserved_m, preserved_l, Formula.satisfies, run_formula_l K, value_formula_l,
    parameters_pushBound_l, up₃, up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  rfl

theorem result_formula_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B C ω e t₀ t₁ t₂ a n w m z Q : Term ℒ [] Δ .set) :
    (result_m φ B C ω e t₀ t₁ t₂ a n w m z Q).satisfies η ↔
      ∃ A r c v, PowerlessRelativeFiniteProgramConcat.joined_l
        (B.eval η) (C.eval η) (ω.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η)
          (n.eval η) (w.eval η) (m.eval η) (z.eval η) (Q.eval η) A r c v ∧
            preserved_l φ η (B.eval η) (C.eval η) (ω.eval η) (e.eval η)
              (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η)
                (n.eval η) (w.eval η) (m.eval η) (z.eval η) A c v := by
  simp only [result_m, Formula.satisfies, PowerlessRelativeFiniteProgramConcat.joined_formula_l K,
    preserved_formula_l K, parameters_pushBound_l, parameters_empty_l,
    up₄, up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  rfl

theorem exists_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B C ω e t₀ t₁ t₂ a n w m z Q : Term ℒ [] Δ .set)
    (hBase : ∀ x, mem_l hℳ x (B.eval η) → ∀ y, mem_l hℳ y x → mem_l hℳ y (B.eval η))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η))
    (hω : SecondOrderOmega.omega_l hℳ (ω.eval η))
    (hωC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (ω.eval η))
    (hQC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (Q.eval η))
    (he : ∀ x, ¬mem_l hℳ x (e.eval η))
    (hInitial : PowerlessRelativeFiniteProgramStep.record_l
      (e.eval η) (e.eval η) (e.eval η) (a.eval η))
    (hTags : t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η)
    (hFunctional : functional_l φ η (B.eval η))
    (hAlphabet : ∀ q, mem_l hℳ q (Q.eval η) ↔ PowerlessRelativeFiniteProgramAlphabet.instruction_l
      (C.eval η) (ω.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) q)
    (hn : mem_l hℳ (n.eval η) (ω.eval η)) (hm : mem_l hℳ (m.eval η) (ω.eval η))
    (hw : map_l (ℳ := 𝒱) (w.eval η) (n.eval η) (Q.eval η))
    (hz : map_l (ℳ := 𝒱) (z.eval η) (m.eval η) (Q.eval η)) :
    (result_m φ B C ω e t₀ t₁ t₂ a n w m z Q).satisfies η := by
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  obtain ⟨A, r, c, v, hJoined⟩ := PowerlessRelativeFiniteProgramConcat.exists_l
    K hBase (hωEq ▸ hωC) hQC he hTags (hωEq ▸ hAlphabet) (hωEq ▸ hn) (hωEq ▸ hm) hw hz
  have hJoined' : PowerlessRelativeFiniteProgramConcat.joined_l
      (B.eval η) (C.eval η) (ω.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η)
        (n.eval η) (w.eval η) (m.eval η) (z.eval η) (Q.eval η) A r c v := hωEq.symm ▸ hJoined
  simp only [result_m, preserved_m, Formula.satisfies,
    PowerlessRelativeFiniteProgramConcat.joined_formula_l K, run_formula_l K, value_formula_l,
    parameters_pushBound_l, parameters_empty_l, up₄, up₃, up₂, up,
    Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  have hRead (k l y : type_l hℳ) := by
    let ξ : Env 𝒱 [.set, .set, .set, .set, .set, .set] Δ :=
      ((((((η.pushBound A).pushBound r).pushBound c).pushBound v).pushBound l).pushBound k)
    let t (s : Term ℒ [] Δ .set) := up₆ s
    let A' : Term ℒ [.set, .set, .set, .set, .set, .set] Δ .set :=
      .bvar (.there (.there (.there (.there (.there .here)))))
    let r' : Term ℒ [.set, .set, .set, .set, .set, .set] Δ .set :=
      .bvar (.there (.there (.there (.there .here))))
    let c' : Term ℒ [.set, .set, .set, .set, .set, .set] Δ .set := .bvar (.there (.there (.there .here)))
    let v' : Term ℒ [.set, .set, .set, .set, .set, .set] Δ .set := .bvar (.there (.there .here))
    let k' : Term ℒ [.set, .set, .set, .set, .set, .set] Δ .set := .bvar .here
    let l' : Term ℒ [.set, .set, .set, .set, .set, .set] Δ .set := .bvar (.there .here)
    have ht (s : Term ℒ [] Δ .set) : (t s).eval ξ = s.eval η := by
      simp only [t, up₆, up₃, up₂, up, Term.eval_weakenBound, ξ]
    have hA' : A'.eval ξ = A := rfl
    have hr' : r'.eval ξ = r := rfl
    have hc' : c'.eval ξ = c := rfl
    have hv' : v'.eval ξ = v := rfl
    have hk' : k'.eval ξ = k := rfl
    have hl' : l'.eval ξ = l := rfl
    have hParameters : PowerlessBMSQuotientSubsetImageDerives.parameters_l ξ = η := by
      simp only [ξ, parameters_pushBound_l, parameters_empty_l]
    have h := PowerlessRelativeFiniteProgramConcatBoundRead.readings_l K φ ξ
      (t B) (t C) (t ω) (t e) (t t₀) (t t₁) (t t₂) (t a) (t n) (t w) (t m) (t z) (t Q)
        A' r' c' v' k' l'
      (by simpa only [ht] using hBase) (by simpa only [ht] using hC)
      (by simpa only [ht] using hω) (by simpa only [ht] using he)
      (by simpa only [ht] using hInitial) (by simpa only [ht] using hw)
      (by simpa only [ht] using hz) (by simpa only [ht] using hTags)
      (by simpa only [ht, hParameters] using hFunctional)
      (by simpa only [ht] using hn) (by simpa only [ht] using hm)
      (by simpa only [ht, hA', hr', hc', hv'] using hJoined') y
    simpa only [ht, hA', hr', hc', hv', hk', hl', hParameters] using h
  exact ⟨A, r, c, v, hJoined', (fun k y => (hRead k k y).1),
    (fun k l y => (hRead k l y).2)⟩

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω e t₀ t₁ t₂ a n w m z Q : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B C) <|
      .imp (SecondOrderOmegaSyntax.omega_m ω) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B ω) <|
          .imp (PowerlessRelativeHierarchySyntax.class_m B Q) <|
            .imp (PowerlessDefinableFiniteTraceDerives.zero_m e) <|
              .imp (PowerlessRelativeFiniteProgramStep.record_m e e e a) <|
                .imp (tags_m t₀ t₁ t₂) <| .imp (functional_m φ B) <|
                  .imp (PowerlessRelativeFiniteProgramAlphabet.alphabet_m C ω t₀ t₁ t₂ Q) <|
                    .imp (SecondOrderObjectSyntax.member_m n ω) <|
                      .imp (SecondOrderObjectSyntax.member_m m ω) <|
                        .imp (SecondOrderObjectSyntax.map_m w n Q) <|
                          .imp (SecondOrderObjectSyntax.map_m z m Q)
                            (result_m φ B C ω e t₀ t₁ t₂ a n w m z Q)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω e t₀ t₁ t₂ a n w m z Q : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B C ω e t₀ t₁ t₂ a n w m z Q)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (B C ω e t₀ t₁ t₂ a n w m z Q : Term ℒ [] Δ .set) :
    (sentence_m φ B C ω e t₀ t₁ t₂ a n w m z Q).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, PowerlessDefinableFiniteTraceDerives.zero_m, tags_m, functional_m,
    Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeFiniteProgramStep.record_formula_l, map_formula_l,
    PowerlessRelativeFiniteProgramAlphabet.alphabet_formula_l, at_formula_l,
    parameters_pushBound_l, parameters_empty_l, SecondOrderObjectSyntax.member_m,
    Arguments.eval, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro η hBase hC hω hωC hQC he hInitial hTags hFunctional hAlphabet hn hm hw hz
  exact exists_l K φ η B C ω e t₀ t₁ t₂ a n w m z Q
    hBase hC hω hωC hQC he hInitial hTags hFunctional hAlphabet hn hm hw hz

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω e t₀ t₁ t₂ a n w m z Q : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B C ω e t₀ t₁ t₂ a n w m z Q)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 φ B C ω e t₀ t₁ t₂ a n w m z Q)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramConcatExistsRead
