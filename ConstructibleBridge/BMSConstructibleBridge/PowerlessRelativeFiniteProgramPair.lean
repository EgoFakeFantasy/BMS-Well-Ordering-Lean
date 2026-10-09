import BMSConstructibleBridge.PowerlessRelativeFiniteProgramJointRead

/-! # 同一程序的两个输出有真实配对程序

先证明两个读数可在同一末态读取，再构造父坐标对及配对指令，
取得新的 Class 程序词和实际有序对输出。本模块保留同词接口；
任意两词的输出配对由 `PairClosure` 经内部拼接及父坐标平移取得。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramPair

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
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
private abbrev up₅ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up₂ (up₃ t)

def result_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w n Q e t₀ t₁ t₂ a k x l z : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <|
    let S : Term ℒ [.set, .set, .set, .set, .set] Δ .set :=
      .bvar (.there (.there (.there (.there .here))))
    let v := .bvar (.there (.there (.there .here)))
    let q := .bvar (.there (.there .here))
    let y := .bvar (.there .here)
    let p := .bvar .here
    .conj (SecondOrderObjectSyntax.ordered_m (up₅ x) (up₅ z) y) <|
      .conj (SecondOrderObjectSyntax.ordered_m (up₅ k) (up₅ l) p) <|
        .conj (SecondOrderObjectSyntax.ordered_m (up₅ t₂) p q) <|
          .conj (PowerlessRelativeFiniteProgramWordAppend.append_m
            (up₅ B) (up₅ w) (up₅ n) (up₅ Q) q S v)
            (PowerlessRelativeFiniteProgramBoundRun.run_m φ
              (up₅ B) (up₅ C) (up₅ ω) v (up₅ e) (up₅ t₀) (up₅ t₁) (up₅ t₂)
                (up₅ a) S (up₅ n) y)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem exists_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B C ω w n Q e t₀ t₁ t₂ a k x l z : Term ℒ [] Δ .set)
    (hBase : ∀ y, mem_l hℳ y (B.eval η) → ∀ u, mem_l hℳ u y → mem_l hℳ u (B.eval η))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η))
    (hω : ω.eval η = K.omega) (he : ∀ y, ¬mem_l hℳ y (e.eval η))
    (hInitial : PowerlessRelativeFiniteProgramStep.record_l (e.eval η) (e.eval η) (e.eval η) (a.eval η))
    (hwC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (w.eval η))
    (hQC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (Q.eval η))
    (hw : map_l (ℳ := 𝒱) (w.eval η) (n.eval η) (Q.eval η))
    (hTags : t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η)
    (hFunctional : functional_l φ η (B.eval η)) (hn : mem_l hℳ (n.eval η) K.omega)
    (hAlphabet : ∀ q, mem_l hℳ q (Q.eval η) ↔
      PowerlessRelativeFiniteProgramAlphabet.instruction_l (C.eval η) (ω.eval η)
        (t₀.eval η) (t₁.eval η) (t₂.eval η) q)
    (hRunX : run_l φ η (B.eval η) (C.eval η) (ω.eval η) (w.eval η) (e.eval η)
      (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (n.eval η) (k.eval η) (x.eval η))
    (hRunZ : run_l φ η (B.eval η) (C.eval η) (ω.eval η) (w.eval η) (e.eval η)
      (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (n.eval η) (l.eval η) (z.eval η)) :
    ∃ S v q y p, ordered_l (ℳ := 𝒱) (x.eval η) (z.eval η) y ∧
      ordered_l (ℳ := 𝒱) (k.eval η) (l.eval η) p ∧ ordered_l (ℳ := 𝒱) (t₂.eval η) p q ∧
        PowerlessRelativeFiniteProgramWordAppend.append_l
          (B.eval η) (w.eval η) (n.eval η) (Q.eval η) q S v ∧
            run_l φ η (B.eval η) (C.eval η) (ω.eval η) v (e.eval η)
              (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) S (n.eval η) y := by
  obtain ⟨S, D, F, s, E, f, hDC, hFC, hF, hs, hValid, hx, hz⟩ :=
    PowerlessRelativeFiniteProgramJointRead.joint_l K φ η B C ω w n Q e t₀ t₁ t₂ a k x l z
      hBase hC he hw hTags hFunctional hn hRunX hRunZ
  have hk := (SecondOrderFunctionProperties.value_mem_l hℳ hValid.2.2.2.2.2 hx).1
  have hl := (SecondOrderFunctionProperties.value_mem_l hℳ hValid.2.2.2.2.2 hz).1
  have hkω := SecondOrderOmegaTransitive.member_l hℳ (hω.symm ▸ K.omega_spec) (hω.symm ▸ hn) hk
  have hlω := SecondOrderOmegaTransitive.member_l hℳ (hω.symm ▸ K.omega_spec) (hω.symm ▸ hn) hl
  obtain ⟨p, hkl⟩ := SecondOrderPairObjects.ordered_exists_l hℳ (k.eval η) (l.eval η)
  obtain ⟨q, hqp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ (t₂.eval η) p
  obtain ⟨y, hxy⟩ := SecondOrderPairObjects.ordered_exists_l hℳ (x.eval η) (z.eval η)
  have hq := (hAlphabet q).mpr (Or.inr (Or.inr ⟨k.eval η, l.eval η, p, hkω, hlω, hkl, hqp⟩))
  have hComputed := (PowerlessRelativeFiniteProgramInstruction.pair_l φ η
    (q := q) (p := p) (k := k.eval η) (l := l.eval η) (x := x.eval η) (z := z.eval η) (y := y)
    hBase hC hValid.2.2.2.1 hValid.2.2.2.2.2 hTags hqp hkl hx hz).mpr hxy
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
    (up₂ B) (up₂ C) (up₂ ω) (up₂ w) (up₂ n) (up₂ Q) ρ σ (up₂ e)
      (up₂ t₀) (up₂ t₁) (up₂ t₂) (up₂ a)
    (by simpa only [hu] using hBase) (by simpa only [hu] using hC)
    (by simpa only [hu] using hω) (by simpa only [hu] using he)
    (by simpa only [hu] using hInitial) (by simpa only [hu] using hwC)
    (by simpa only [hu] using hValid.2.2.1) (by simpa only [hu] using hQC)
    (by simpa only [hu] using hw) (by simpa only [hu, hρ] using hq)
    (by simpa only [hu] using hTags) (by simpa only [hu, hParams] using hFunctional)
    (by simpa only [hu] using hn) (by simpa only [hu] using hDC)
    (by simpa only [hu] using hFC) (by simpa only [hu, hσ, hParams] using hF)
    (by simpa only [hu] using hs) (by simpa only [hu] using hValid)
    (by simpa only [hu, hρ, hParams] using hComputed)
  refine ⟨S, v, q, y, p, hxy, hkl, hqp, ?_, ?_⟩
  · simpa only [hu, hσ, hρ] using hAppend
  · simpa only [hu, hσ, hParams] using hNew

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w n Q e t₀ t₁ t₂ a k x l z : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B C) <|
      .imp (SecondOrderOmegaSyntax.omega_m ω) <|
        .imp (PowerlessDefinableFiniteTraceDerives.zero_m e) <|
          .imp (PowerlessRelativeFiniteProgramStep.record_m e e e a) <|
            .imp (PowerlessRelativeHierarchySyntax.class_m B w) <|
              .imp (PowerlessRelativeHierarchySyntax.class_m B Q) <|
                .imp (SecondOrderObjectSyntax.map_m w n Q) <|
                  .imp (tags_m t₀ t₁ t₂) <| .imp (functional_m φ B) <|
                    .imp (SecondOrderObjectSyntax.member_m n ω) <|
                      .imp (PowerlessRelativeFiniteProgramAlphabet.alphabet_m C ω t₀ t₁ t₂ Q) <|
                        .imp (PowerlessRelativeFiniteProgramBoundRun.run_m φ B C ω w e t₀ t₁ t₂ a n k x) <|
                          .imp (PowerlessRelativeFiniteProgramBoundRun.run_m φ B C ω w e t₀ t₁ t₂ a n l z)
                            (result_m φ B C ω w n Q e t₀ t₁ t₂ a k x l z)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w n Q e t₀ t₁ t₂ a k x l z : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B C ω w n Q e t₀ t₁ t₂ a k x l z)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w n Q e t₀ t₁ t₂ a k x l z : Term ℒ [] Δ .set) :
    (sentence_m φ B C ω w n Q e t₀ t₁ t₂ a k x l z).TrueIn
      (SecondOrderQuotient.structure_l h𝒩) := by
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
    map_formula_l, ordered_formula_l, at_formula_l,
    parameters_pushBound_l, parameters_empty_l, SecondOrderObjectSyntax.member_m,
    Arguments.eval, up₅, up₃, up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro η hBase hC hω he hInitial hwC hQC hw hTags hFunctional hn hAlphabet hRunX hRunZ
  exact exists_l K φ η B C ω w n Q e t₀ t₁ t₂ a k x l z hBase hC
    (SecondOrderOmega.unique_l h𝒩 hω K.omega_spec) he hInitial hwC hQC hw hTags hFunctional
      ((SecondOrderOmega.unique_l h𝒩 hω K.omega_spec) ▸ hn) hAlphabet hRunX hRunZ

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w n Q e t₀ t₁ t₂ a k x l z : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B C ω w n Q e t₀ t₁ t₂ a k x l z)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ h𝒩 => models_l h𝒩 φ B C ω w n Q e t₀ t₁ t₂ a k x l z)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramPair
