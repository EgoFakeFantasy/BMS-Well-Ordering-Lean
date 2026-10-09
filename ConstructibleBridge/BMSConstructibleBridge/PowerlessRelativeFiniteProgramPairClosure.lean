import BMSConstructibleBridge.PowerlessRelativeFiniteProgramBoundPair
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramConcatExistsRead

/-! # 任意两程序的实际输出对配对封闭

先构造同一拼接程序并保持两侧全部读数，再在其末端增加配对指令。
结论包含实际 Class 新词、内部自然数长度、有效输出坐标及真实 run；
不是仅证明有序对集合存在，也不假定整个程序求值像已成为集合。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramPairClosure

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
private abbrev up₄ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up₂ (up₂ t)

def result_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω e t₀ t₁ t₂ a Q x y : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <|
    let N : Term ℒ [.set, .set, .set, .set] Δ .set := .bvar (.there (.there (.there .here)))
    let v := .bvar (.there (.there .here))
    let i := .bvar (.there .here)
    let p := .bvar .here
    .conj (SecondOrderObjectSyntax.ordered_m (up₄ x) (up₄ y) p) <|
      .conj (SecondOrderObjectSyntax.member_m N (up₄ ω)) <|
        .conj (SecondOrderObjectSyntax.member_m i N) <|
          .conj (PowerlessRelativeHierarchySyntax.class_m (up₄ B) v) <|
            .conj (PowerlessRelativeHierarchySyntax.class_m (up₄ B) p) <|
              .conj (SecondOrderObjectSyntax.map_m v N (up₄ Q))
                (PowerlessRelativeFiniteProgramBoundRun.run_m φ
                  (up₄ B) (up₄ C) (up₄ ω) v (up₄ e) (up₄ t₀) (up₄ t₁) (up₄ t₂)
                    (up₄ a) N i p)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem exists_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B C ω e t₀ t₁ t₂ a n w m z Q k x l y : Term ℒ [] Δ .set)
    (hB : ∀ u, mem_l hℳ u (B.eval η) → ∀ v, mem_l hℳ v u → mem_l hℳ v (B.eval η))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η))
    (hω : SecondOrderOmega.omega_l hℳ (ω.eval η))
    (hωC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (ω.eval η))
    (hQ : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (Q.eval η))
    (he : ∀ u, ¬mem_l hℳ u (e.eval η))
    (ha : PowerlessRelativeFiniteProgramStep.record_l
      (e.eval η) (e.eval η) (e.eval η) (a.eval η))
    (ht : t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η)
    (hφ : functional_l φ η (B.eval η))
    (hQω : ∀ q, mem_l hℳ q (Q.eval η) ↔ PowerlessRelativeFiniteProgramAlphabet.instruction_l
      (C.eval η) (ω.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) q)
    (hn : mem_l hℳ (n.eval η) (ω.eval η)) (hm : mem_l hℳ (m.eval η) (ω.eval η))
    (hw : map_l (ℳ := 𝒱) (w.eval η) (n.eval η) (Q.eval η))
    (hz : map_l (ℳ := 𝒱) (z.eval η) (m.eval η) (Q.eval η))
    (hx : run_l φ η (B.eval η) (C.eval η) (ω.eval η) (w.eval η) (e.eval η)
      (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (n.eval η) (k.eval η) (x.eval η))
    (hy : run_l φ η (B.eval η) (C.eval η) (ω.eval η) (z.eval η) (e.eval η)
      (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (m.eval η) (l.eval η) (y.eval η)) :
    ∃ N v i p, ordered_l (ℳ := 𝒱) (x.eval η) (y.eval η) p ∧
      mem_l hℳ N (ω.eval η) ∧ mem_l hℳ i N ∧
        PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) v ∧
          PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) p ∧
            map_l (ℳ := 𝒱) v N (Q.eval η) ∧
              run_l φ η (B.eval η) (C.eval η) (ω.eval η) v (e.eval η)
                (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) N i p := by
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  have hJoin := PowerlessRelativeFiniteProgramConcatExistsRead.exists_l K φ η
    B C ω e t₀ t₁ t₂ a n w m z Q hB hC hω hωC hQ he ha ht hφ hQω hn hm hw hz
  obtain ⟨A, r, c, v, hv, hRead⟩ :=
    (PowerlessRelativeFiniteProgramConcatExistsRead.result_formula_l K φ η
      B C ω e t₀ t₁ t₂ a n w m z Q).mp hJoin
  have hl : mem_l hℳ (l.eval η) (m.eval η) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hValid, hgy⟩ := hy
    exact (SecondOrderFunctionProperties.value_mem_l hℳ hValid.2.2.2.2.2 hgy).1
  have hlω := SecondOrderOmegaTransitive.member_l hℳ hω hm hl
  have hA := hv.2.2.1
  obtain ⟨i, hi, _⟩ := hA.2 (l.eval η) hlω
  have hcω := (SecondOrderFunctionProperties.value_mem_l hℳ hA hv.2.2.2.2.1).2
  have hx' := hRead.1 (k.eval η) (x.eval η) hx
  have hy' := hRead.2 (l.eval η) i (y.eval η) hi.2 hy
  let ξ : Env 𝒱 [.set, .set, .set] Δ := ((η.pushBound c).pushBound v).pushBound i
  let σ : Term ℒ [.set, .set, .set] Δ .set := .bvar (.there (.there .here))
  let ν : Term ℒ [.set, .set, .set] Δ .set := .bvar (.there .here)
  let ι : Term ℒ [.set, .set, .set] Δ .set := .bvar .here
  have hu (t : Term ℒ [] Δ .set) : (up₃ t).eval ξ = t.eval η := by
    simp only [up₃, up₂, up, Term.eval_weakenBound, ξ]
  have hσ : σ.eval ξ = c := rfl
  have hν : ν.eval ξ = v := rfl
  have hι : ι.eval ξ = i := rfl
  have hParams : parameters_l ξ = η := by
    simp only [ξ, parameters_pushBound_l, parameters_empty_l]
  obtain ⟨S, u, q, p, d, hxy, _, _, hu', hp⟩ :=
    PowerlessRelativeFiniteProgramBoundPair.exists_l K φ ξ
      (up₃ B) (up₃ C) (up₃ ω) ν σ (up₃ Q) (up₃ e) (up₃ t₀) (up₃ t₁) (up₃ t₂)
        (up₃ a) (up₃ k) (up₃ x) ι (up₃ y)
      (by simpa only [hu] using hB) (by simpa only [hu] using hC)
      (by simpa only [hu] using hωEq) (by simpa only [hu] using he)
      (by simpa only [hu] using ha) (by simpa only [hu, hν] using hv.2.2.2.2.2.2.1)
      (by simpa only [hu] using hQ) (by simpa only [hu, hν, hσ] using hv.2.2.2.2.2.2.2.1)
      (by simpa only [hu] using ht) (by simpa only [hu, hParams] using hφ)
      (by simpa only [hσ] using (hωEq ▸ hcω)) (by simpa only [hu] using hQω)
      (by simpa only [hu, hν, hσ, hParams] using hx')
      (by simpa only [hu, hν, hσ, hι, hParams] using hy')
  have hAppend : PowerlessRelativeFiniteProgramWordAppend.append_l
      (B.eval η) v c (Q.eval η) q S u := by
    simpa only [hu, hν, hσ] using hu'
  have hp' : run_l φ η (B.eval η) (C.eval η) (ω.eval η) u (e.eval η)
      (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) S c p := by
    simpa only [hu, hσ, hParams] using hp
  -- 长度是模型内部后继；仅在 Prop 中取得原数码，不使用 Type 选择。
  obtain ⟨j, hj⟩ := numberCode_surjective_l K ⟨c, hωEq ▸ hcω⟩
  have hj' : (numberCode_l K j).val = c := congrArg Subtype.val hj
  have hSuc : PowerlessNatural.successor_l (ℳ := 𝒱) c
      (numberCode_l K (SecondOrderModel.succ_l j)).val :=
    hj' ▸ PowerlessBMSQuotientSuccessor.successor_l K j
  have hS : S = (numberCode_l K (SecondOrderModel.succ_l j)).val :=
    SecondOrderQuotient.ext_l hℳ _ _ (fun t => (hAppend.2.2.1 t).trans (hSuc t).symm)
  have hSω : mem_l hℳ S (ω.eval η) :=
    hωEq.symm ▸ (hS.symm ▸ (numberCode_l K (SecondOrderModel.succ_l j)).property)
  have hcS : mem_l hℳ c S := (hAppend.2.2.1 c).mpr (Or.inr rfl)
  have hpC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) p := by
    obtain ⟨_, _, _, _, E, g, _, _, _, _, hValid, hgp⟩ := hp'
    exact PowerlessRelativeClassCorrespondence.transitive_l hℳ hB hValid.2.2.2.1
      (SecondOrderFunctionProperties.value_mem_l hℳ hValid.2.2.2.2.2 hgp).2
  refine ⟨S, u, c, p, ?_, hSω, hcS, hAppend.2.1, hpC, hAppend.2.2.2.1, hp'⟩
  simpa only [hu] using hxy

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω e t₀ t₁ t₂ a n w m z Q k x l y : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
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
                          .imp (SecondOrderObjectSyntax.map_m z m Q) <|
                            .imp (PowerlessRelativeFiniteProgramBoundRun.run_m φ B C ω w e t₀ t₁ t₂ a n k x) <|
                              .imp (PowerlessRelativeFiniteProgramBoundRun.run_m φ B C ω z e t₀ t₁ t₂ a m l y)
                                (result_m φ B C ω e t₀ t₁ t₂ a Q x y)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω e t₀ t₁ t₂ a n w m z Q k x l y : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B C ω e t₀ t₁ t₂ a n w m z Q k x l y)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω e t₀ t₁ t₂ a n w m z Q k x l y : Term ℒ [] Δ .set) :
    (sentence_m φ B C ω e t₀ t₁ t₂ a n w m z Q k x l y).TrueIn
      (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, result_m, PowerlessDefinableFiniteTraceDerives.zero_m,
    tags_m, functional_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeFiniteProgramStep.record_formula_l,
    PowerlessRelativeFiniteProgramAlphabet.alphabet_formula_l,
    PowerlessRelativeFiniteProgramBoundRun.run_formula_l K,
    map_formula_l, ordered_formula_l, at_formula_l, parameters_pushBound_l, parameters_empty_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up₄, up₂, up, Term.eval_weakenBound,
    Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro η hB hC hω hωC hQ he ha ht hφ hQω hn hm hw hz hx hy
  exact exists_l K φ η B C ω e t₀ t₁ t₂ a n w m z Q k x l y
    hB hC hω hωC hQ he ha ht hφ hQω hn hm hw hz hx hy

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω e t₀ t₁ t₂ a n w m z Q k x l y : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B C ω e t₀ t₁ t₂ a n w m z Q k x l y)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ h𝒩 => models_l h𝒩 φ B C ω e t₀ t₁ t₂ a n w m z Q k x l y)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramPairClosure
