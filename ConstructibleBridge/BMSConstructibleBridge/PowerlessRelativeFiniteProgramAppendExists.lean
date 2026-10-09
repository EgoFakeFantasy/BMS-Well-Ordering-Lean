import BMSConstructibleBridge.PowerlessRelativeFiniteProgramAppendRead
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramBoundRun

/-! # 存在输出指定计算值的延长程序

在实际旧词和旧历史上追加一条指令，取得新的 Class 程序词及真实
输出。新词在对象句中存在量化，不再作为已给出的延拓前提。
原算子的输入／输出槽通过参数提升保持，未假定整个求值像存在。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramAppendExists

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeFiniteProgramExecution (relation_m relation_formula_l)
open PowerlessRelativeFiniteProgramInstruction (functional_l functional_m tags_m computed_l computed_m good_l)
open PowerlessRelativeFiniteProgramStep (valid_l valid_m)
open PowerlessDefinableFiniteTrace (trace_l trace_m trace_formula_l lift_m lift_formula_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_pushBound_l parameters_empty_l at_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def result_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w n Q q S e t₀ t₁ t₂ a y : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .existsE .set <|
    .conj (PowerlessRelativeFiniteProgramWordAppend.append_m
      (up B) (up w) (up n) (up Q) (up q) (up S) (.bvar .here))
      (PowerlessRelativeFiniteProgramBoundRun.run_m φ
        (up B) (up C) (up ω) (.bvar .here) (up e) (up t₀) (up t₁) (up t₂)
          (up a) (up S) (up n) (up y))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem exists_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B C ω w n Q q S e t₀ t₁ t₂ a : Term ℒ [] Δ .set)
    {D F s E f y : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x (B.eval η) → ∀ z, mem_l hℳ z x → mem_l hℳ z (B.eval η))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η))
    (hω : ω.eval η = K.omega) (he : ∀ x, ¬mem_l hℳ x (e.eval η))
    (hInitial : PowerlessRelativeFiniteProgramStep.record_l (e.eval η) (e.eval η) (e.eval η) (a.eval η))
    (hwC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (w.eval η))
    (hnC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (n.eval η))
    (hQC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (Q.eval η))
    (hw : map_l (ℳ := 𝒱) (w.eval η) (n.eval η) (Q.eval η))
    (hq : mem_l hℳ (q.eval η) (Q.eval η))
    (hTags : t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η)
    (hFunctional : functional_l φ η (B.eval η)) (hn : mem_l hℳ (n.eval η) K.omega)
    (hDC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) D)
    (hFC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) F)
    (hF : trace_l (relation_m φ B C ω w e t₀ t₁ t₂) η
      (e.eval η) (a.eval η) (n.eval η) (S.eval η) D F)
    (hs : value_l (ℳ := 𝒱) F (n.eval η) s)
    (hValid : valid_l (B.eval η) (ω.eval η) (n.eval η) E f s)
    (hy : computed_l φ η (B.eval η) (C.eval η) f
      (t₀.eval η) (t₁.eval η) (t₂.eval η) (q.eval η) y) :
    ∃ v, PowerlessRelativeFiniteProgramWordAppend.append_l
      (B.eval η) (w.eval η) (n.eval η) (Q.eval η) (q.eval η) (S.eval η) v ∧
        PowerlessRelativeFiniteProgramBoundOutput.run_l φ η
          (B.eval η) (C.eval η) (ω.eval η) v (e.eval η)
            (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (S.eval η) (n.eval η) y := by
  obtain ⟨T, v, hAppend, _, _⟩ := PowerlessRelativeFiniteProgramWordAppend.exists_l
    hBase hwC hnC hQC hw hq
  have hTS : T = S.eval η := SecondOrderQuotient.ext_l hℳ T (S.eval η)
    (fun x => (hAppend.2.2.1 x).trans (hF.1 x).symm)
  subst T
  let ξ : Env 𝒱 [] (.set :: Δ) := η.pushFree v
  let φ' := lift_m φ
  let u (t : Term ℒ [] Δ .set) := t.weakenFree SetTheory.SetSort.set
  let ν : Term ℒ [] (.set :: Δ) .set := .fvar .here
  have hu (t : Term ℒ [] Δ .set) : (u t).eval ξ = t.eval η := by
    simp only [u, ξ, Term.eval_weakenFree]
  have hν : ν.eval ξ = v := rfl
  have hFunctional' : functional_l φ' ξ (B.eval η) := by
    simpa only [φ', ξ, functional_l, lift_formula_l] using hFunctional
  have hy' : computed_l φ' ξ (B.eval η) (C.eval η) f
      (t₀.eval η) (t₁.eval η) (t₂.eval η) (q.eval η) y := by
    simpa only [φ', ξ, computed_l, good_l, lift_formula_l] using hy
  have hF' : trace_l (relation_m φ' (u B) (u C) (u ω) (u w) (u e) (u t₀) (u t₁) (u t₂)) ξ
      (e.eval η) (a.eval η) (n.eval η) (S.eval η) D F := by
    simpa only [φ', ξ, u, Term.eval_weakenFree, trace_l, relation_formula_l K,
      PowerlessRelativeFiniteProgramStep.step_l, PowerlessRelativeFiniteProgramStep.good_l,
      PowerlessRelativeFiniteProgramStore.store_l, computed_l, good_l, lift_formula_l] using hF
  have hRun := PowerlessRelativeFiniteProgramAppendRead.reading_l K φ' ξ
    (u B) (u C) (u ω) (u w) (u n) (u Q) (u q) ν (u S) (u e) (u t₀) (u t₁) (u t₂) (u a)
    (by simpa only [hu] using hBase) (by simpa only [hu] using hC)
    (by simpa only [hu] using hω) (by simpa only [hu] using he)
    (by simpa only [hu] using hInitial) (by simpa only [hu] using hw)
    (by simpa only [hu] using hTags) (by simpa only [hu] using hFunctional')
    (by simpa only [hu] using hn) (by simpa only [hu, hν] using hAppend)
    (by simpa only [hu] using hDC) (by simpa only [hu] using hFC)
    (by simpa only [hu] using hF') (by simpa only [hu] using hs)
    (by simpa only [hu] using hValid) (by simpa only [hu] using hy')
  have hNative := (PowerlessRelativeFiniteProgramBoundRun.native_l K φ' ξ
    (u B) (u C) (u ω) ν (u e) (u t₀) (u t₁) (u t₂) (u a) (u S) (u n) y).mp hRun
  refine ⟨v, hAppend, ?_⟩
  simpa only [PowerlessRelativeFiniteProgramBoundOutput.run_l,
    PowerlessRelativeFiniteProgramStep.step_l, PowerlessRelativeFiniteProgramStep.good_l,
    PowerlessRelativeFiniteProgramStore.store_l, computed_l, good_l,
    hu, hν, φ', ξ, lift_formula_l] using hNative

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w n Q q S e t₀ t₁ t₂ a D F s E f y : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B C) <|
      .imp (SecondOrderOmegaSyntax.omega_m ω) <|
        .imp (PowerlessDefinableFiniteTraceDerives.zero_m e) <|
          .imp (PowerlessRelativeFiniteProgramStep.record_m e e e a) <|
            .imp (PowerlessRelativeHierarchySyntax.class_m B w) <|
              .imp (PowerlessRelativeHierarchySyntax.class_m B n) <|
                .imp (PowerlessRelativeHierarchySyntax.class_m B Q) <|
                  .imp (SecondOrderObjectSyntax.map_m w n Q) <|
                    .imp (SecondOrderObjectSyntax.member_m q Q) <|
                      .imp (tags_m t₀ t₁ t₂) <| .imp (functional_m φ B) <|
                        .imp (SecondOrderObjectSyntax.member_m n ω) <|
                          .imp (PowerlessRelativeHierarchySyntax.class_m B D) <|
                            .imp (PowerlessRelativeHierarchySyntax.class_m B F) <|
                              .imp (trace_m (relation_m φ B C ω w e t₀ t₁ t₂) e a n S D F) <|
                                .imp (SecondOrderObjectSyntax.value_m F n s) <|
                                  .imp (valid_m B ω n E f s) <|
                                    .imp (computed_m φ B C f t₀ t₁ t₂ q y)
                                      (result_m φ B C ω w n Q q S e t₀ t₁ t₂ a y)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w n Q q S e t₀ t₁ t₂ a D F s E f y : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B C ω w n Q q S e t₀ t₁ t₂ a D F s E f y)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w n Q q S e t₀ t₁ t₂ a D F s E f y : Term ℒ [] Δ .set) :
    (sentence_m φ B C ω w n Q q S e t₀ t₁ t₂ a D F s E f y).TrueIn
      (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, result_m, PowerlessDefinableFiniteTraceDerives.zero_m,
    tags_m, functional_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeFiniteProgramStep.record_formula_l,
    PowerlessRelativeFiniteProgramWordAppend.append_formula_l K,
    PowerlessRelativeFiniteProgramStep.valid_formula_l K,
    PowerlessRelativeFiniteProgramInstruction.computed_formula_l K,
    PowerlessRelativeFiniteProgramBoundRun.run_formula_l K,
    trace_formula_l, map_formula_l, value_formula_l, at_formula_l,
    parameters_pushBound_l, parameters_empty_l, SecondOrderObjectSyntax.member_m,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro η hBase hC hω he hInitial hwC hnC hQC hw hq hTags hFunctional hn hDC hFC hF hs hValid hy
  have hωEq := SecondOrderOmega.unique_l h𝒩 hω K.omega_spec
  exact exists_l K φ η B C ω w n Q q S e t₀ t₁ t₂ a
    hBase hC hωEq he hInitial hwC hnC hQC hw hq hTags hFunctional (hωEq ▸ hn)
      hDC hFC hF hs hValid hy

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w n Q q S e t₀ t₁ t₂ a D F s E f y : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B C ω w n Q q S e t₀ t₁ t₂ a D F s E f y)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ h𝒩 => models_l h𝒩 φ B C ω w n Q q S e t₀ t₁ t₂ a D F s E f y)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramAppendExists
