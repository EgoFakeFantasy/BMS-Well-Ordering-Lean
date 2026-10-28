import BMSConstructibleBridge.PowerlessRelativeFiniteProgramExecutionAppend

/-! # 追加指令的实际程序读数

追加一步精确保留原历史，最后存储坐标的值就是该指令在原存储图上的
计算值。结论给真实 run，而非无见证时的缺省 output；原计算关系同时
覆盖常量、调用、配对及非法指令的明确缺省规则。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramAppendRead

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeFiniteProgramExecution (relation_m relation_formula_l)
open PowerlessRelativeFiniteProgramInstruction (functional_l functional_m tags_m computed_l computed_m)
open PowerlessRelativeFiniteProgramStep (valid_l valid_m)
open PowerlessDefinableFiniteTrace (trace_l trace_m trace_formula_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_pushBound_l parameters_empty_l at_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem reading_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B C ω w n Q q v S e t₀ t₁ t₂ a : Term ℒ [] Δ .set)
    {D F s E f y : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x (B.eval η) → ∀ z, mem_l hℳ z x → mem_l hℳ z (B.eval η))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η))
    (hω : ω.eval η = K.omega) (he : ∀ x, ¬mem_l hℳ x (e.eval η))
    (hInitial : PowerlessRelativeFiniteProgramStep.record_l (e.eval η) (e.eval η) (e.eval η) (a.eval η))
    (hw : map_l (ℳ := 𝒱) (w.eval η) (n.eval η) (Q.eval η))
    (hTags : t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η)
    (hFunctional : functional_l φ η (B.eval η)) (hn : mem_l hℳ (n.eval η) K.omega)
    (hAppend : PowerlessRelativeFiniteProgramWordAppend.append_l
      (B.eval η) (w.eval η) (n.eval η) (Q.eval η) (q.eval η) (S.eval η) (v.eval η))
    (hDC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) D)
    (hFC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) F)
    (hF : trace_l (relation_m φ B C ω w e t₀ t₁ t₂) η
      (e.eval η) (a.eval η) (n.eval η) (S.eval η) D F)
    (hs : value_l (ℳ := 𝒱) F (n.eval η) s)
    (hValid : valid_l (B.eval η) (ω.eval η) (n.eval η) E f s)
    (hy : computed_l φ η (B.eval η) (C.eval η) f
      (t₀.eval η) (t₁.eval η) (t₂.eval η) (q.eval η) y) :
    PowerlessRelativeFiniteProgramOutput.run_l (relation_m φ B C ω v e t₀ t₁ t₂) η
      (B.eval η) (ω.eval η) (e.eval η) (a.eval η) (S.eval η) (n.eval η) y := by
  obtain ⟨T, A, H, t, hAC, hHC, hTrace, ht, hRead⟩ :=
    PowerlessRelativeFiniteProgramExecutionAppend.exists_l K φ η
      B C ω w n Q q v S e t₀ t₁ t₂ a
      hBase hC hω he hInitial hw hTags hFunctional hn hAppend hDC hFC hF
  have hsH := (hRead (n.eval η) s).mpr (Or.inl hs)
  have hnS := (hAppend.2.2.1 (n.eval η)).mpr (Or.inr rfl)
  have hStep := (relation_formula_l K φ η B C ω v e t₀ t₁ t₂ s t).mp
    (hTrace.2.2.2 (n.eval η) (S.eval η) s t hnS hAppend.2.2.1 hsH ht)
  obtain ⟨r, U, A', g, hr, hStore, hU, hValid'⟩ :=
    PowerlessRelativeFiniteProgramStep.transition_l K φ η
      (e := e.eval η) hBase hC hAppend.2.2.2.1 hTags hFunctional
        (hω ▸ hValid) (hω ▸ hStep)
  obtain ⟨r₀, _, hCurrent⟩ := PowerlessRelativeFiniteProgramStep.current_exists_unique_l
    hAppend.2.2.2.1 (e.eval η) (n.eval η)
  have hrq : r = q.eval η := (hCurrent r hr).trans
    (hCurrent (q.eval η) (Or.inl (PowerlessRelativeFiniteProgramWordAppend.last_l hAppend))).symm
  have hUS : U = S.eval η := SecondOrderQuotient.ext_l hℳ U (S.eval η)
    (fun x => (hU x).trans (hAppend.2.2.1 x).symm)
  subst U
  rw [hrq] at hStore
  obtain ⟨z, hz, _, _, _, _, _, _, hValues⟩ := hStore
  obtain ⟨z₀, _, hComputed⟩ := PowerlessRelativeFiniteProgramInstruction.exists_unique_l
    φ η hBase hC hValid.2.2.2.1 hValid.2.2.2.2.2 hTags hFunctional (q.eval η)
  have hzy : z = y := (hComputed z hz).trans (hComputed y hy).symm
  have hValue : value_l (ℳ := 𝒱) g (n.eval η) y :=
    (hValues (n.eval η) y).mpr (Or.inr ⟨rfl, hzy.symm⟩)
  exact ⟨T, A, H, t, A', g, hAC, hHC, hTrace, ht, hω.symm ▸ hValid', hValue⟩

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w n Q q v S e t₀ t₁ t₂ a D F s E f y : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B C) <|
      .imp (SecondOrderOmegaSyntax.omega_m ω) <|
        .imp (PowerlessDefinableFiniteTraceDerives.zero_m e) <|
          .imp (PowerlessRelativeFiniteProgramStep.record_m e e e a) <|
            .imp (SecondOrderObjectSyntax.map_m w n Q) <|
              .imp (tags_m t₀ t₁ t₂) <| .imp (functional_m φ B) <|
                .imp (SecondOrderObjectSyntax.member_m n ω) <|
                  .imp (PowerlessRelativeFiniteProgramWordAppend.append_m B w n Q q S v) <|
                    .imp (PowerlessRelativeHierarchySyntax.class_m B D) <|
                      .imp (PowerlessRelativeHierarchySyntax.class_m B F) <|
                        .imp (trace_m (relation_m φ B C ω w e t₀ t₁ t₂) e a n S D F) <|
                          .imp (SecondOrderObjectSyntax.value_m F n s) <|
                            .imp (valid_m B ω n E f s) <|
                              .imp (computed_m φ B C f t₀ t₁ t₂ q y)
                                (PowerlessRelativeFiniteProgramOutput.run_m
                                  (relation_m φ B C ω v e t₀ t₁ t₂) B ω e a S n y)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w n Q q v S e t₀ t₁ t₂ a D F s E f y : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B C ω w n Q q v S e t₀ t₁ t₂ a D F s E f y)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w n Q q v S e t₀ t₁ t₂ a D F s E f y : Term ℒ [] Δ .set) :
    (sentence_m φ B C ω w n Q q v S e t₀ t₁ t₂ a D F s E f y).TrueIn
      (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, PowerlessDefinableFiniteTraceDerives.zero_m,
    tags_m, functional_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeFiniteProgramStep.record_formula_l,
    PowerlessRelativeFiniteProgramWordAppend.append_formula_l K,
    PowerlessRelativeFiniteProgramStep.valid_formula_l K,
    PowerlessRelativeFiniteProgramInstruction.computed_formula_l K,
    PowerlessRelativeFiniteProgramOutput.run_formula_l K,
    trace_formula_l, map_formula_l, value_formula_l, at_formula_l,
    parameters_pushBound_l, parameters_empty_l, SecondOrderObjectSyntax.member_m,
    Arguments.eval, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro η hBase hC hω he hInitial hw hTags hFunctional hn hAppend hDC hFC hF hs hValid hy
  have hωEq := SecondOrderOmega.unique_l h𝒩 hω K.omega_spec
  exact reading_l K φ η B C ω w n Q q v S e t₀ t₁ t₂ a
    hBase hC hωEq he hInitial hw hTags hFunctional (hωEq ▸ hn)
      hAppend hDC hFC hF hs hValid hy

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w n Q q v S e t₀ t₁ t₂ a D F s E f y : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B C ω w n Q q v S e t₀ t₁ t₂ a D F s E f y)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ h𝒩 => models_l h𝒩 φ B C ω w n Q q v S e t₀ t₁ t₂ a D F s E f y)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramAppendRead
