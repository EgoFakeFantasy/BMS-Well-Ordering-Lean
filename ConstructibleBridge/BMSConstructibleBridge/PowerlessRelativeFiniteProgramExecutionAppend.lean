import BMSConstructibleBridge.PowerlessRelativeFiniteProgramWordAppend

/-! # 延长指令词时保留同一前缀历史并执行新指令

先将旧历史传给新词，再使用已验证的通用历史延拓定理加入唯一
新状态。新图精确保留全部旧状态，不以重新取得任意历史替代图保持。
新增一步来自原状态转移；具体常量／调用／配对读数另行接入。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramExecutionAppend

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeFiniteProgramExecution (relation_m relation_formula_l)
open PowerlessRelativeFiniteProgramInstruction (functional_l functional_m tags_m)
open PowerlessDefinableFiniteTrace (trace_l trace_m trace_formula_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_pushBound_l parameters_empty_l at_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₄ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up₂ (up₂ t)

def result_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω v e t₀ t₁ t₂ a S F : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  let ψ := relation_m φ B C ω v e t₀ t₁ t₂
  .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <|
    let T : Term ℒ [.set, .set, .set, .set] Δ .set := .bvar (.there (.there (.there .here)))
    let A := .bvar (.there (.there .here))
    let H := .bvar (.there .here)
    let t := .bvar .here
    .conj (PowerlessRelativeHierarchySyntax.class_m (up₄ B) A) <|
      .conj (PowerlessRelativeHierarchySyntax.class_m (up₄ B) H) <|
        .conj (trace_m ψ (up₄ e) (up₄ a) (up₄ S) T A H) <|
          .conj (SecondOrderObjectSyntax.value_m H (up₄ S) t)
            (SecondOrderFunctionAppendDerives.reading_m (up₄ F) (up₄ S) t H)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem exists_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B C ω w n Q q v S e t₀ t₁ t₂ a : Term ℒ [] Δ .set) {D F : type_l hℳ}
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
      (e.eval η) (a.eval η) (n.eval η) (S.eval η) D F) :
    ∃ T A H t, PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) A ∧
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) H ∧
        trace_l (relation_m φ B C ω v e t₀ t₁ t₂) η
          (e.eval η) (a.eval η) (S.eval η) T A H ∧ value_l (ℳ := 𝒱) H (S.eval η) t ∧
          ∀ i x, value_l (ℳ := 𝒱) H i x ↔ value_l (ℳ := 𝒱) F i x ∨ i = S.eval η ∧ x = t := by
  have hOld := PowerlessRelativeFiniteProgramPrefix.trace_transfer_l K φ η
    B C ω w n Q v e t₀ t₁ t₂ a n hBase hC hω he hInitial hw hTags hFunctional hn
      (PowerlessRelativeFiniteProgramWordAppend.agreement_l hAppend) hF
  obtain ⟨s, hs, _⟩ := hF.2.1.2 (n.eval η) ((hF.1 (n.eval η)).mpr (Or.inr rfl))
  obtain ⟨t, ht, _⟩ := PowerlessRelativeFiniteProgramStep.exists_unique_l φ η
    (e := e.eval η) hBase hC hAppend.2.2.2.1 hTags hFunctional s
  obtain ⟨T, A, H, _, hAC, hHC, hT, _, hH, hRead⟩ :=
    PowerlessRelativeClassFunctionAppend.exists_l hBase hFC hAppend.1 hDC hAppend.1 ht.1 hF.2.1
      (fun hSS => SecondOrderNaturalCases.asymmetry_l hℳ hSS hSS)
  have hStep := (relation_formula_l K φ η B C ω v e t₀ t₁ t₂ s t).mpr ht
  have hTrace := PowerlessDefinableFiniteTrace.extension_l K
    (relation_m φ B C ω v e t₀ t₁ t₂) η
      (n := n.eval η) (g := H) (T := T) (E := A) hn hOld hH hT hRead hs.2 hStep
  exact ⟨T, A, H, t, hAC, hHC, hTrace, (hRead (S.eval η) t).mpr (Or.inr ⟨rfl, rfl⟩), hRead⟩

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w n Q q v S e t₀ t₁ t₂ a D F : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
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
                        .imp (trace_m (relation_m φ B C ω w e t₀ t₁ t₂) e a n S D F)
                          (result_m φ B C ω v e t₀ t₁ t₂ a S F)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w n Q q v S e t₀ t₁ t₂ a D F : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B C ω w n Q q v S e t₀ t₁ t₂ a D F)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w n Q q v S e t₀ t₁ t₂ a D F : Term ℒ [] Δ .set) :
    (sentence_m φ B C ω w n Q q v S e t₀ t₁ t₂ a D F).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, result_m, SecondOrderFunctionAppendDerives.reading_m,
    PowerlessDefinableFiniteTraceDerives.zero_m, tags_m, functional_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeFiniteProgramStep.record_formula_l,
    PowerlessRelativeFiniteProgramWordAppend.append_formula_l K,
    trace_formula_l, map_formula_l, value_formula_l, at_formula_l,
    parameters_pushBound_l, parameters_empty_l, SecondOrderObjectSyntax.member_m, Arguments.eval,
    up₄, up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro η hBase hC hω he hInitial hw hTags hFunctional hn hAppend hDC hFC hF
  have hωEq := SecondOrderOmega.unique_l h𝒩 hω K.omega_spec
  exact exists_l K φ η B C ω w n Q q v S e t₀ t₁ t₂ a
    hBase hC hωEq he hInitial hw hTags hFunctional (hωEq ▸ hn) hAppend hDC hFC hF

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w n Q q v S e t₀ t₁ t₂ a D F : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B C ω w n Q q v S e t₀ t₁ t₂ a D F)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ h𝒩 => models_l h𝒩 φ B C ω w n Q q v S e t₀ t₁ t₂ a D F)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramExecutionAppend
