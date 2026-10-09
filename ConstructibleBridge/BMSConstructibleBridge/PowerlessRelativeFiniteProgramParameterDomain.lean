import BMSConstructibleBridge.PowerlessRelativeClassParameterSeed
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramAlphabetEnumeration
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramDomainEnumeration

/-! # 从原有限参数族构造实际可数程序域

先构造同一个实际常量种子，再构造三类指令字母表和全部内部有限词，
最后枚举原码域 Seq(Q)×ω。结论真正存在量化 C、Q、S、P，不要求调用者
提供任何种子／字母表／码域枚举。仍只覆盖程序域准备，不替代实际见证
算子的构造、求值像闭包、凝聚、Collection 或 BMS 的最终对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramParameterDomain

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₄ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up₂ (up₂ t)

def conclusion_m {Δ : SortContext ℒ} (B ω t₀ t₁ t₂ : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <|
    let C := .bvar (.there (.there (.there .here)))
    let Q := .bvar (.there (.there .here))
    let S := .bvar (.there .here)
    let P := .bvar .here
    .conj (PowerlessRelativeHierarchySyntax.class_m (up₄ B) C) <|
      .conj (PowerlessRelativeHierarchySyntax.class_m (up₄ B) Q) <|
        .conj (PowerlessRelativeOrdinalCutoff.countable_m (up₄ B) (up₄ ω) C) <|
          .conj (SecondOrderObjectSyntax.member_m (up₄ B) C) <|
            .conj (ThirdOrderTheory.subset_m (up₄ ω) C) <|
              .conj (PowerlessRelativeClassParameterSeed.members_m Δ C (fun v => .fvar v)) <|
                .conj (PowerlessRelativeClassParameterSeed.bound_m (up₄ B) (up₄ ω) C) <|
                  .conj (PowerlessRelativeFiniteProgramAlphabet.alphabet_m C (up₄ ω)
                    (up₄ t₀) (up₄ t₁) (up₄ t₂) Q) <|
                    .conj (PowerlessRelativeFiniteProgramDomain.domain_m (up₄ B) (up₄ ω) Q S P)
                      (PowerlessRelativeOrdinalCutoff.countable_m (up₄ B) (up₄ ω) P)

def schema_m {Δ : SortContext ℒ} (B ω t₀ t₁ t₂ : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_m Δ B (fun v => .fvar v))
        (conclusion_m B ω t₀ t₁ t₂)

def sentence_m {Δ : SortContext ℒ} (B ω t₀ t₁ t₂ : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B ω t₀ t₁ t₂)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B ω t₀ t₁ t₂ : Term ℒ [] Δ .set) :
    (sentence_m B ω t₀ t₁ t₂).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hBase hω hParams
  have hBase' := (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ η B).mp hBase
  have hω' := (SecondOrderOmegaSyntax.omega_l hℳ η ω).mp hω
  have hParams' := (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_formula_l
    K Δ η B (fun v => .fvar v)).mp hParams
  have hTerm (t : Term ℒ [] Δ .set) :
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (t.eval η) := by
    match t with
    | .bvar v => nomatch v
    | .fvar v => exact hParams' _ v
    | .app f _ => nomatch f
  have hSeed := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
    (PowerlessRelativeClassParameterSeed.models_l hℳ B ω) η
  simp only [PowerlessRelativeClassParameterSeed.schema_m, Formula.satisfies] at hSeed
  have hSeed' := hSeed hBase hω
    ((PowerlessRelativeHierarchySemantics.class_formula_l K η B ω).mpr (hTerm ω)) hParams
  obtain ⟨C, G, hC, hG, hMap, hOnto, hωC, hb, hMembers, hBound⟩ :=
    (PowerlessRelativeClassParameterSeed.conclusion_l K η B ω).mp hSeed'
  let O : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) := ⟨ω.eval η, hTerm ω⟩
  let A : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) := ⟨C, hC⟩
  let F : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) := ⟨G, hG⟩
  let a : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) := ⟨t₀.eval η, hTerm t₀⟩
  let b : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) := ⟨t₁.eval η, hTerm t₁⟩
  let c : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) := ⟨t₂.eval η, hTerm t₂⟩
  have hCountC := PowerlessRelativeClassOntoCountability.countable_l (hBase := hBase')
    K hω' hC hG hMap hOnto
  obtain ⟨Q, hQ, hAlphabet⟩ := PowerlessRelativeFiniteProgramAlphabet.exists_l hBase'
    hC (hTerm ω) a.property b.property c.property
  let D : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) := ⟨Q, hQ⟩
  obtain ⟨E, hE, hEOnto⟩ := PowerlessRelativeFiniteProgramAlphabetEnumeration.exists_l
    (hBase := hBase') (t₀ := a) (t₁ := b) (t₂ := c) (Q := D)
    ((PowerlessRelativeClassOmegaAbsolute.omega_l O).mpr hω')
    ((PowerlessRelativeClassFunctionAbsolute.map_l F O A).mpr hMap)
    ((PowerlessRelativeClassFunctionAbsolute.onto_l F O A).mpr hOnto) hAlphabet
  obtain ⟨S, P, hDomain⟩ := PowerlessRelativeFiniteProgramDomain.exists_l hBase' hω' (hTerm ω) hQ
  obtain ⟨_, _, _, hCountP⟩ := PowerlessRelativeFiniteProgramDomainEnumeration.exists_l
    (hBase := hBase') K ((PowerlessRelativeClassOmegaAbsolute.omega_l O).mpr hω') hE hEOnto hDomain
  simp only [conclusion_m, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeOrdinalCutoff.countable_formula_l K,
    PowerlessRelativeClassParameterSeed.members_formula_l,
    PowerlessRelativeClassParameterSeed.bound_formula_l K,
    PowerlessRelativeFiniteProgramAlphabet.alphabet_formula_l,
    PowerlessRelativeFiniteProgramDomain.domain_formula_l K,
    subset_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval,
    up₄, up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  exact ⟨C, Q, S, P, hC, hQ, hCountC, hb, hωC, hMembers, hBound, hAlphabet, hDomain, hCountP⟩

theorem derives_m {Δ : SortContext ℒ} (B ω t₀ t₁ t₂ : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m B ω t₀ t₁ t₂)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 B ω t₀ t₁ t₂)

#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramParameterDomain
