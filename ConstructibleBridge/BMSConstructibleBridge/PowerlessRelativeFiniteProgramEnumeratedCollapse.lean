import BMSConstructibleBridge.PowerlessRelativeFiniteProgramNumberEvaluation
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramAlphabetEnumeration
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramDomainEnumeration

/-! # 原全程序枚举及求值隶属图的实际坍缩

纯隶属语言、原 Z₂。由原常量种子枚举、实际字母表和实际全码域，在
证明内产生 Class 满射 U:ω→P，再构造数码求值的精确隶属图及坍缩。
原算子公式不须 Δ₀，不收集其全部输出，也不预供 U。绑定 U 后保留
原算子参数和原求值 AST；有限元素性、Class 值域及凝聚仍须另证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramEnumeratedCollapse

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_pushBound_l parameters_empty_l at_m at_formula_l)
open PowerlessRelativeFiniteProgramInstruction (functional_l functional_m tags_m)
open PowerlessRelativeFiniteProgramNumberEvaluation (number_m number_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

private theorem opening_l {Δ : SortContext ℒ} (η : Env 𝒱 [] Δ) :
    PowerlessSourceOpening.env_l η = η := by
  apply Env.ext
  · intro s v; nomatch v
  · intro s v; rfl

/-- 新枚举仅占新增绑定槽，原自由参数、原求值正文逐字保留。 -/
theorem reading_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B C ω Q e t₀ t₁ t₂ a : Term ℒ [] Δ .set) (U n y : type_l hℳ) :
    (number_m φ (up B) (up C) (up ω) (up Q) (up e) (up t₀) (up t₁) (up t₂)
      (up a) (.bvar .here)).satisfies (((η.pushFree U).pushFree n).pushFree y) ↔
      number_l φ η (B.eval η) (C.eval η) (ω.eval η) (Q.eval η) (e.eval η)
        (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) U n y := by
  simpa only [PowerlessSourceOpening.push_l, opening_l, parameters_pushBound_l,
    parameters_empty_l, up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here] using
      PowerlessRelativeFiniteProgramNumberEvaluation.bound_formula_l K φ (η.pushBound U)
        (up B) (up C) (up ω) (up Q) (up e) (up t₀) (up t₁) (up t₂) (up a) (.bvar .here) n y

theorem exists_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B C ω Q e t₀ t₁ t₂ a G S P : Term ℒ [] Δ .set)
    (hBase : ∀ x, mem_l hℳ x (B.eval η) → ∀ z, mem_l hℳ z x → mem_l hℳ z (B.eval η))
    (hω : SecondOrderOmega.omega_l hℳ (ω.eval η))
    (hωC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (ω.eval η))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η))
    (hG : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (G.eval η))
    (h₀ : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (t₀.eval η))
    (h₁ : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (t₁.eval η))
    (h₂ : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (t₂.eval η))
    (hQ : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (Q.eval η))
    (hMap : map_l (ℳ := 𝒱) (G.eval η) (ω.eval η) (C.eval η))
    (hOnto : ∀ x, mem_l hℳ x (C.eval η) → ∃ n, mem_l hℳ n (ω.eval η) ∧
      value_l (ℳ := 𝒱) (G.eval η) n x)
    (hAlphabet : ∀ q, mem_l hℳ q (Q.eval η) ↔
      PowerlessRelativeFiniteProgramAlphabet.instruction_l (C.eval η) (ω.eval η)
        (t₀.eval η) (t₁.eval η) (t₂.eval η) q)
    (hDomain : PowerlessRelativeFiniteProgramDomain.domain_l (B.eval η) (ω.eval η)
      (Q.eval η) (S.eval η) (P.eval η))
    (he : ∀ x, ¬mem_l hℳ x (e.eval η))
    (hInitial : PowerlessRelativeFiniteProgramStep.record_l (e.eval η) (e.eval η) (e.eval η) (a.eval η))
    (hTags : t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η)
    (hFunctional : functional_l φ η (B.eval η)) :
    ∃ U A D T H : type_l hℳ,
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) U ∧
      map_l (ℳ := 𝒱) U (ω.eval η) (P.eval η) ∧
      (∀ p, mem_l hℳ p (P.eval η) → ∃ n, mem_l hℳ n (ω.eval η) ∧ value_l (ℳ := 𝒱) U n p) ∧
      (∀ n, mem_l hℳ n (ω.eval η) → ∃! y, number_l φ η (B.eval η) (C.eval η)
        (ω.eval η) (Q.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) U n y) ∧
      (∀ y, (∃ n, mem_l hℳ n (ω.eval η) ∧ number_l φ η (B.eval η) (C.eval η)
        (ω.eval η) (Q.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) U n y) ↔
          ∃ p, mem_l hℳ p (P.eval η) ∧ PowerlessRelativeFiniteProgramEvaluation.matrix_l
            false φ η (B.eval η) (C.eval η) (ω.eval η) (Q.eval η) (e.eval η)
              (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) p y) ∧
      PowerlessDefinableMembershipDiagram.spec_l
        (number_m φ (up B) (up C) (up ω) (up Q) (up e) (up t₀) (up t₁) (up t₂)
          (up a) (.bvar .here)) (η.pushFree U) (ω.eval η) A ∧
      PowerlessDefinableMembershipCollapse.domain_l (𝒩 := 𝒱) A D ∧
        SecondOrderCollapseFunction.spec_l hℳ A D T H := by
  let O : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) := ⟨ω.eval η, hωC⟩
  let C₀ : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) := ⟨C.eval η, hC⟩
  let G₀ : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) := ⟨G.eval η, hG⟩
  let Q₀ : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) := ⟨Q.eval η, hQ⟩
  let a₀ : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) := ⟨t₀.eval η, h₀⟩
  let a₁ : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) := ⟨t₁.eval η, h₁⟩
  let a₂ : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) := ⟨t₂.eval η, h₂⟩
  have hO := (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) O).mpr hω
  obtain ⟨F, hF, hFOnto⟩ := PowerlessRelativeFiniteProgramAlphabetEnumeration.exists_l
    (hBase := hBase) (t₀ := a₀) (t₁ := a₁) (t₂ := a₂) (Q := Q₀) hO
    ((PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) G₀ O C₀).mpr hMap)
    ((PowerlessRelativeClassFunctionAbsolute.onto_l (hBase := hBase) G₀ O C₀).mpr hOnto) hAlphabet
  obtain ⟨U, hU, hUOnto, _⟩ :=
    PowerlessRelativeFiniteProgramDomainEnumeration.exists_l (hBase := hBase) K hO hF hFOnto hDomain
  have hResult := PowerlessRelativeFiniteProgramNumberEvaluation.result_l K φ η B C ω Q e
    t₀ t₁ t₂ a U.val hBase hC hω he hInitial hTags hFunctional hDomain hU
  let ψ := number_m φ (up B) (up C) (up ω) (up Q) (up e) (up t₀) (up t₁) (up t₂)
    (up a) (.bvar .here)
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  have hUnique n y z (hn : mem_l hℳ n K.omega)
      (hy : ψ.satisfies (((η.pushFree U.val).pushFree n).pushFree y))
      (hz : ψ.satisfies (((η.pushFree U.val).pushFree n).pushFree z)) : y = z := by
    obtain ⟨v, _, hv⟩ := hResult n (by simpa only [hωEq] using hn)
    exact (hv y ((reading_l K φ η B C ω Q e t₀ t₁ t₂ a U.val n y).mp hy)).trans
      (hv z ((reading_l K φ η B C ω Q e t₀ t₁ t₂ a U.val n z).mp hz)).symm
  obtain ⟨A, D, T, H, hSpec, hField, hCollapse⟩ :=
    PowerlessDefinableMembershipCollapse.exists_l K ψ (η.pushFree U.val) hUnique
  exact ⟨U.val, A, D, T, H, U.property, hU, hUOnto, hResult,
    PowerlessRelativeFiniteProgramNumberEvaluation.range_l φ η hU hUOnto,
    by simpa only [hωEq] using hSpec, hField, hCollapse⟩

private def body_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a : Term ℒ [] Δ .set) : Formula ℒ [] (.set :: Δ) :=
  let ψ := number_m φ (up B) (up C) (up ω) (up Q) (up e) (up t₀) (up t₁) (up t₂)
    (up a) (.bvar .here)
  let O := ω.weakenFree SetTheory.SetSort.set
  .conj (.forallE .set <| .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (up O)) <|
    .existsE .set <| .conj (at_m ψ (.bvar (.there .here)) (.bvar .here)) <|
      .forallE .set <| .imp (at_m ψ (.bvar (.there (.there .here))) (.bvar .here))
        (.equal (.bvar .here) (.bvar (.there .here))))
    (PowerlessDefinableMembershipCollapse.conclusion_m ψ O)

def conclusion_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a P : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .existsE .set <| .conj (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here)) <|
    .conj (SecondOrderObjectSyntax.map_m (.bvar .here) (up ω) (up P)) <|
      .conj (PowerlessRelativeClassEnumerationSectionDerives.onto_m (.bvar .here) (up ω) (up P))
        (PowerlessSourceRebinding.formula_m (body_m φ B C ω Q e t₀ t₁ t₂ a))

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a G S P : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B ω) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B C) <|
          .imp (PowerlessRelativeHierarchySyntax.class_m B G) <|
            .imp (PowerlessRelativeHierarchySyntax.class_m B t₀) <|
              .imp (PowerlessRelativeHierarchySyntax.class_m B t₁) <|
                .imp (PowerlessRelativeHierarchySyntax.class_m B t₂) <|
                  .imp (PowerlessRelativeHierarchySyntax.class_m B Q) <|
                    .imp (SecondOrderObjectSyntax.map_m G ω C) <|
                      .imp (PowerlessRelativeClassEnumerationSectionDerives.onto_m G ω C) <|
                        .imp (PowerlessRelativeFiniteProgramAlphabet.alphabet_m C ω t₀ t₁ t₂ Q) <|
                          .imp (PowerlessRelativeFiniteProgramDomain.domain_m B ω Q S P) <|
                            .imp (PowerlessDefinableFiniteTraceDerives.zero_m e) <|
                              .imp (PowerlessRelativeFiniteProgramStep.record_m e e e a) <|
                                .imp (tags_m t₀ t₁ t₂) <| .imp (functional_m φ B)
                                  (conclusion_m φ B C ω Q e t₀ t₁ t₂ a P)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a G S P : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B C ω Q e t₀ t₁ t₂ a G S P)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (B C ω Q e t₀ t₁ t₂ a G S P : Term ℒ [] Δ .set) :
    (sentence_m φ B C ω Q e t₀ t₁ t₂ a G S P).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeHierarchySemantics.class_formula_l K,
    map_formula_l, PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l,
    PowerlessRelativeFiniteProgramAlphabet.alphabet_formula_l,
    PowerlessRelativeFiniteProgramDomain.domain_formula_l K,
    PowerlessDefinableFiniteTraceDerives.zero_m, PowerlessRelativeFiniteProgramStep.record_formula_l,
    tags_m, functional_m, at_formula_l, parameters_pushBound_l, parameters_empty_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro η hBase hω hωC hC hG h₀ h₁ h₂ hQ hMap hOnto hAlphabet hDomain he hInitial hTags hFunctional
  obtain ⟨U, A, D, T, H, hUC, hU, hUOnto, hResult, _, hSpec, hField, hCollapse⟩ :=
    exists_l K φ η B C ω Q e t₀ t₁ t₂ a G S P hBase hω hωC hC hG h₀ h₁ h₂ hQ
      hMap hOnto hAlphabet hDomain he hInitial hTags
      (by simpa only [functional_l, PowerlessRelativeClassCorrespondence.member_l,
        SecondOrderQuotient.structure_l, ThirdOrderSemantics.carrier_l] using hFunctional)
  simp only [conclusion_m, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.class_formula_l K, map_formula_l,
    PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l,
    up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here]
  refine ⟨U, hUC, hU, hUOnto, ?_⟩
  apply (PowerlessSourceRebinding.formula_l _ (η.pushBound U)).mpr
  simp only [PowerlessSourceOpening.push_l, opening_l, body_m,
    PowerlessDefinableMembershipCollapse.conclusion_m, Formula.satisfies, at_formula_l,
    PowerlessDefinableMembershipDiagram.spec_formula_l,
    PowerlessDefinableMembershipCollapse.domain_formula_l, SecondOrderCollapseSyntax.formula_l,
    parameters_pushBound_l, parameters_empty_l, up, Term.eval_weakenBound, Term.eval_weakenFree,
    Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there, reading_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  exact ⟨hResult, A, D, T, H, hSpec, hField, hCollapse⟩

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a G S P : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B C ω Q e t₀ t₁ t₂ a G S P)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ h𝒩 => models_l h𝒩 φ B C ω Q e t₀ t₁ t₂ a G S P)

#print axioms reading_l
#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramEnumeratedCollapse
