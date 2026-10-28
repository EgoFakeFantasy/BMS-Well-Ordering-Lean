import BMSConstructibleBridge.PowerlessRelativeFiniteProgramEvaluation
import BMSConstructibleBridge.PowerlessDefinableMembershipCollapse
import BMSConstructibleBridge.PowerlessRelativeClassEnumerationSectionDerives

/-! # 原有限程序的自然数求值与虚拟坍缩

纯隶属语言、原 Z₂。实际满射 U:ω→P 枚举原全部程序码域；输出正文
精确复用 matrix false，保留空词、全部输出坐标和原缺省值。原算子可以
是任意复杂公式，不预供求值全像集合。单值性来自同一 U 和原程序求值，
随后在证明内构造精确数码隶属图及实际坍缩。T/H 不预称 Class。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramNumberEvaluation

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_l parameters_pushBound_l parameters_empty_l at_m at_formula_l)
open PowerlessRelativeFiniteProgramInstruction (functional_l functional_m tags_m)
open PowerlessRelativeFiniteProgramEvaluation (matrix_m matrix_l matrix_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)

/-- 新自由槽依次为输出、自然数，其余仍是原算子参数。 -/
def number_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a U : Term ℒ Γ Δ .set) :
    Formula ℒ [] (.set :: .set :: (List.replicate Γ.length .set ++ Δ)) :=
  PowerlessSourceOpening.form_m (show Formula ℒ (.set :: .set :: Γ) Δ from
    .existsE .set <| .conj
      (SecondOrderObjectSyntax.value_m (up₃ U) (.bvar (.there (.there .here))) (.bvar .here))
      (matrix_m false φ (up₃ B) (up₃ C) (up₃ ω) (up₃ Q) (up₃ e)
        (up₃ t₀) (up₃ t₁) (up₃ t₂) (up₃ a) (.bvar .here) (.bvar (.there .here))))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def number_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (B C ω Q e t₀ t₁ t₂ a U n y : type_l hℳ) : Prop :=
  ∃ p, value_l (ℳ := 𝒱) U n p ∧ matrix_l false φ η B C ω Q e t₀ t₁ t₂ a p y

private theorem opening_l {Δ : SortContext ℒ} (η : Env 𝒱 [] Δ) :
    PowerlessSourceOpening.env_l η = η := by
  apply Env.ext
  · intro s v; nomatch v
  · intro s v; rfl

theorem bound_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B C ω Q e t₀ t₁ t₂ a U : Term ℒ Γ Δ .set) (n y : type_l hℳ) :
    (number_m φ B C ω Q e t₀ t₁ t₂ a U).satisfies
      (((PowerlessSourceOpening.env_l η).pushFree n).pushFree y) ↔
      number_l φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η) (Q.eval η) (e.eval η)
        (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (U.eval η) n y := by
  have hη := PowerlessSourceOpening.formula_l
    (show Formula ℒ (.set :: .set :: Γ) Δ from
      .existsE .set <| .conj
        (SecondOrderObjectSyntax.value_m (up₃ U) (.bvar (.there (.there .here))) (.bvar .here))
        (matrix_m false φ (up₃ B) (up₃ C) (up₃ ω) (up₃ Q) (up₃ e)
          (up₃ t₀) (up₃ t₁) (up₃ t₂) (up₃ a) (.bvar .here) (.bvar (.there .here))))
    ((η.pushBound n).pushBound y)
  simpa only [number_m, number_l, PowerlessSourceOpening.push_l,
    Formula.satisfies, value_formula_l, matrix_formula_l K, parameters_pushBound_l,
    up₃, up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there] using hη

theorem number_formula_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B C ω Q e t₀ t₁ t₂ a U : Term ℒ [] Δ .set) (n y : type_l hℳ) :
    (number_m φ B C ω Q e t₀ t₁ t₂ a U).satisfies ((η.pushFree n).pushFree y) ↔
      number_l φ η (B.eval η) (C.eval η) (ω.eval η) (Q.eval η) (e.eval η)
        (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (U.eval η) n y := by
  simpa only [opening_l, parameters_empty_l] using
    bound_formula_l K φ η B C ω Q e t₀ t₁ t₂ a U n y

theorem result_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B C ω Q e t₀ t₁ t₂ a : Term ℒ [] Δ .set) (U : type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x (B.eval η) → ∀ z, mem_l hℳ z x → mem_l hℳ z (B.eval η))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η))
    (hω : SecondOrderOmega.omega_l hℳ (ω.eval η)) (he : ∀ x, ¬mem_l hℳ x (e.eval η))
    (hInitial : PowerlessRelativeFiniteProgramStep.record_l (e.eval η) (e.eval η) (e.eval η) (a.eval η))
    (hTags : t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η)
    (hFunctional : functional_l φ η (B.eval η)) {S P : type_l hℳ}
    (hDomain : PowerlessRelativeFiniteProgramDomain.domain_l (B.eval η) (ω.eval η) (Q.eval η) S P)
    (hU : map_l (ℳ := 𝒱) U (ω.eval η) P)
    (n : type_l hℳ) (hn : mem_l hℳ n (ω.eval η)) :
    ∃! y, number_l φ η (B.eval η) (C.eval η) (ω.eval η) (Q.eval η) (e.eval η)
      (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) U n y := by
  obtain ⟨p, ⟨hp, hUp⟩, _⟩ := hU.2 n hn
  have ht (t : Term ℒ [] Δ .set) : (up t).eval (η.pushBound p) = t.eval η := by
    simp only [up, Term.eval_weakenBound]
  have h := PowerlessRelativeFiniteProgramEvaluation.result_l K φ (η.pushBound p)
    (up B) (up C) (up ω) (up Q) (up e) (up t₀) (up t₁) (up t₂) (up a) (.bvar .here)
    (by simpa only [ht] using hBase) (by simpa only [ht] using hC)
    (by simpa only [ht] using hω) (by simpa only [ht] using he)
    (by simpa only [ht] using hInitial) (by simpa only [ht] using hTags)
    (by simpa only [ht, parameters_pushBound_l, parameters_empty_l] using hFunctional)
    (by simpa only [ht] using hDomain)
    (by simpa only [Term.eval, Env.pushBound_bound_here, ThirdOrderSemantics.member_l,
      SecondOrderQuotient.structure_l] using hp)
  have hResult : ∃! y, matrix_l false φ η (B.eval η) (C.eval η) (ω.eval η) (Q.eval η)
      (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) p y := by
    simpa only [ht, parameters_pushBound_l, parameters_empty_l, Term.eval,
      Env.pushBound_bound_here] using h.1
  obtain ⟨y, hy, hUnique⟩ := hResult
  refine ⟨y, ⟨p, hUp, hy⟩, ?_⟩
  rintro z ⟨p', hUp', hz⟩
  obtain rfl := SecondOrderFunctionProperties.value_unique_l hℳ hU hUp' hUp
  exact hUnique z hz

/-- 精确全像对应依赖原满射，既不漏空词也不删无效输出坐标。 -/
theorem range_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {B C ω Q e t₀ t₁ t₂ a U P : type_l hℳ}
    (hU : map_l (ℳ := 𝒱) U ω P)
    (hOnto : ∀ p, mem_l hℳ p P → ∃ n, mem_l hℳ n ω ∧ value_l (ℳ := 𝒱) U n p)
    (y : type_l hℳ) :
    (∃ n, mem_l hℳ n ω ∧ number_l φ η B C ω Q e t₀ t₁ t₂ a U n y) ↔
      ∃ p, mem_l hℳ p P ∧ matrix_l false φ η B C ω Q e t₀ t₁ t₂ a p y := by
  constructor
  · rintro ⟨n, _, p, hUp, hy⟩
    exact ⟨p, (SecondOrderFunctionProperties.value_mem_l hℳ hU hUp).2, hy⟩
  · rintro ⟨p, hp, hy⟩
    obtain ⟨n, hn, hUp⟩ := hOnto p hp
    exact ⟨n, hn, p, hUp, hy⟩

def conclusion_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a U P : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  let ψ := number_m φ B C ω Q e t₀ t₁ t₂ a U
  .conj (.forallE .set <| .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (up ω)) <|
    .existsE .set <| .conj (at_m ψ (.bvar (.there .here)) (.bvar .here)) <|
      .forallE .set <| .imp (at_m ψ (.bvar (.there (.there .here))) (.bvar .here))
        (.equal (.bvar .here) (.bvar (.there .here)))) <|
    .conj (.forallE .set <| .iff
      (.existsE .set <| .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up₂ ω))
        (at_m ψ (.bvar .here) (.bvar (.there .here))))
      (.existsE .set <| .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up₂ P))
        (matrix_m false φ (up₂ B) (up₂ C) (up₂ ω) (up₂ Q) (up₂ e)
          (up₂ t₀) (up₂ t₁) (up₂ t₂) (up₂ a) (.bvar .here) (.bvar (.there .here)))))
      (PowerlessDefinableMembershipCollapse.conclusion_m ψ ω)

theorem conclusion_formula_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B C ω Q e t₀ t₁ t₂ a U P : Term ℒ [] Δ .set) :
    (conclusion_m φ B C ω Q e t₀ t₁ t₂ a U P).satisfies η ↔
      (∀ n, mem_l hℳ n (ω.eval η) → ∃! y, number_l φ η (B.eval η) (C.eval η)
        (ω.eval η) (Q.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η)
          (a.eval η) (U.eval η) n y) ∧
      (∀ y, (∃ n, mem_l hℳ n (ω.eval η) ∧ number_l φ η (B.eval η) (C.eval η)
        (ω.eval η) (Q.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η)
          (a.eval η) (U.eval η) n y) ↔ ∃ p, mem_l hℳ p (P.eval η) ∧
            matrix_l false φ η (B.eval η) (C.eval η) (ω.eval η) (Q.eval η) (e.eval η)
              (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) p y) ∧
      ∃ A D T H, PowerlessDefinableMembershipDiagram.spec_l
          (number_m φ B C ω Q e t₀ t₁ t₂ a U) η (ω.eval η) A ∧
        PowerlessDefinableMembershipCollapse.domain_l (𝒩 := 𝒱) A D ∧
          SecondOrderCollapseFunction.spec_l hℳ A D T H := by
  simp only [conclusion_m, PowerlessDefinableMembershipCollapse.conclusion_m,
    Formula.satisfies, at_formula_l, matrix_formula_l K,
    PowerlessDefinableMembershipDiagram.spec_formula_l,
    PowerlessDefinableMembershipCollapse.domain_formula_l, SecondOrderCollapseSyntax.formula_l,
    parameters_pushBound_l, parameters_empty_l, number_formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up₂, up, Term.eval_weakenBound,
    Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there, ExistsUnique]
  rfl

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a U S P : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B C) <|
      .imp (SecondOrderOmegaSyntax.omega_m ω) <|
        .imp (PowerlessDefinableFiniteTraceDerives.zero_m e) <|
          .imp (PowerlessRelativeFiniteProgramStep.record_m e e e a) <|
            .imp (tags_m t₀ t₁ t₂) <| .imp (functional_m φ B) <|
              .imp (PowerlessRelativeFiniteProgramDomain.domain_m B ω Q S P) <|
                .imp (SecondOrderObjectSyntax.map_m U ω P) <|
                  .imp (PowerlessRelativeClassEnumerationSectionDerives.onto_m U ω P)
                    (conclusion_m φ B C ω Q e t₀ t₁ t₂ a U P)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a U S P : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B C ω Q e t₀ t₁ t₂ a U S P)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (B C ω Q e t₀ t₁ t₂ a U S P : Term ℒ [] Δ .set) :
    (sentence_m φ B C ω Q e t₀ t₁ t₂ a U S P).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderOmegaSyntax.omega_l,
    PowerlessDefinableFiniteTraceDerives.zero_m, PowerlessRelativeFiniteProgramStep.record_formula_l,
    tags_m, functional_m, PowerlessBMSQuotientSubsetImageDerives.at_formula_l,
    PowerlessRelativeFiniteProgramDomain.domain_formula_l K, map_formula_l,
    PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l,
    parameters_pushBound_l, parameters_empty_l, SecondOrderObjectSyntax.member_m,
    Arguments.eval, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro η hBase hC hω he hInitial hTags hFunctional hDomain hU hOnto
  have hResult := result_l K φ η B C ω Q e t₀ t₁ t₂ a (U.eval η) hBase hC hω he hInitial hTags
    (by simpa only [functional_l, PowerlessRelativeClassCorrespondence.member_l,
      SecondOrderQuotient.structure_l, ThirdOrderSemantics.carrier_l] using hFunctional) hDomain hU
  have hωEq := SecondOrderOmega.unique_l h𝒩 hω K.omega_spec
  have hUnique n y z (hn : mem_l h𝒩 n K.omega)
      (hy : (number_m φ B C ω Q e t₀ t₁ t₂ a U).satisfies ((η.pushFree n).pushFree y))
      (hz : (number_m φ B C ω Q e t₀ t₁ t₂ a U).satisfies ((η.pushFree n).pushFree z)) : y = z := by
    obtain ⟨v, _, hv⟩ := hResult n (by simpa only [hωEq] using hn)
    exact (hv y ((number_formula_l K φ η B C ω Q e t₀ t₁ t₂ a U n y).mp hy)).trans
      (hv z ((number_formula_l K φ η B C ω Q e t₀ t₁ t₂ a U n z).mp hz)).symm
  obtain ⟨A, D, T, H, hSpec, hField, hCollapse⟩ :=
    PowerlessDefinableMembershipCollapse.exists_l K
      (number_m φ B C ω Q e t₀ t₁ t₂ a U) η hUnique
  apply (conclusion_formula_l K φ η B C ω Q e t₀ t₁ t₂ a U P).mpr
  exact ⟨hResult, range_l φ η hU hOnto, A, D, T, H,
    by simpa only [hωEq] using hSpec, hField, hCollapse⟩

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a U S P : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B C ω Q e t₀ t₁ t₂ a U S P)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ h𝒩 => models_l h𝒩 φ B C ω Q e t₀ t₁ t₂ a U S P)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramNumberEvaluation
