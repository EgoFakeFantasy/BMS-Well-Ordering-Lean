import BMSConstructibleBridge.PowerlessClassProgramHull
import BMSConstructibleBridge.PowerlessDefinableWholeCollapse
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramEnumeratedCollapse

/-! # 同一实际 Class 程序的全码域总同构

纯隶属语言、原 Z₂。规范编码包及原全部程序的 Class 枚举均在证明内
产生；数码正文保持原算子、原自由参数和完整 matrix false。沿实际满射
给出的精确全像对应传输虚拟外延性与真实单集上邻，从而所有内部数码
进入同一实际坍缩的域域，投影在全部原输出上成为总同构。
对象句子不预供算子函数性、虚拟外延性、数码枚举或总同构。种子、
字母表、原全码域与种子 Class 枚举仍采用原构造规格；元素性、凝聚、
T/H 的 Class 性、严格阶段界及最终 BMS 对象推导仍须另证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassProgramIsomorphism

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessBMSQuotientSubsetImageDerives
  (parameters_l parameters_pushBound_l parameters_empty_l at_m at_formula_l)
open SecondOrderCanonicalLevelDerives (guard_m guard_l guard_formula_l)
open PowerlessClassProgramHull (operator_m)
open PowerlessRelativeFiniteProgramNumberEvaluation (number_m number_l)
open PowerlessRelativeFiniteProgramEnumeratedCollapse (reading_l)
open PowerlessDefinableMembershipIsomorphism (image_l project_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (v : Term ℒ Γ Δ .set) :=
  v.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (v : Term ℒ Γ Δ .set) := up (up v)
private abbrev up₃ {Γ Δ : SortContext ℒ} (v : Term ℒ Γ Δ .set) := up (up₂ v)
private abbrev up₅ {Γ Δ : SortContext ℒ} (v : Term ℒ Γ Δ .set) := up₂ (up₃ v)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "ε" => SecondOrderQuotient.mem_l hℳ

private theorem opening_l {Δ : SortContext ℒ} (η : Env 𝒱 [] Δ) :
    PowerlessSourceOpening.env_l η = η := by
  apply Env.ext
  · intro v s; nomatch s
  · intro v s; rfl

/-- 保留原精确隶属图及原坍缩，补齐其全域性和总同构，不另造输出像。 -/
theorem collapse_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B C ω Q e t₀ t₁ t₂ a P : Term ℒ [] Δ .set) (U A D T H : Raw)
    (hResult : ∀ n, ε n (ω.eval η) → ∃! y, number_l φ η (B.eval η) (C.eval η)
      (ω.eval η) (Q.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) U n y)
    (hRange : ∀ y, (∃ n, ε n (ω.eval η) ∧ number_l φ η (B.eval η) (C.eval η)
      (ω.eval η) (Q.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) U n y) ↔
        PowerlessRelativeFiniteProgramVirtualClosure.image_l false φ η (B.eval η) (C.eval η)
          (ω.eval η) (Q.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (P.eval η) y)
    (hExt :
      let I := PowerlessRelativeFiniteProgramVirtualClosure.image_l false φ η
        (B.eval η) (C.eval η) (ω.eval η) (Q.eval η) (e.eval η)
          (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (P.eval η)
      ∀ x y, I x → I y → (∀ z, I z → (ε z x ↔ ε z y)) → x = y)
    (hUpper :
      let I := PowerlessRelativeFiniteProgramVirtualClosure.image_l false φ η
        (B.eval η) (C.eval η) (ω.eval η) (Q.eval η) (e.eval η)
          (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (P.eval η)
      ∀ x, I x → ∃ z, I z ∧ SecondOrderPairObjects.pair_l hℳ x x z)
    (hA : PowerlessDefinableMembershipDiagram.spec_l
      (number_m φ (up B) (up C) (up ω) (up Q) (up e) (up t₀) (up t₁) (up t₂)
        (up a) (.bvar .here)) (η.pushFree U) (ω.eval η) A)
    (hD : PowerlessDefinableMembershipCollapse.domain_l (𝒩 := 𝒱) A D)
    (hH : SecondOrderCollapseFunction.spec_l hℳ A D T H) :
    D = ω.eval η ∧ PowerlessDefinableWholeCollapse.isomorphism_l
      (number_m φ (up B) (up C) (up ω) (up Q) (up e) (up t₀) (up t₁) (up t₂)
        (up a) (.bvar .here)) (η.pushFree U) (ω.eval η) T H := by
  let ψ := number_m φ (up B) (up C) (up ω) (up Q) (up e) (up t₀) (up t₁) (up t₂)
    (up a) (.bvar .here)
  let I := PowerlessRelativeFiniteProgramVirtualClosure.image_l false φ η
    (B.eval η) (C.eval η) (ω.eval η) (Q.eval η) (e.eval η)
      (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (P.eval η)
  have hImage (x : Raw) : image_l ψ (η.pushFree U) (ω.eval η) x ↔ I x := by
    simpa only [image_l, ψ, reading_l K, ThirdOrderSemantics.member_l,
      SecondOrderQuotient.structure_l, I] using hRange x
  have hUnique n x y (hn : ε n (ω.eval η))
      (hx : ψ.satisfies (((η.pushFree U).pushFree n).pushFree x))
      (hy : ψ.satisfies (((η.pushFree U).pushFree n).pushFree y)) : x = y := by
    obtain ⟨z, _, hz⟩ := hResult n hn
    exact (hz x ((reading_l K φ η B C ω Q e t₀ t₁ t₂ a U n x).mp hx)).trans
      (hz y ((reading_l K φ η B C ω Q e t₀ t₁ t₂ a U n y).mp hy)).symm
  have hCode n (hn : ε n (ω.eval η)) : ∃ x, ψ.satisfies (((η.pushFree U).pushFree n).pushFree x) := by
    obtain ⟨x, hx, _⟩ := hResult n hn
    exact ⟨x, (reading_l K φ η B C ω Q e t₀ t₁ t₂ a U n x).mpr hx⟩
  have hExt' : PowerlessDefinableMembershipIsomorphism.ext_l ψ (η.pushFree U) (ω.eval η) := by
    intro x y hx hy hxy
    exact hExt x y ((hImage x).mp hx) ((hImage y).mp hy)
      (fun z hz => hxy z ((hImage z).mpr hz))
  have hUpper' x (hx : image_l ψ (η.pushFree U) (ω.eval η) x) :
      ∃ z, image_l ψ (η.pushFree U) (ω.eval η) z ∧ SecondOrderPairObjects.pair_l hℳ x x z := by
    obtain ⟨z, hz, hxz⟩ := hUpper x ((hImage x).mp hx)
    exact ⟨z, (hImage z).mpr hz, hxz⟩
  have hEq := PowerlessVirtualHullExtensionality.domain_l ψ (η.pushFree U) hA hD hCode hUpper'
  subst D
  refine ⟨rfl, ?_,
    PowerlessDefinableMembershipIsomorphism.injective_l ψ (η.pushFree U) hUnique hA hD hH hExt',
    (fun x y z hy hz => PowerlessDefinableMembershipIsomorphism.same_l ψ (η.pushFree U) hUnique hA hD hH hy hz),
    (fun x y a b hx hy => PowerlessDefinableMembershipIsomorphism.member_l ψ (η.pushFree U) hUnique hA hD hH hExt' hx hy),
    PowerlessDefinableMembershipIsomorphism.onto_l ψ (η.pushFree U) hA hD hH⟩
  rintro x ⟨n, hn, hnx⟩
  obtain ⟨y, ⟨hy, hny⟩, _⟩ := hH.2.1.2 n hn
  exact ⟨y, hy, n, hn, hnx, hny⟩

theorem exists_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (Φ : List (Formula ℒ [] (.set :: .set :: Δ))) (η : Env 𝒱 [] Δ)
    (ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a G S P s t : Term ℒ [] Δ .set)
    (hCoding : SecondOrderComparisonStageTotal.coding_l K (r₁.eval η) (r₂.eval η)
      (r₃.eval η) (Pair.eval η) (Valid.eval η))
    (hω : SecondOrderOmega.omega_l hℳ (ω.eval η))
    (hGuard : guard_l (B.eval η) (P₀.eval η))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η))
    (hωC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (ω.eval η))
    (hQ : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (Q.eval η))
    (hG : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (G.eval η))
    (h₀ : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (t₀.eval η))
    (h₁ : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (t₁.eval η))
    (h₂ : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (t₂.eval η))
    (hMap : map_l (ℳ := 𝒱) (G.eval η) (ω.eval η) (C.eval η))
    (hOnto : ∀ x, ε x (C.eval η) → ∃ n, ε n (ω.eval η) ∧ value_l (ℳ := 𝒱) (G.eval η) n x)
    (he : ∀ x, ¬ε x (e.eval η))
    (ha : PowerlessRelativeFiniteProgramStep.record_l (e.eval η) (e.eval η) (e.eval η) (a.eval η))
    (ht : t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η)
    (hAlphabet : ∀ q, ε q (Q.eval η) ↔
      PowerlessRelativeFiniteProgramAlphabet.instruction_l (C.eval η) (ω.eval η)
        (t₀.eval η) (t₁.eval η) (t₂.eval η) q)
    (hDomain : PowerlessRelativeFiniteProgramDomain.domain_l (B.eval η) (ω.eval η)
      (Q.eval η) (S.eval η) (P.eval η))
    (hBC : ε (B.eval η) (C.eval η)) (hs : ε (s.eval η) (C.eval η))
    (htC : ε (t.eval η) (C.eval η)) (hst : s.eval η ≠ t.eval η) :
    let φ := operator_m Φ ω e r₁ r₂ r₃ Pair Valid B P₀ s t
    ∃ U A T H : Raw, PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) U ∧
      map_l (ℳ := 𝒱) U (ω.eval η) (P.eval η) ∧
      (∀ p, ε p (P.eval η) → ∃ n, ε n (ω.eval η) ∧ value_l (ℳ := 𝒱) U n p) ∧
      (∀ n, ε n (ω.eval η) → ∃! y, number_l φ η (B.eval η) (C.eval η)
        (ω.eval η) (Q.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) U n y) ∧
      PowerlessDefinableMembershipDiagram.spec_l
        (number_m φ (up B) (up C) (up ω) (up Q) (up e) (up t₀) (up t₁) (up t₂)
          (up a) (.bvar .here)) (η.pushFree U) (ω.eval η) A ∧
      PowerlessDefinableMembershipCollapse.domain_l (𝒩 := 𝒱) A (ω.eval η) ∧
      SecondOrderCollapseFunction.spec_l hℳ A (ω.eval η) T H ∧
      PowerlessDefinableWholeCollapse.isomorphism_l
        (number_m φ (up B) (up C) (up ω) (up Q) (up e) (up t₀) (up t₁) (up t₂)
          (up a) (.bvar .here)) (η.pushFree U) (ω.eval η) T H := by
  let φ := operator_m Φ ω e r₁ r₂ r₃ Pair Valid B P₀ s t
  have hB : ∀ x, ε x (B.eval η) → ∀ z, ε z x → ε z (B.eval η) :=
    fun x hx z hz => hGuard.2.1 x z hx hz
  obtain ⟨hφ, hClass, hSeed, hPair, hCall, hTotal⟩ := PowerlessClassProgramHull.closure_l K Φ η
    ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a S P s t
      hCoding hω hGuard hC hωC hQ he ha ht hAlphabet hDomain hBC
  have hExt := PowerlessVirtualHullExtensionality.extensional_l Φ η s t _ hB hst hClass
    (hSeed _ hs) hPair hCall hTotal
  have hUpper := PowerlessVirtualHullExtensionality.upper_l Φ η s t _ hB hst hClass
    (hSeed _ hs) (hSeed _ htC) hPair hCall hTotal
  obtain ⟨U, A, D, T, H, hUC, hU, hUOnto, hResult, hRange, hA, hD, hH⟩ :=
    PowerlessRelativeFiniteProgramEnumeratedCollapse.exists_l K φ η B C ω Q e t₀ t₁ t₂ a G S P
      hB hω hωC hC hG h₀ h₁ h₂ hQ hMap hOnto hAlphabet hDomain he ha ht hφ
  obtain ⟨hEq, hIso⟩ := collapse_l K φ η B C ω Q e t₀ t₁ t₂ a P U A D T H
    hResult hRange hExt hUpper hA hD hH
  subst D
  exact ⟨U, A, T, H, hUC, hU, hUOnto, hResult, hA, hD, hH, hIso⟩

private def number_body_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a : Term ℒ [] Δ .set) : Formula ℒ [] (.set :: Δ) :=
  let ψ := number_m φ (up B) (up C) (up ω) (up Q) (up e) (up t₀) (up t₁) (up t₂)
    (up a) (.bvar .here)
  let O := ω.weakenFree SetTheory.SetSort.set
  .conj (.forallE .set <| .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (up O)) <|
    .existsE .set <| .conj (at_m ψ (.bvar (.there .here)) (.bvar .here)) <|
      .forallE .set <| .imp (at_m ψ (.bvar (.there (.there .here))) (.bvar .here))
        (.equal (.bvar .here) (.bvar (.there .here))))
    (PowerlessDefinableWholeCollapse.conclusion_m ψ O)

def conclusion_m {Δ : SortContext ℒ} (Φ : List (Formula ℒ [] (.set :: .set :: Δ)))
    (ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a P s t : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  let φ := operator_m Φ ω e r₁ r₂ r₃ Pair Valid B P₀ s t
  .existsE .set <| .conj (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here)) <|
    .conj (SecondOrderObjectSyntax.map_m (.bvar .here) (up ω) (up P)) <|
      .conj (PowerlessRelativeClassEnumerationSectionDerives.onto_m (.bvar .here) (up ω) (up P))
        (PowerlessSourceRebinding.formula_m (number_body_m φ B C ω Q e t₀ t₁ t₂ a))

private def mode_m {Δ : SortContext ℒ} (Φ : List (Formula ℒ [] (.set :: .set :: Δ)))
    (ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a G S P s t : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (guard_m B P₀) <| .imp (PowerlessRelativeHierarchySyntax.class_m B C) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B ω) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B Q) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B G) <|
          .imp (PowerlessRelativeHierarchySyntax.class_m B t₀) <|
            .imp (PowerlessRelativeHierarchySyntax.class_m B t₁) <|
              .imp (PowerlessRelativeHierarchySyntax.class_m B t₂) <|
                .imp (SecondOrderObjectSyntax.map_m G ω C) <|
                  .imp (PowerlessRelativeClassEnumerationSectionDerives.onto_m G ω C) <|
                    .imp (PowerlessDefinableFiniteTraceDerives.zero_m e) <|
                      .imp (PowerlessRelativeFiniteProgramStep.record_m e e e a) <|
                        .imp (PowerlessRelativeFiniteProgramInstruction.tags_m t₀ t₁ t₂) <|
                          .imp (PowerlessRelativeFiniteProgramAlphabet.alphabet_m C ω t₀ t₁ t₂ Q) <|
                            .imp (PowerlessRelativeFiniteProgramDomain.domain_m B ω Q S P) <|
                              .imp (SecondOrderObjectSyntax.member_m B C) <|
                                .imp (SecondOrderObjectSyntax.member_m s C) <|
                                  .imp (SecondOrderObjectSyntax.member_m t C) <| .imp (.neg (.equal s t))
                                    (conclusion_m Φ ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a P s t)

private theorem mode_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (Φ : List (Formula ℒ [] (.set :: .set :: Δ))) (η : Env 𝒱 [] Δ)
    (ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a G S P s t : Term ℒ [] Δ .set)
    (hCoding : SecondOrderComparisonStageTotal.coding_l K (r₁.eval η) (r₂.eval η)
      (r₃.eval η) (Pair.eval η) (Valid.eval η))
    (hω : SecondOrderOmega.omega_l hℳ (ω.eval η)) :
    (mode_m Φ ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a G S P s t).satisfies η := by
  simp only [mode_m, Formula.satisfies, guard_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, map_formula_l,
    PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l,
    PowerlessDefinableFiniteTraceDerives.zero_formula_l,
    PowerlessRelativeFiniteProgramStep.record_formula_l,
    PowerlessRelativeFiniteProgramInstruction.tags_m,
    PowerlessRelativeFiniteProgramAlphabet.alphabet_formula_l,
    PowerlessRelativeFiniteProgramDomain.domain_formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  intro hGuard hC hωC hQ hG h₀ h₁ h₂ hMap hOnto he ha ht hAlphabet hDomain hBC hs htC hst
  obtain ⟨U, A, T, H, hUC, hU, hUOnto, hResult, hA, hD, hH, hIso⟩ :=
    exists_l K Φ η ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a G S P s t
      hCoding hω hGuard hC hωC hQ hG h₀ h₁ h₂ hMap hOnto he ha ht hAlphabet hDomain hBC hs htC hst
  simp only [conclusion_m, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.class_formula_l K, map_formula_l,
    PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l,
    up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here]
  refine ⟨U, hUC, hU, hUOnto, ?_⟩
  apply (PowerlessSourceRebinding.formula_l _ (η.pushBound U)).mpr
  simp only [PowerlessSourceOpening.push_l, opening_l, number_body_m, Formula.satisfies,
    PowerlessDefinableWholeCollapse.conclusion_formula_l, parameters_empty_l, at_formula_l,
    parameters_pushBound_l, up, Term.eval_weakenBound, Term.eval_weakenFree,
    Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there, reading_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  exact ⟨hResult, A, T, H, hA, hD, hH, hIso⟩

private def body_m {Γ Δ : SortContext ℒ} (Φ : List (Formula ℒ [] (.set :: .set :: Δ)))
    (ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a G S P s t : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let τ := @PowerlessSourceRebinding.term_m Γ Δ
  PowerlessSourceRebinding.formula_m <|
    mode_m (Φ.map (PowerlessRelativeFiniteProgramBoundOutput.prefix_m Γ.length))
      (τ ω) (τ e) (τ r₁) (τ r₂) (τ r₃) (τ Pair) (τ Valid) (τ B) (τ P₀) (τ C)
        (τ Q) (τ t₀) (τ t₁) (τ t₂) (τ a) (τ G) (τ S) (τ P) (τ s) (τ t)

def schema_m {Δ : SortContext ℒ} (Φ : List (Formula ℒ [] (.set :: .set :: Δ)))
    (ω e B P₀ C Q t₀ t₁ t₂ a G S P s t : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <|
      body_m Φ (up₅ ω) (up₅ e) (.bvar (.there (.there (.there (.there .here)))))
        (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here)))
        (.bvar (.there .here)) (.bvar .here) (up₅ B) (up₅ P₀) (up₅ C) (up₅ Q)
        (up₅ t₀) (up₅ t₁) (up₅ t₂) (up₅ a) (up₅ G) (up₅ S) (up₅ P) (up₅ s) (up₅ t)

def sentence_m {Δ : SortContext ℒ} (Φ : List (Formula ℒ [] (.set :: .set :: Δ)))
    (ω e B P₀ C Q t₀ t₁ t₂ a G S P s t : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m Φ ω e B P₀ C Q t₀ t₁ t₂ a G S P s t)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (Φ : List (Formula ℒ [] (.set :: .set :: Δ)))
    (ω e B P₀ C Q t₀ t₁ t₂ a G S P s t : Term ℒ [] Δ .set) :
    (sentence_m Φ ω e B P₀ C Q t₀ t₁ t₂ a G S P s t).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, omega_formula_l]
  intro hω
  have hω' := (SecondOrderOmegaSyntax.omega_l h𝒩 η ω).mp ((omega_formula_l η ω).mpr hω)
  obtain ⟨K, _, r₁, r₂, r₃, Pair, Valid, _, _, hCoding⟩ := SecondOrderComparisonCoding.exists_l hω
  refine ⟨r₁, r₂, r₃, Pair, Valid, ?_⟩
  simp only [body_m, PowerlessSourceRebinding.formula_l]
  apply mode_l K
  · simpa only [PowerlessSourceRebinding.term_l, Term.eval,
      Env.pushBound_bound_here, Env.pushBound_bound_there] using hCoding
  · simpa only [PowerlessSourceRebinding.term_l, up₅, up₃, up₂, up,
      Term.eval_weakenBound] using hω'

theorem derives_m {Δ : SortContext ℒ} (Φ : List (Formula ℒ [] (.set :: .set :: Δ)))
    (ω e B P₀ C Q t₀ t₁ t₂ a G S P s t : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m Φ ω e B P₀ C Q t₀ t₁ t₂ a G S P s t)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ h𝒩 => models_l h𝒩 Φ ω e B P₀ C Q t₀ t₁ t₂ a G S P s t)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassProgramIsomorphism
