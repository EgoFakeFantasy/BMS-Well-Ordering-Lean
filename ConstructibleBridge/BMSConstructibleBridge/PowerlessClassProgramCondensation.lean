import BMSConstructibleBridge.PowerlessClassProgramElementarity
import BMSConstructibleBridge.PowerlessClassProgramIsomorphism
import BMSConstructibleBridge.PowerlessWholeCollapseSeed
import BMSConstructibleBridge.PowerlessClassOperationRequests
import BMSConstructibleBridge.PowerlessWholeCollapseCodedCoverage
import BMSConstructibleBridge.PowerlessRelativeWeakCondensationDerives

/-! # 同一实际 Class 程序坍缩的弱凝聚与层资格

纯隶属 ℒ、原 Z₂。操作请求、原完整覆盖族及调用方有限族共用同一
算子和全程序域。原 Class 覆盖经请求反射及同一全坍缩传输，取得 T
内原阶段见证和任意 raw Def 输出闭包；已证弱凝聚识别同一 T=Lⱼ[B]。
种子 D 覆盖 B 和内部 ω，内部归纳固定它们。T 的 Class 资格在结论内
证明，不作为背景前提。实际种子枚举和原程序构造规格仍需后续无条件
装配；完整 Collection、严格阶段界及最终 BMS 良序句尚未完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassProgramCondensation

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderCanonicalLevelDerives (guard_m guard_l guard_formula_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_pushBound_l parameters_empty_l)
open PowerlessRelativeFiniteProgramNumberEvaluation (number_m)
open PowerlessRelativeFiniteProgramEnumeratedCollapse (reading_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

def family_m (Φ : PowerlessClassFiniteElementarity.family_m []) :
    PowerlessClassFiniteElementarity.family_m [] :=
  PowerlessClassOperationRequests.family_m [] ++
    (PowerlessRelativeFiniteHullCodedCoverage.family_m [] ++ Φ)

private def parameters_m {Δ : SortContext ℒ} : VariableSubstitution ℒ [] [] Δ :=
  fun v => nomatch v

private abbrev up {Γ Δ : SortContext ℒ} (v : Term ℒ Γ Δ .set) :=
  v.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (v : Term ℒ Γ Δ .set) := up (up v)
private abbrev up₃ {Γ Δ : SortContext ℒ} (v : Term ℒ Γ Δ .set) := up (up₂ v)
private abbrev up₅ {Γ Δ : SortContext ℒ} (v : Term ℒ Γ Δ .set) := up₂ (up₃ v)

private def number_body_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a D : Term ℒ [] Δ .set) : Formula ℒ [] (.set :: Δ) :=
  let ψ := number_m φ (up B) (up C) (up ω) (up Q) (up e) (up t₀) (up t₁) (up t₂)
    (up a) (.bvar .here)
  let O := Term.weakenFree (σ := ℒ) SetTheory.SetSort.set ω
  let b := Term.weakenFree (σ := ℒ) SetTheory.SetSort.set B
  let d := Term.weakenFree (σ := ℒ) SetTheory.SetSort.set D
  .existsE .set <| .existsE .set <| .existsE .set <|
    let A : Term ℒ (.set :: .set :: .set :: []) (.set :: Δ) .set := .bvar (.there (.there .here))
    let T := .bvar (.there .here)
    let H := .bvar .here
    .conj (PowerlessDefinableMembershipDiagram.spec_m ψ (up₃ O) A) <|
      .conj (PowerlessDefinableMembershipCollapse.domain_m A (up₃ O)) <|
        .conj (SecondOrderCollapseSyntax.formula_m A (up₃ O) T H) <|
          .conj (PowerlessDefinableWholeCollapse.isomorphism_m ψ (up₃ O) T H)
            (.conj (PowerlessWholeCollapseSeed.conclusion_m ψ (up₃ O) (up₃ d) T H) <|
              .conj (PowerlessRelativeHierarchySyntax.class_m (up₃ b) T)
                (PowerlessRelativeWeakCondensationDerives.conclusion_m (up₃ b) T))

/-- 有限元素性与实际坍缩使用同一原请求族和同一编码包。 -/
def conclusion_m {Δ : SortContext ℒ} (Φ : PowerlessClassFiniteElementarity.family_m [])
    (ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a P s t D : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  let Ψ := PowerlessClassProgramFiniteRequests.family_m (PowerlessClassFiniteElementarity.requests_m (family_m Φ)) B parameters_m
  let φ := PowerlessClassProgramHull.operator_m Ψ ω e r₁ r₂ r₃ Pair Valid B P₀ s t
  .conj (PowerlessClassProgramElementarity.conclusion_m (family_m Φ) parameters_m
    ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a P s t) <|
      .existsE .set <| .conj (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here)) <|
        .conj (SecondOrderObjectSyntax.map_m (.bvar .here) (up ω) (up P)) <|
          .conj (PowerlessRelativeClassEnumerationSectionDerives.onto_m (.bvar .here) (up ω) (up P))
            (PowerlessSourceRebinding.formula_m (number_body_m φ B C ω Q e t₀ t₁ t₂ a D))

private def mode_m {Δ : SortContext ℒ} (Φ : PowerlessClassFiniteElementarity.family_m [])
    (ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a G S P s t D : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
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
                                  .imp (SecondOrderObjectSyntax.member_m t C) <| .imp (.neg (.equal s t)) <|
                                    .imp (PowerlessRelativeHierarchyDerives.transitive_m D) <|
                                      .imp (ThirdOrderTheory.subset_m D C) <|
                                        .imp (SecondOrderObjectSyntax.member_m D C) <|
                                          .imp (SecondOrderObjectSyntax.member_m B D) <|
                                          .imp (SecondOrderObjectSyntax.member_m ω D)
                                            (conclusion_m Φ ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a P s t D)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "ε" => SecondOrderQuotient.mem_l hℳ

private theorem opening_l {Δ : SortContext ℒ} (η : Env 𝒱 [] Δ) :
    PowerlessSourceOpening.env_l η = η := by
  apply Env.ext
  · intro _ v; nomatch v
  · intro _ _; rfl

private theorem env_id_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ) :
    PowerlessDefinableMembershipDiagram.env_l η (fun v => .fvar v) =
      PowerlessBMSQuotientSubsetImageDerives.parameters_l η := by
  apply Env.ext
  · intro _ v; nomatch v
  · intro s v; cases s; rfl

private theorem number_body_formula_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B C ω Q e t₀ t₁ t₂ a D : Term ℒ [] Δ .set) (U : Raw) :
    let ψ := number_m φ (up B) (up C) (up ω) (up Q) (up e) (up t₀) (up t₁) (up t₂)
      (up a) (.bvar .here)
    (number_body_m φ B C ω Q e t₀ t₁ t₂ a D).satisfies (η.pushFree U) ↔
      ∃ A T H : Raw, PowerlessDefinableMembershipDiagram.spec_l ψ (η.pushFree U) (ω.eval η) A ∧
        PowerlessDefinableMembershipCollapse.domain_l (𝒩 := 𝒱) A (ω.eval η) ∧
          SecondOrderCollapseFunction.spec_l hℳ A (ω.eval η) T H ∧
            PowerlessDefinableWholeCollapse.isomorphism_l ψ (η.pushFree U) (ω.eval η) T H ∧
              ((∀ x, ε x (D.eval η) → ε x T ∧
                PowerlessDefinableMembershipIsomorphism.project_l ψ (η.pushFree U) (ω.eval η) H x x) ∧
              ε (D.eval η) T ∧ PowerlessDefinableMembershipIsomorphism.project_l ψ
                (η.pushFree U) (ω.eval η) H (D.eval η) (D.eval η)) ∧
              PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) T ∧
                ∃ J, PowerlessRelativeCollapseStageIndex.spec_l (B.eval η) T J ∧
                  SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) J ∧
                    PowerlessRelativeHierarchySemantics.limit_l hℳ J ∧
                      PowerlessRelativeHierarchySemantics.level_l hℳ (B.eval η) J T := by
  simp only [number_body_m, Formula.satisfies,
    PowerlessDefinableMembershipDiagram.spec_formula_l,
    PowerlessDefinableMembershipCollapse.domain_formula_l, SecondOrderCollapseSyntax.formula_l,
    PowerlessDefinableWholeCollapse.isomorphism_formula_l, PowerlessWholeCollapseSeed.conclusion_m,
    PowerlessWholeCollapseSeed.fixed_formula_l, PowerlessDefinableMembershipIsomorphism.project_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeWeakCondensationDerives.conclusion_formula_l K,
    env_id_l, parameters_pushBound_l, parameters_empty_l,
    up₃, up₂, up, Term.eval_weakenBound, Term.eval_weakenFree, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  rfl

private theorem mode_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (Φ : PowerlessClassFiniteElementarity.family_m [])
    (η : Env 𝒱 [] Δ)
    (ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a G S P s t D : Term ℒ [] Δ .set)
    (hCoding : SecondOrderComparisonStageTotal.coding_l K (r₁.eval η) (r₂.eval η)
      (r₃.eval η) (Pair.eval η) (Valid.eval η))
    (hω : SecondOrderOmega.omega_l hℳ (ω.eval η)) :
    (mode_m Φ ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a G S P s t D).satisfies η := by
  simp only [mode_m, Formula.satisfies, guard_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, map_formula_l,
    PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l,
    PowerlessDefinableFiniteTraceDerives.zero_formula_l,
    PowerlessRelativeFiniteProgramStep.record_formula_l,
    PowerlessRelativeFiniteProgramInstruction.tags_m,
    PowerlessRelativeFiniteProgramAlphabet.alphabet_formula_l,
    PowerlessRelativeFiniteProgramDomain.domain_formula_l K,
    PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ, subset_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  intro hGuard hC hωC hQ hG h₀ h₁ h₂ hMap hOnto he ha ht hAlphabet hDomain hBC hs htC hst hD hDC hDC₀ hBD hωD
  let Ψ := PowerlessClassProgramFiniteRequests.family_m (PowerlessClassFiniteElementarity.requests_m (family_m Φ)) B parameters_m
  let φ := PowerlessClassProgramHull.operator_m Ψ ω e r₁ r₂ r₃ Pair Valid B P₀ s t
  obtain ⟨_, hClass, hSeed, _, _, _⟩ := PowerlessClassProgramHull.closure_l K Ψ η
    ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a S P s t
      hCoding hω hGuard hC hωC hQ he ha ht hAlphabet hDomain hBC
  obtain ⟨U, A, T, H, hUC, hU, hUOnto, _, hA, hField, hH, hIso⟩ :=
    PowerlessClassProgramIsomorphism.exists_l K Ψ η
      ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a G S P s t
        hCoding hω hGuard hC hωC hQ hG h₀ h₁ h₂ hMap hOnto he ha ht hAlphabet hDomain hBC hs htC hst
  let ψ := number_m φ (up B) (up C) (up ω) (up Q) (up e) (up t₀) (up t₁) (up t₂)
    (up a) (.bvar .here)
  have hImage (x : Raw) : PowerlessDefinableMembershipIsomorphism.image_l ψ
      (η.pushFree U) (ω.eval η) x ↔
        PowerlessRelativeFiniteProgramVirtualClosure.image_l false φ η (B.eval η) (C.eval η)
          (ω.eval η) (Q.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (P.eval η) x := by
    simpa only [PowerlessDefinableMembershipIsomorphism.image_l, ψ, reading_l K,
      member_l, SecondOrderQuotient.structure_l, PowerlessRelativeFiniteProgramVirtualClosure.image_l] using
        PowerlessRelativeFiniteProgramNumberEvaluation.range_l φ η hU hUOnto x
  have hCover x (hx : ε x (D.eval η)) := (hImage x).mpr (hSeed x (hDC x hx))
  have hDI := (hImage (D.eval η)).mpr (hSeed _ hDC₀)
  have hFixed := PowerlessWholeCollapseSeed.fixed_l ψ (η.pushFree U) (ω.eval η) (D.eval η) T H
    hIso hD (fun x hx z hz => hH.1 x z hx hz) hCover
  have hFixed₀ := PowerlessWholeCollapseSeed.seed_l ψ (η.pushFree U) (ω.eval η) (D.eval η) T H
    hIso hD (fun x hx z hz => hH.1 x z hx hz) hCover hDI
  have hBase : ∀ x, ε x (B.eval η) → ∀ z, ε z x → ε z (B.eval η) :=
    fun x hx z hz => hGuard.2.1 x z hx hz
  have hTrans : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) T :=
    fun x z hx hz => hH.1 x z hx hz
  have hClass₀ : ∃ x, PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) x :=
    ⟨B.eval η, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩
  let I := PowerlessDefinableMembershipIsomorphism.image_l ψ (η.pushFree U) (ω.eval η)
  let ξ : Env (PowerlessSourceClass.structure_l (ℳ := 𝒱)
      (PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η)) hClass₀) [] [] := Env.empty
  let Λ := PowerlessClassFiniteElementarity.requests_m (family_m Φ)
  have hAll := PowerlessClassProgramFiniteRequests.requests_l K Λ parameters_m η
    ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a S P s t
      hCoding hω hGuard hC hωC hQ he ha ht hAlphabet hDomain hBC hs htC hst ξ
        (fun v => nomatch v)
  have hPredicate : (fun x : carrier_l (PowerlessSourceClass.structure_l (ℳ := 𝒱)
      (PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η)) hClass₀) => I x.val) =
      (fun x => PowerlessClassProgramFiniteRequests.image_l Λ parameters_m η
        ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a P s t x.val) := by
    funext x
    exact propext (hImage x.val)
  have hAll₀ : PowerlessSourcePredicateRequests.closed_l Λ ξ (fun x => I x.val) := by
    rw [hPredicate]
    exact hAll
  have hCaptured (p) (hp : p ∈ family_m Φ) : PowerlessSourcePredicateRequests.closed_l
      (PowerlessSourceRequests.requests_m .truth p.2) ξ (fun x => I x.val) :=
    PowerlessSourcePredicateRequests.subset_l
      (fun q hq => List.mem_flatMap.mpr ⟨p, hp, hq⟩) hAll₀
  have hIP x (hx : I x) := hClass x ((hImage x).mp hx)
  have hClosed : PowerlessWholeCollapseClosure.closed_l ψ (η.pushFree U) (ω.eval η) :=
    PowerlessClassOperationRequests.closed_l (hBase := hBase) (hP := hClass₀) I hIP
      (fun p hp => hCaptured p (List.mem_append_left _ hp))
  have hBT := (hFixed (B.eval η) hBD).1
  have hωT := (hFixed (ω.eval η) hωD).1
  have hBI := hCover (B.eval η) hBD
  have hωI := hCover (ω.eval η) hωD
  have hPackets := PowerlessWholeCollapseCodedCoverage.packet_l K ψ (η.pushFree U)
    (ω.eval η) T H (B.eval η) (ω.eval η) hBase hω hIso hTrans hIP hClosed hBI hωI
      hBT hωT (hFixed (B.eval η) hBD).2 (hFixed (ω.eval η) hωD).2
      (hCaptured _ (List.mem_append_right _ (List.mem_append_left _ List.mem_cons_self)))
  have hTargetClosed := PowerlessWholeCollapseClosure.target_l ψ (η.pushFree U)
    (ω.eval η) T H hIso hTrans hClosed
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  have hCondensation := PowerlessRelativeWeakCondensation.exists_l K hBase
    (fun x hx z hz => hTrans x z hx hz) hBT
    (fun x hx => hTrans (ω.eval η) x hωT (hωEq.symm ▸ hx)) hTargetClosed
    (fun x hx => PowerlessRelativeCodedHistoryCollapseReading.stage_l K (hPackets x hx))
    (fun x hx r hr => PowerlessRelativeCodedHistoryCollapseReading.def_l K hTrans (hPackets x hx) hr)
  have hTargetClass : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) T := by
    obtain ⟨J, _hJ, _hOrdinal, _hLimit, hLevel⟩ := hCondensation
    exact PowerlessRelativeLevelClosure.class_l hℳ hBase hLevel
  change (_ ∧ _)
  refine ⟨PowerlessClassProgramElementarity.elementarity_l K (family_m Φ) parameters_m η
    ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a S P s t
      hCoding hω hGuard hC hωC hQ he ha ht hAlphabet hDomain hBC hs htC hst, ?_⟩
  simp only [Formula.satisfies,
    PowerlessRelativeHierarchySemantics.class_formula_l K, map_formula_l,
    PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l,
    up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here]
  refine ⟨U, hUC, hU, hUOnto, ?_⟩
  apply (PowerlessSourceRebinding.formula_l _ (η.pushBound U)).mpr
  rw [PowerlessSourceOpening.push_l, opening_l]
  exact (number_body_formula_l K φ η B C ω Q e t₀ t₁ t₂ a D U).mpr
    ⟨A, T, H, hA, hField, hH, hIso, ⟨hFixed, hFixed₀⟩, hTargetClass, hCondensation⟩

/-- 读回同一实际程序的原见证，供后续类图构造装配使用。 -/
theorem witnesses_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (Φ : PowerlessClassFiniteElementarity.family_m []) (η : Env 𝒱 [] Δ)
    (ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a G S P s t D : Term ℒ [] Δ .set)
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
    (hAlphabet : ∀ q, ε q (Q.eval η) ↔ PowerlessRelativeFiniteProgramAlphabet.instruction_l
      (C.eval η) (ω.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) q)
    (hDomain : PowerlessRelativeFiniteProgramDomain.domain_l (B.eval η) (ω.eval η) (Q.eval η) (S.eval η) (P.eval η))
    (hBC : ε (B.eval η) (C.eval η)) (hs : ε (s.eval η) (C.eval η)) (htC : ε (t.eval η) (C.eval η))
    (hst : s.eval η ≠ t.eval η)
    (hD : ∀ x, ε x (D.eval η) → ∀ z, ε z x → ε z (D.eval η))
    (hDC : ∀ x, ε x (D.eval η) → ε x (C.eval η)) (hDC₀ : ε (D.eval η) (C.eval η))
    (hBD : ε (B.eval η) (D.eval η)) (hωD : ε (ω.eval η) (D.eval η)) :
    let Ψ := PowerlessClassProgramFiniteRequests.family_m
      (PowerlessClassFiniteElementarity.requests_m (family_m Φ)) B parameters_m
    let φ := PowerlessClassProgramHull.operator_m Ψ ω e r₁ r₂ r₃ Pair Valid B P₀ s t
    ∃ U : Raw, PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) U ∧
      map_l (ℳ := 𝒱) U (ω.eval η) (P.eval η) ∧
      (∀ p, ε p (P.eval η) → ∃ n, ε n (ω.eval η) ∧ value_l (ℳ := 𝒱) U n p) ∧
      let ψ := number_m φ (up B) (up C) (up ω) (up Q) (up e) (up t₀) (up t₁) (up t₂)
        (up a) (.bvar .here)
      ∃ A T H : Raw, PowerlessDefinableMembershipDiagram.spec_l ψ (η.pushFree U) (ω.eval η) A ∧
        PowerlessDefinableMembershipCollapse.domain_l (𝒩 := 𝒱) A (ω.eval η) ∧
          SecondOrderCollapseFunction.spec_l hℳ A (ω.eval η) T H ∧
            PowerlessDefinableWholeCollapse.isomorphism_l ψ (η.pushFree U) (ω.eval η) T H ∧
              ((∀ x, ε x (D.eval η) → ε x T ∧
                PowerlessDefinableMembershipIsomorphism.project_l ψ (η.pushFree U) (ω.eval η) H x x) ∧
              ε (D.eval η) T ∧ PowerlessDefinableMembershipIsomorphism.project_l ψ
                (η.pushFree U) (ω.eval η) H (D.eval η) (D.eval η)) ∧
              PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) T ∧
                ∃ J, PowerlessRelativeCollapseStageIndex.spec_l (B.eval η) T J ∧
                  SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) J ∧
                    PowerlessRelativeHierarchySemantics.limit_l hℳ J ∧
                      PowerlessRelativeHierarchySemantics.level_l hℳ (B.eval η) J T := by
  have hMode := mode_l K Φ η ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a G S P s t D hCoding hω
  simp only [mode_m, Formula.satisfies, guard_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, map_formula_l,
    PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l,
    PowerlessDefinableFiniteTraceDerives.zero_formula_l,
    PowerlessRelativeFiniteProgramStep.record_formula_l,
    PowerlessRelativeFiniteProgramInstruction.tags_m,
    PowerlessRelativeFiniteProgramAlphabet.alphabet_formula_l,
    PowerlessRelativeFiniteProgramDomain.domain_formula_l K,
    PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ, subset_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval] at hMode
  have hResult := (hMode hGuard hC hωC hQ hG h₀ h₁ h₂ hMap hOnto he ha ht hAlphabet
    hDomain hBC hs htC hst hD hDC hDC₀ hBD hωD).2
  simp only [Formula.satisfies,
    PowerlessRelativeHierarchySemantics.class_formula_l K, map_formula_l,
    PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l,
    up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here] at hResult
  obtain ⟨U, hUC, hU, hUOnto, hBody⟩ := hResult
  rw [PowerlessSourceRebinding.formula_l, PowerlessSourceOpening.push_l, opening_l] at hBody
  exact ⟨U, hUC, hU, hUOnto, (number_body_formula_l K _ η B C ω Q e t₀ t₁ t₂ a D U).mp hBody⟩

private def body_m {Δ Θ : SortContext ℒ} (Φ : PowerlessClassFiniteElementarity.family_m [])
    (ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a G S P s t D : Term ℒ Δ Θ .set) : Formula ℒ Δ Θ :=
  let τ := @PowerlessSourceRebinding.term_m Δ Θ
  PowerlessSourceRebinding.formula_m <|
    mode_m Φ (τ ω) (τ e) (τ r₁) (τ r₂) (τ r₃) (τ Pair) (τ Valid) (τ B) (τ P₀)
      (τ C) (τ Q) (τ t₀) (τ t₁) (τ t₂) (τ a) (τ G) (τ S) (τ P) (τ s) (τ t) (τ D)

def schema_m {Δ : SortContext ℒ} (Φ : PowerlessClassFiniteElementarity.family_m [])
    (ω e B P₀ C Q t₀ t₁ t₂ a G S P s t D : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <|
      body_m Φ (up₅ ω) (up₅ e) (.bvar (.there (.there (.there (.there .here)))))
        (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here)))
        (.bvar (.there .here)) (.bvar .here) (up₅ B) (up₅ P₀) (up₅ C) (up₅ Q)
        (up₅ t₀) (up₅ t₁) (up₅ t₂) (up₅ a) (up₅ G) (up₅ S) (up₅ P) (up₅ s) (up₅ t) (up₅ D)

def sentence_m {Δ : SortContext ℒ} (Φ : PowerlessClassFiniteElementarity.family_m [])
    (ω e B P₀ C Q t₀ t₁ t₂ a G S P s t D : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m Φ ω e B P₀ C Q t₀ t₁ t₂ a G S P s t D)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (Φ : PowerlessClassFiniteElementarity.family_m [])
    (ω e B P₀ C Q t₀ t₁ t₂ a G S P s t D : Term ℒ [] Δ .set) :
    (sentence_m Φ ω e B P₀ C Q t₀ t₁ t₂ a G S P s t D).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
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

theorem derives_m {Δ : SortContext ℒ} (Φ : PowerlessClassFiniteElementarity.family_m [])
    (ω e B P₀ C Q t₀ t₁ t₂ a G S P s t D : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m Φ ω e B P₀ C Q t₀ t₁ t₂ a G S P s t D)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ h𝒩 => models_l h𝒩 Φ ω e B P₀ C Q t₀ t₁ t₂ a G S P s t D)

#print axioms derives_m
#print axioms witnesses_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassProgramCondensation
