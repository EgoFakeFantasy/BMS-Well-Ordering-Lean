import BMSConstructibleBridge.PowerlessClassProgramHull
import BMSConstructibleBridge.PowerlessVirtualHullRequests

/-! # 同一实际程序捕获原有限请求见证

纯隶属语言、原 Z₂。纯二元求值图逐字开放原 matrix false，保留原缺省
分支及原参数。原程序的种子、配对和规范调用闭包在证明内取得，真实
标签查询捕获每条原请求的 Class 见证，不预供原全像集合或请求闭包。
规范编码包由原 Z₂ 在对象结论中存在量化；W 元素性尚须限制实际请求
的候选域，并证明同一虚拟壳位于 W。本模块不宣称凝聚或最终良序完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassProgramRequests

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessBMSQuotientSubsetImageDerives
  (parameters_l parameters_pushBound_l parameters_empty_l)
open SecondOrderCanonicalLevelDerives (guard_m guard_l guard_formula_l)
open PowerlessClassProgramHull (operator_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (v : Term ℒ Γ Δ .set) :=
  v.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (v : Term ℒ Γ Δ .set) := up (up v)
private abbrev up₃ {Γ Δ : SortContext ℒ} (v : Term ℒ Γ Δ .set) := up (up₂ v)
private abbrev up₅ {Γ Δ : SortContext ℒ} (v : Term ℒ Γ Δ .set) := up₂ (up₃ v)

/-- 只开放原求值的输入／输出绑定槽，原算子正文和自由参数不变。 -/
def evaluation_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a : Term ℒ [] Δ .set) : Formula ℒ [] (.set :: .set :: Δ) :=
  PowerlessSourceOpening.form_m <| PowerlessRelativeFiniteProgramEvaluation.matrix_m false φ
    (up₂ B) (up₂ C) (up₂ ω) (up₂ Q) (up₂ e) (up₂ t₀) (up₂ t₁) (up₂ t₂) (up₂ a)
      (.bvar (.there .here)) (.bvar .here)

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

theorem evaluation_formula_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B C ω Q e t₀ t₁ t₂ a : Term ℒ [] Δ .set) (p y : Raw) :
    (evaluation_m φ B C ω Q e t₀ t₁ t₂ a).satisfies ((η.pushFree p).pushFree y) ↔
      PowerlessRelativeFiniteProgramEvaluation.matrix_l false φ η
        (B.eval η) (C.eval η) (ω.eval η) (Q.eval η) (e.eval η)
          (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) p y := by
  have h := PowerlessSourceOpening.formula_l
    (PowerlessRelativeFiniteProgramEvaluation.matrix_m false φ
      (up₂ B) (up₂ C) (up₂ ω) (up₂ Q) (up₂ e) (up₂ t₀) (up₂ t₁) (up₂ t₂) (up₂ a)
        (.bvar (.there .here)) (.bvar .here)) ((η.pushBound p).pushBound y)
  simpa only [evaluation_m, PowerlessSourceOpening.push_l, opening_l,
    PowerlessRelativeFiniteProgramEvaluation.matrix_formula_l K,
    parameters_pushBound_l, parameters_empty_l, up₂, up, Term.eval_weakenBound,
    Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there] using h

theorem image_formula_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B C ω Q e t₀ t₁ t₂ a P : Term ℒ [] Δ .set) (x : Raw) :
    PowerlessDefinableMembershipIsomorphism.image_l
      (evaluation_m φ B C ω Q e t₀ t₁ t₂ a) η (P.eval η) x ↔
        PowerlessRelativeFiniteProgramVirtualClosure.image_l false φ η
          (B.eval η) (C.eval η) (ω.eval η) (Q.eval η) (e.eval η)
            (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (P.eval η) x := by
  simp only [PowerlessDefinableMembershipIsomorphism.image_l, evaluation_formula_l K,
    PowerlessRelativeFiniteProgramVirtualClosure.image_l,
    ThirdOrderSemantics.member_l, SecondOrderQuotient.structure_l]

def conclusion_m {Δ : SortContext ℒ} (Φ : List (Formula ℒ [] (.set :: .set :: Δ)))
    (ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a P s t : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  let φ := operator_m Φ ω e r₁ r₂ r₃ Pair Valid B P₀ s t
  PowerlessVirtualHullRequests.requests_m (evaluation_m φ B C ω Q e t₀ t₁ t₂ a) Φ B P

theorem requests_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (Φ : List (Formula ℒ [] (.set :: .set :: Δ))) (η : Env 𝒱 [] Δ)
    (ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a S P s t : Term ℒ [] Δ .set)
    (hCoding : SecondOrderComparisonStageTotal.coding_l K (r₁.eval η) (r₂.eval η)
      (r₃.eval η) (Pair.eval η) (Valid.eval η))
    (hω : SecondOrderOmega.omega_l hℳ (ω.eval η))
    (hGuard : guard_l (B.eval η) (P₀.eval η))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η))
    (hωC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (ω.eval η))
    (hQ : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (Q.eval η))
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
    (conclusion_m Φ ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a P s t).satisfies η := by
  let φ := operator_m Φ ω e r₁ r₂ r₃ Pair Valid B P₀ s t
  let θ := evaluation_m φ B C ω Q e t₀ t₁ t₂ a
  obtain ⟨_, _, hSeed, hPair, hCall, hTotal⟩ := PowerlessClassProgramHull.closure_l K Φ η
    ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a S P s t
      hCoding hω hGuard hC hωC hQ he ha ht hAlphabet hDomain hBC
  apply (PowerlessVirtualHullRequests.requests_formula_l θ Φ η B P).mpr
  intro ψ hψ
  apply (PowerlessVirtualHullRequests.closed_formula_l K θ ψ η B P).mpr
  simp only [parameters_empty_l]
  intro x hx hSome
  obtain ⟨y, hy, hψy⟩ := PowerlessVirtualHullRequests.witness_l Φ η s t _ hst
    (hSeed _ hs) (hSeed _ htC) hPair hCall hTotal ψ hψ x
      ((image_formula_l K φ η B C ω Q e t₀ t₁ t₂ a P x).mp hx) hSome
  exact ⟨y, (image_formula_l K φ η B C ω Q e t₀ t₁ t₂ a P y).mpr hy, hψy⟩

private def mode_m {Δ : SortContext ℒ} (Φ : List (Formula ℒ [] (.set :: .set :: Δ)))
    (ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a S P s t : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (guard_m B P₀) <| .imp (PowerlessRelativeHierarchySyntax.class_m B C) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B ω) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B Q) <|
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
    (ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a S P s t : Term ℒ [] Δ .set)
    (hCoding : SecondOrderComparisonStageTotal.coding_l K (r₁.eval η) (r₂.eval η)
      (r₃.eval η) (Pair.eval η) (Valid.eval η))
    (hω : SecondOrderOmega.omega_l hℳ (ω.eval η)) :
    (mode_m Φ ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a S P s t).satisfies η := by
  simp only [mode_m, Formula.satisfies, guard_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessDefinableFiniteTraceDerives.zero_formula_l,
    PowerlessRelativeFiniteProgramStep.record_formula_l,
    PowerlessRelativeFiniteProgramInstruction.tags_m,
    PowerlessRelativeFiniteProgramAlphabet.alphabet_formula_l,
    PowerlessRelativeFiniteProgramDomain.domain_formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  intro hGuard hC hωC hQ he ha ht hAlphabet hDomain hBC hs htC hst
  exact requests_l K Φ η ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a S P s t
    hCoding hω hGuard hC hωC hQ he ha ht hAlphabet hDomain hBC hs htC hst

private def body_m {Γ Δ : SortContext ℒ} (Φ : List (Formula ℒ [] (.set :: .set :: Δ)))
    (ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a S P s t : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let τ := @PowerlessSourceRebinding.term_m Γ Δ
  PowerlessSourceRebinding.formula_m <|
    mode_m (Φ.map (PowerlessRelativeFiniteProgramBoundOutput.prefix_m Γ.length))
      (τ ω) (τ e) (τ r₁) (τ r₂) (τ r₃) (τ Pair) (τ Valid) (τ B) (τ P₀) (τ C)
        (τ Q) (τ t₀) (τ t₁) (τ t₂) (τ a) (τ S) (τ P) (τ s) (τ t)

def schema_m {Δ : SortContext ℒ} (Φ : List (Formula ℒ [] (.set :: .set :: Δ)))
    (ω e B P₀ C Q t₀ t₁ t₂ a S P s t : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <|
      body_m Φ (up₅ ω) (up₅ e) (.bvar (.there (.there (.there (.there .here)))))
        (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here)))
        (.bvar (.there .here)) (.bvar .here) (up₅ B) (up₅ P₀) (up₅ C) (up₅ Q)
        (up₅ t₀) (up₅ t₁) (up₅ t₂) (up₅ a) (up₅ S) (up₅ P) (up₅ s) (up₅ t)

def sentence_m {Δ : SortContext ℒ} (Φ : List (Formula ℒ [] (.set :: .set :: Δ)))
    (ω e B P₀ C Q t₀ t₁ t₂ a S P s t : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m Φ ω e B P₀ C Q t₀ t₁ t₂ a S P s t)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (Φ : List (Formula ℒ [] (.set :: .set :: Δ)))
    (ω e B P₀ C Q t₀ t₁ t₂ a S P s t : Term ℒ [] Δ .set) :
    (sentence_m Φ ω e B P₀ C Q t₀ t₁ t₂ a S P s t).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
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
    (ω e B P₀ C Q t₀ t₁ t₂ a S P s t : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m Φ ω e B P₀ C Q t₀ t₁ t₂ a S P s t)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ h𝒩 => models_l h𝒩 Φ ω e B P₀ C Q t₀ t₁ t₂ a S P s t)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassProgramRequests
