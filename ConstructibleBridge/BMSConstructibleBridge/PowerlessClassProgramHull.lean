import BMSConstructibleBridge.PowerlessVirtualHullExtensionality
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramVirtualClosure

/-! # 同一实际程序的外延虚拟壳

纯隶属语言、原 Z₂。原有限请求族保留全部自由参数；实际规范编码包在
对象句子中存在量化。规范 Class 最小见证算子的函数性与总定义性均在
证明内取得，原程序拼接给配对及调用闭包，从而得到虚拟外延性和真实
单集上邻。没有预供这些闭包、全像集合或外部选择函数。
种子、字母表及全码域仍使用原实际构造规格；数码枚举、元素性、凝聚、
Class 层内重枚举及 Collection 尚须后续装配。本模块不是最终良序句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassProgramHull

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessBMSQuotientSubsetImageDerives
  (parameters_l parameters_pushBound_l parameters_empty_l)
open SecondOrderCanonicalLevelDerives (guard_m guard_l guard_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (v : Term ℒ Γ Δ .set) :=
  v.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (v : Term ℒ Γ Δ .set) := up (up v)
private abbrev up₃ {Γ Δ : SortContext ℒ} (v : Term ℒ Γ Δ .set) := up (up₂ v)
private abbrev up₅ {Γ Δ : SortContext ℒ} (v : Term ℒ Γ Δ .set) := up₂ (up₃ v)

def operator_m {Δ : SortContext ℒ} (Φ : List (Formula ℒ [] (.set :: .set :: Δ)))
    (ω e r₁ r₂ r₃ Pair Valid B P₀ s t : Term ℒ [] Δ .set) :
    Formula ℒ [] (.set :: .set :: Δ) :=
  SecondOrderCanonicalClassSkolem.operator_m (PowerlessClassHullRequests.family_m Φ s t)
    ω e r₁ r₂ r₃ Pair Valid B P₀

private abbrev image_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a P x : Term ℒ Γ Δ .set) :=
  PowerlessRelativeFiniteProgramVirtualClosure.image_m false φ B C ω Q e t₀ t₁ t₂ a P x

private def ext_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a P : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .forallE .set <| .forallE .set <| .imp
    (image_m φ (up₂ B) (up₂ C) (up₂ ω) (up₂ Q) (up₂ e)
      (up₂ t₀) (up₂ t₁) (up₂ t₂) (up₂ a) (up₂ P) (.bvar (.there .here))) <|
    .imp (image_m φ (up₂ B) (up₂ C) (up₂ ω) (up₂ Q) (up₂ e)
      (up₂ t₀) (up₂ t₁) (up₂ t₂) (up₂ a) (up₂ P) (.bvar .here)) <|
      .imp (.forallE .set <| .imp
        (image_m φ (up₃ B) (up₃ C) (up₃ ω) (up₃ Q) (up₃ e)
          (up₃ t₀) (up₃ t₁) (up₃ t₂) (up₃ a) (up₃ P) (.bvar .here)) <|
        .iff (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there (.there .here))))
          (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there .here))))
        (.equal (.bvar (.there .here)) (.bvar .here))

private def upper_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a P : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .forallE .set <| .imp
    (image_m φ (up B) (up C) (up ω) (up Q) (up e)
      (up t₀) (up t₁) (up t₂) (up a) (up P) (.bvar .here)) <|
    .existsE .set <| .conj
      (image_m φ (up₂ B) (up₂ C) (up₂ ω) (up₂ Q) (up₂ e)
        (up₂ t₀) (up₂ t₁) (up₂ t₂) (up₂ a) (up₂ P) (.bvar .here))
      (SecondOrderObjectSyntax.pair_m (.bvar (.there .here)) (.bvar (.there .here)) (.bvar .here))

def conclusion_m {Δ : SortContext ℒ} (Φ : List (Formula ℒ [] (.set :: .set :: Δ)))
    (ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a P s t : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  let φ := operator_m Φ ω e r₁ r₂ r₃ Pair Valid B P₀ s t
  .conj (ext_m φ B C ω Q e t₀ t₁ t₂ a P) (upper_m φ B C ω Q e t₀ t₁ t₂ a P)

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

theorem conclusion_formula_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (Φ : List (Formula ℒ [] (.set :: .set :: Δ))) (η : Env 𝒱 [] Δ)
    (ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a P s t : Term ℒ [] Δ .set) :
    let φ := operator_m Φ ω e r₁ r₂ r₃ Pair Valid B P₀ s t
    let I := PowerlessRelativeFiniteProgramVirtualClosure.image_l false φ η
      (B.eval η) (C.eval η) (ω.eval η) (Q.eval η) (e.eval η)
        (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (P.eval η)
    (conclusion_m Φ ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a P s t).satisfies η ↔
      (∀ x y, I x → I y → (∀ z, I z → (ε z x ↔ ε z y)) → x = y) ∧
      (∀ x, I x → ∃ z, I z ∧ SecondOrderPairObjects.pair_l hℳ x x z) := by
  simp only [conclusion_m, ext_m, upper_m, image_m, Formula.satisfies,
    PowerlessRelativeFiniteProgramVirtualClosure.image_formula_l K,
    SecondOrderObjectSyntax.pair_l hℳ, SecondOrderObjectSyntax.member_m, Arguments.eval,
    parameters_pushBound_l, parameters_empty_l, up₃, up₂, up, Term.eval_weakenBound,
    Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  rfl

/-- 同一规范包的函数性、总定义性及原程序真实闭包，供同构与请求捕获共用。 -/
theorem closure_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
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
    (hBC : ε (B.eval η) (C.eval η)) :
    let χ := PowerlessClassHullRequests.family_m Φ s t
    let φ := operator_m Φ ω e r₁ r₂ r₃ Pair Valid B P₀ s t
    let I := PowerlessRelativeFiniteProgramVirtualClosure.image_l false φ η
      (B.eval η) (C.eval η) (ω.eval η) (Q.eval η) (e.eval η)
        (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (P.eval η)
    PowerlessRelativeFiniteProgramInstruction.functional_l φ η (B.eval η) ∧
    (∀ x, I x → PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) x) ∧
    (∀ x, ε x (C.eval η) → I x) ∧
    (∀ x y, I x → I y → ∃ p, I p ∧ ordered_l (ℳ := 𝒱) x y p) ∧
    (∀ q z, I q → PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) z →
      SecondOrderCanonicalClassSkolem.relation_l χ η (ω.eval η) (e.eval η)
        (r₁.eval η) (r₂.eval η) (r₃.eval η) (Pair.eval η) (Valid.eval η)
          (B.eval η) (P₀.eval η) q z → I z) ∧
    (∀ q, ∃ z, PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) z ∧
      SecondOrderCanonicalClassSkolem.relation_l χ η (ω.eval η) (e.eval η)
        (r₁.eval η) (r₂.eval η) (r₃.eval η) (Pair.eval η) (Valid.eval η)
          (B.eval η) (P₀.eval η) q z) := by
  let χ := PowerlessClassHullRequests.family_m Φ s t
  let φ := operator_m Φ ω e r₁ r₂ r₃ Pair Valid B P₀ s t
  let I := PowerlessRelativeFiniteProgramVirtualClosure.image_l false φ η
    (B.eval η) (C.eval η) (ω.eval η) (Q.eval η) (e.eval η)
      (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (P.eval η)
  have hB : ∀ x, ε x (B.eval η) → ∀ z, ε z x → ε z (B.eval η) :=
    fun x hx z hz => hGuard.2.1 x z hx hz
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  have heEq : e.eval η = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val :=
    SecondOrderQuotient.ext_l hℳ _ _ (fun x =>
      ⟨fun hx => (he x hx).elim, fun hx => (PowerlessBMSQuotientSuccessor.zero_l K x hx).elim⟩)
  have hφ : PowerlessRelativeFiniteProgramInstruction.functional_l φ η (B.eval η) := by
    simpa only [φ, operator_m, opening_l] using
      SecondOrderCanonicalClassSkolem.functional_l K χ η ω e r₁ r₂ r₃ Pair Valid B P₀
        hωEq heEq hCoding hGuard
  have hClosure := PowerlessRelativeFiniteProgramVirtualClosure.closure_l K φ η B C ω Q e
    t₀ t₁ t₂ a S P hB hC hω hωC hQ he ha ht
      (by simpa only [parameters_empty_l] using hφ) hAlphabet hDomain hBC
  simp only [parameters_empty_l] at hClosure
  have hClass (x : Raw) (hx : I x) := PowerlessRelativeFiniteProgramVirtualClosure.class_l φ η hx
  have hCall (q z : Raw) (hq : I q)
      (hz : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) z)
      (hRel : SecondOrderCanonicalClassSkolem.relation_l χ η (ω.eval η) (e.eval η)
        (r₁.eval η) (r₂.eval η) (r₃.eval η) (Pair.eval η) (Valid.eval η)
          (B.eval η) (P₀.eval η) q z) : I z := by
    apply hClosure.2.2.2 q z hq hz
    simpa only [φ, operator_m, χ, parameters_empty_l, opening_l] using
      (SecondOrderCanonicalClassSkolem.operator_formula_l K χ η ω e r₁ r₂ r₃ Pair Valid B P₀ q z).mpr
        (by simpa only [parameters_empty_l] using hRel)
  have hTotal (q : Raw) : ∃ z, PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) z ∧
      SecondOrderCanonicalClassSkolem.relation_l χ η (ω.eval η) (e.eval η)
        (r₁.eval η) (r₂.eval η) (r₃.eval η) (Pair.eval η) (Valid.eval η)
          (B.eval η) (P₀.eval η) q z := by
    obtain ⟨z, hz, _⟩ := SecondOrderCanonicalClassSkolem.result_l K hCoding hGuard χ η q
    change SecondOrderCanonicalClassSkolem.relation_l χ η K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val (r₁.eval η) (r₂.eval η)
        (r₃.eval η) (Pair.eval η) (Valid.eval η) (B.eval η) (P₀.eval η) q z at hz
    have hz' : SecondOrderCanonicalClassSkolem.relation_l χ η (ω.eval η) (e.eval η)
        (r₁.eval η) (r₂.eval η) (r₃.eval η) (Pair.eval η) (Valid.eval η)
          (B.eval η) (P₀.eval η) q z := by simpa only [hωEq, heEq] using hz
    exact ⟨z, SecondOrderCanonicalClassSkolem.class_l χ η hGuard hz', hz'⟩
  exact ⟨hφ, hClass, hClosure.1, hClosure.2.2.1, hCall, hTotal⟩

/-- 外延性与单集上邻不另作前提，均消费同一实际闭包。 -/
theorem hull_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
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
    let φ := operator_m Φ ω e r₁ r₂ r₃ Pair Valid B P₀ s t
    let I := PowerlessRelativeFiniteProgramVirtualClosure.image_l false φ η
      (B.eval η) (C.eval η) (ω.eval η) (Q.eval η) (e.eval η)
        (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (P.eval η)
    (∀ x y, I x → I y → (∀ z, I z → (ε z x ↔ ε z y)) → x = y) ∧
    (∀ x, I x → ∃ z, I z ∧ SecondOrderPairObjects.pair_l hℳ x x z) := by
  obtain ⟨_, hClass, hSeed, hPair, hCall, hTotal⟩ := closure_l K Φ η
    ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a S P s t
      hCoding hω hGuard hC hωC hQ he ha ht hAlphabet hDomain hBC
  have hB : ∀ x, ε x (B.eval η) → ∀ z, ε z x → ε z (B.eval η) :=
    fun x hx z hz => hGuard.2.1 x z hx hz
  exact ⟨PowerlessVirtualHullExtensionality.extensional_l Φ η s t _ hB hst hClass
    (hSeed _ hs) hPair hCall hTotal,
    PowerlessVirtualHullExtensionality.upper_l Φ η s t _ hB hst hClass
      (hSeed _ hs) (hSeed _ htC) hPair hCall hTotal⟩

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
  apply (conclusion_formula_l K Φ η ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a P s t).mpr
  exact hull_l K Φ η ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a S P s t
    hCoding hω hGuard hC hωC hQ he ha ht hAlphabet hDomain hBC hs htC hst

/-- 开放新增编码槽，原请求正文仅加入对应前缀，其原自由参数保持在尾部。 -/
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

#print axioms conclusion_formula_l
#print axioms closure_l
#print axioms hull_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassProgramHull
