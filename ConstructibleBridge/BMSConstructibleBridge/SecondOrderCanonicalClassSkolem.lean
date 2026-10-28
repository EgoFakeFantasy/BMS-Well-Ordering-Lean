import BMSConstructibleBridge.SecondOrderCanonicalClassMinimum
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramInstruction

/-! # 全局规范类最小见证的关系式总化

纯隶属语言、原 Z₂。任意固定纯请求正文及原有限参数：有 Class 见证
时取同一规范类序的唯一最小见证，无见证时取 B。任意 raw 请求输入
都有唯一 Class 输出；不存在输出全像集合或 Type 选择函数的假设。
原对象模式产生同一规范编码参数并证明关系的总唯一性。有限请求族
编码、程序壳元素性及凝聚尚不由本模块代替。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalClassSkolem

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessBMSQuotientSubsetImageDerives (parameters_l parameters_pushBound_l parameters_empty_l at_m at_formula_l)
open SecondOrderCanonicalClassOrder (edge_m edge_l edge_formula_l)
open SecondOrderCanonicalLevelDerives (guard_m guard_l guard_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₆ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up₂ (up₂ (up₂ t))

def relation_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω e t₁ t₂ t₃ Pair Valid B P₀ x y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (.conj (PowerlessRelativeHierarchySyntax.class_m B y) <|
    .conj (at_m φ x y) <| .forallE .set <| .imp (at_m φ (up x) (.bvar .here))
      (.neg (edge_m (up ω) (up e) (up t₁) (up t₂) (up t₃) (up Pair) (up Valid)
        (up B) (up P₀) (.bvar .here) (up y))))
    (.conj (.neg (.existsE .set <| .conj
      (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here))
      (at_m φ (up x) (.bvar .here)))) (.equal y B))

/-- 原算子输出、输入位于首两自由槽，所有规范编码参数保留在尾部。 -/
def operator_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω e t₁ t₂ t₃ Pair Valid B P₀ : Term ℒ Γ Δ .set) :
    Formula ℒ [] (.set :: .set :: (List.replicate Γ.length .set ++ Δ)) :=
  PowerlessSourceOpening.form_m (relation_m φ (up₂ ω) (up₂ e) (up₂ t₁) (up₂ t₂)
    (up₂ t₃) (up₂ Pair) (up₂ Valid) (up₂ B) (up₂ P₀) (.bvar (.there .here)) (.bvar .here))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ

private abbrev zero_l (K : source_coding_l hℳ) :=
  (numberCode_l K (SecondOrderModel.zero_l ℳ)).val

def relation_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (ω e t₁ t₂ t₃ Pair Valid B P₀ x y : Raw) : Prop :=
  SecondOrderCanonicalClassMinimum.minimum_l φ (η.pushFree x)
    ω e t₁ t₂ t₃ Pair Valid B P₀ y ∨
      (¬∃ z, PowerlessRelativeClassCorrespondence.member_l hℳ B z ∧
        φ.satisfies ((η.pushFree x).pushFree z)) ∧ y = B

theorem relation_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (ω e t₁ t₂ t₃ Pair Valid B P₀ x y : Term ℒ Γ Δ .set) :
    (relation_m φ ω e t₁ t₂ t₃ Pair Valid B P₀ x y).satisfies η ↔
      relation_l φ (parameters_l η) (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η)
        (t₃.eval η) (Pair.eval η) (Valid.eval η) (B.eval η) (P₀.eval η) (x.eval η) (y.eval η) := by
  simp only [relation_m, relation_l, SecondOrderCanonicalClassMinimum.minimum_l,
    Formula.satisfies, PowerlessRelativeHierarchySemantics.class_formula_l K,
    at_formula_l, edge_formula_l K, parameters_pushBound_l, up, Term.eval_weakenBound,
    Term.eval, Env.pushBound_bound_here]
  rfl

theorem operator_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (ω e t₁ t₂ t₃ Pair Valid B P₀ : Term ℒ Γ Δ .set) (x y : Raw) :
    (operator_m φ ω e t₁ t₂ t₃ Pair Valid B P₀).satisfies
      (((PowerlessSourceOpening.env_l η).pushFree x).pushFree y) ↔
      relation_l φ (parameters_l η) (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η)
        (t₃.eval η) (Pair.eval η) (Valid.eval η) (B.eval η) (P₀.eval η) x y := by
  have h := PowerlessSourceOpening.formula_l
    (relation_m φ (up₂ ω) (up₂ e) (up₂ t₁) (up₂ t₂) (up₂ t₃) (up₂ Pair)
      (up₂ Valid) (up₂ B) (up₂ P₀) (.bvar (.there .here)) (.bvar .here))
    ((η.pushBound x).pushBound y)
  simpa only [operator_m, PowerlessSourceOpening.push_l, relation_formula_l K,
    parameters_pushBound_l, up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there] using h

theorem result_l (K : source_coding_l hℳ) {t₁ t₂ t₃ Pair Valid B P₀ : Raw}
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
    (hGuard : guard_l B P₀) {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (x : Raw) :
    ∃! y, relation_l φ η K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ x y := by
  classical
  by_cases hSome : ∃ y, PowerlessRelativeClassCorrespondence.member_l hℳ B y ∧
      φ.satisfies ((η.pushFree x).pushFree y)
  · obtain ⟨y, hy, hUnique⟩ :=
      SecondOrderCanonicalClassMinimum.exists_unique_l K hCoding hGuard φ (η.pushFree x) hSome
    refine ⟨y, Or.inl hy, ?_⟩
    rintro z (hz | hz)
    · exact hUnique z hz
    · exact (hz.1 hSome).elim
  · refine ⟨B, Or.inr ⟨hSome, rfl⟩, ?_⟩
    rintro z (hz | hz)
    · exact (hSome ⟨z, hz.1, hz.2.1⟩).elim
    · exact hz.2

theorem class_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {ω e t₁ t₂ t₃ Pair Valid B P₀ x y : Raw}
    (hGuard : guard_l B P₀) (h : relation_l φ η ω e t₁ t₂ t₃ Pair Valid B P₀ x y) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B y := by
  rcases h with h | h
  · exact h.1
  · obtain rfl := h.2
    exact PowerlessRelativeClassCorrespondence.base_object_l hℳ
      (fun x hx z hz => hGuard.2.1 x z hx hz)

/-- 直接供原有限程序的算子守卫使用，不构造全域 Class 函数图。 -/
theorem functional_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (ω e t₁ t₂ t₃ Pair Valid B P₀ : Term ℒ Γ Δ .set)
    (hω : ω.eval η = K.omega) (he : e.eval η = zero_l K)
    (hCoding : SecondOrderComparisonStageTotal.coding_l K (t₁.eval η) (t₂.eval η)
      (t₃.eval η) (Pair.eval η) (Valid.eval η))
    (hGuard : guard_l (B.eval η) (P₀.eval η)) :
    PowerlessRelativeFiniteProgramInstruction.functional_l
      (operator_m φ ω e t₁ t₂ t₃ Pair Valid B P₀)
        (PowerlessSourceOpening.env_l η) (B.eval η) := by
  intro x y z _ _ _ hy hz
  have hy' := (operator_formula_l K φ η ω e t₁ t₂ t₃ Pair Valid B P₀ x y).mp hy
  have hz' := (operator_formula_l K φ η ω e t₁ t₂ t₃ Pair Valid B P₀ x z).mp hz
  rw [hω, he] at hy' hz'
  obtain ⟨v, _, hUnique⟩ := result_l K hCoding hGuard φ (parameters_l η) x
  exact (hUnique y hy').trans (hUnique z hz').symm

/-- 只在原候选非空时使用；缺省分支不冒充原见证。 -/
theorem witness_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {ω e t₁ t₂ t₃ Pair Valid B P₀ x y : Raw}
    (h : relation_l φ η ω e t₁ t₂ t₃ Pair Valid B P₀ x y)
    (hSome : ∃ z, PowerlessRelativeClassCorrespondence.member_l hℳ B z ∧
      φ.satisfies ((η.pushFree x).pushFree z)) : φ.satisfies ((η.pushFree x).pushFree y) := by
  rcases h with h | h
  · exact h.2.1
  · exact (h.1 hSome).elim

def conclusion_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω e t₁ t₂ t₃ Pair Valid B P₀ : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .existsE .set <| .conj
    (relation_m φ (up₂ ω) (up₂ e) (up₂ t₁) (up₂ t₂) (up₂ t₃) (up₂ Pair)
      (up₂ Valid) (up₂ B) (up₂ P₀) (.bvar (.there .here)) (.bvar .here)) <|
    .conj (PowerlessRelativeHierarchySyntax.class_m (up₂ B) (.bvar .here)) <|
      .forallE .set <| .imp
        (relation_m φ (up (up₂ ω)) (up (up₂ e)) (up (up₂ t₁)) (up (up₂ t₂))
          (up (up₂ t₃)) (up (up₂ Pair)) (up (up₂ Valid)) (up (up₂ B)) (up (up₂ P₀))
            (.bvar (.there (.there .here))) (.bvar .here))
        (.equal (.bvar .here) (.bvar (.there .here)))

theorem conclusion_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (ω e t₁ t₂ t₃ Pair Valid B P₀ : Term ℒ Γ Δ .set) :
    (conclusion_m φ ω e t₁ t₂ t₃ Pair Valid B P₀).satisfies η ↔
      ∀ x, ∃ y, relation_l φ (parameters_l η) (ω.eval η) (e.eval η) (t₁.eval η)
        (t₂.eval η) (t₃.eval η) (Pair.eval η) (Valid.eval η) (B.eval η) (P₀.eval η) x y ∧
          PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) y ∧
          ∀ z, relation_l φ (parameters_l η) (ω.eval η) (e.eval η) (t₁.eval η)
            (t₂.eval η) (t₃.eval η) (Pair.eval η) (Valid.eval η) (B.eval η) (P₀.eval η) x z → z = y := by
  simp only [conclusion_m, Formula.satisfies, relation_formula_l K,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    parameters_pushBound_l, up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  rfl

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B P₀ : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .forallE .set <| .imp (SecondOrderOmegaSyntax.omega_m (.bvar .here)) <|
    .existsE .set <| .existsE .set <| .existsE .set <|
      .existsE .set <| .existsE .set <| .existsE .set <|
        .imp (guard_m (up (up₆ B)) (up (up₆ P₀))) <|
          conclusion_m φ (.bvar (.there (.there (.there (.there (.there (.there .here)))))))
            (.bvar (.there (.there (.there (.there (.there .here))))))
            (.bvar (.there (.there (.there (.there .here)))))
            (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here)))
            (.bvar (.there .here)) (.bvar .here) (up (up₆ B)) (up (up₆ P₀))

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B P₀ : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B P₀)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) (B P₀ : Term ℒ [] Δ .set) :
    (sentence_m φ B P₀).TrueIn 𝒱 := by
  obtain ⟨K₀⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, omega_formula_l, Term.eval,
    Env.pushBound_bound_here]
  intro ω hω
  obtain ⟨K, e, t₁, t₂, t₃, Pair, Valid, hωEq, he, hCoding⟩ :=
    SecondOrderComparisonCoding.exists_l hω
  refine ⟨e, t₁, t₂, t₃, Pair, Valid, ?_⟩
  simp only [guard_formula_l, conclusion_formula_l K₀, parameters_pushBound_l,
    parameters_empty_l, up₆, up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  rw [hωEq, he]
  intro hGuard x
  obtain ⟨y, hy, hUnique⟩ := result_l K hCoding hGuard φ η x
  exact ⟨y, hy, class_l φ η hGuard hy, hUnique⟩

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B P₀ : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ B P₀)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 φ B P₀)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalClassSkolem
