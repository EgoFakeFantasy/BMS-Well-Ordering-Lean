import BMSConstructibleBridge.PowerlessRelativeFiniteProgramRelocation

/-! # 父坐标重编号保持同一指令的完整计算关系

只要求两张存储图在实际映射的父坐标上读数精确相同。三标签解析后，
原 good 分支逐一对应，故缺失父坐标、无 Class 算子输出时的缺省 B 分支
也精确保持。没有仅验证成功输出而忽略总化分支，也不预设整段执行保持。
对象出口是原 Z₂ 中 computed 矩阵的逐值等价。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramRelocationComputed

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeFiniteProgramInstruction (good_l computed_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_pushBound_l parameters_empty_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)

def reading_m {Γ Δ : SortContext ℒ} (A f g : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .imp
    (SecondOrderObjectSyntax.value_m (up₂ A) (.bvar (.there .here)) (.bvar .here)) <|
      .forallE .set <| .iff
        (SecondOrderObjectSyntax.value_m (up₃ f) (.bvar (.there (.there .here))) (.bvar .here))
        (SecondOrderObjectSyntax.value_m (up₃ g) (.bvar (.there .here)) (.bvar .here))

def result_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C f g t₀ t₁ t₂ q r : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .iff
    (PowerlessRelativeFiniteProgramInstruction.computed_m φ (up B) (up C) (up f)
      (up t₀) (up t₁) (up t₂) (up q) (.bvar .here))
    (PowerlessRelativeFiniteProgramInstruction.computed_m φ (up B) (up C) (up g)
      (up t₀) (up t₁) (up t₂) (up r) (.bvar .here))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def reading_l (A f g : type_l hℳ) : Prop :=
  ∀ k i, value_l (ℳ := 𝒱) A k i → ∀ x, value_l (ℳ := 𝒱) f k x ↔ value_l (ℳ := 𝒱) g i x

theorem reading_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ) (A f g : Term ℒ Γ Δ .set) :
    (reading_m A f g).satisfies η ↔ reading_l (A.eval η) (f.eval η) (g.eval η) := by
  simp only [reading_m, reading_l, Formula.satisfies, value_formula_l,
    up₃, up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]

private theorem constant_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {B C f t₀ t₁ t₂ a q y : type_l hℳ}
    (hTags : t₀ ≠ t₁ ∧ t₀ ≠ t₂ ∧ t₁ ≠ t₂) (ha : mem_l hℳ a C)
    (hq : ordered_l (ℳ := 𝒱) t₀ a q) : good_l φ η B C f t₀ t₁ t₂ q y ↔ y = a := by
  constructor
  · rintro (⟨b, hq', _, hy⟩ | ⟨_, _, hq', _⟩ | ⟨_, _, _, _, _, hq', _⟩)
    · exact hy.trans ((SecondOrderPairObjects.ordered_eq_l hℳ hq' hq).mp rfl).2
    · exact (hTags.1 ((SecondOrderPairObjects.ordered_eq_l hℳ hq hq').mp rfl).1).elim
    · exact (hTags.2.1 ((SecondOrderPairObjects.ordered_eq_l hℳ hq hq').mp rfl).1).elim
  · intro hy
    exact Or.inl ⟨a, hq, ha, hy⟩

private theorem call_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {B C f t₀ t₁ t₂ k q y : type_l hℳ}
    (hTags : t₀ ≠ t₁ ∧ t₀ ≠ t₂ ∧ t₁ ≠ t₂) (hq : ordered_l (ℳ := 𝒱) t₁ k q) :
    good_l φ η B C f t₀ t₁ t₂ q y ↔ ∃ x, value_l (ℳ := 𝒱) f k x ∧
      PowerlessRelativeClassCorrespondence.member_l hℳ B y ∧ φ.satisfies ((η.pushFree x).pushFree y) := by
  constructor
  · rintro (⟨_, hq', _⟩ | ⟨k', x, hq', hx, hyC, hy⟩ | ⟨_, _, _, _, _, hq', _⟩)
    · exact (hTags.1 (((SecondOrderPairObjects.ordered_eq_l hℳ hq hq').mp rfl).1.symm)).elim
    · have hk := ((SecondOrderPairObjects.ordered_eq_l hℳ hq hq').mp rfl).2
      subst k'
      exact ⟨x, hx, hyC, hy⟩
    · exact (hTags.2.2 ((SecondOrderPairObjects.ordered_eq_l hℳ hq hq').mp rfl).1).elim
  · rintro ⟨x, hx, hyC, hy⟩
    exact Or.inr (Or.inl ⟨k, x, hq, hx, hyC, hy⟩)

private theorem pair_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {B C f t₀ t₁ t₂ k l p q y : type_l hℳ}
    (hTags : t₀ ≠ t₁ ∧ t₀ ≠ t₂ ∧ t₁ ≠ t₂)
    (hp : ordered_l (ℳ := 𝒱) k l p) (hq : ordered_l (ℳ := 𝒱) t₂ p q) :
    good_l φ η B C f t₀ t₁ t₂ q y ↔ ∃ x z,
      value_l (ℳ := 𝒱) f k x ∧ value_l (ℳ := 𝒱) f l z ∧ ordered_l (ℳ := 𝒱) x z y := by
  constructor
  · rintro (⟨_, hq', _⟩ | ⟨_, _, hq', _⟩ | ⟨p', k', l', x, z, hq', hp', hx, hz, hy⟩)
    · exact (hTags.2.1 (((SecondOrderPairObjects.ordered_eq_l hℳ hq hq').mp rfl).1.symm)).elim
    · exact (hTags.2.2 (((SecondOrderPairObjects.ordered_eq_l hℳ hq hq').mp rfl).1.symm)).elim
    · have hpp := ((SecondOrderPairObjects.ordered_eq_l hℳ hq hq').mp rfl).2
      subst p'
      obtain ⟨hkk, hll⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hp hp').mp rfl
      subst k'
      subst l'
      exact ⟨x, z, hx, hz, hy⟩
  · rintro ⟨x, z, hx, hz, hy⟩
    exact Or.inr (Or.inr ⟨p, k, l, x, z, hq, hp, hx, hz, hy⟩)

theorem good_congr_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {B C ω A f g t₀ t₁ t₂ q r : type_l hℳ}
    (hTags : t₀ ≠ t₁ ∧ t₀ ≠ t₂ ∧ t₁ ≠ t₂)
    (hRelocation : PowerlessRelativeFiniteProgramRelocation.relation_l C ω A t₀ t₁ t₂ q r)
    (hRead : reading_l A f g) (y : type_l hℳ) :
    good_l φ η B C f t₀ t₁ t₂ q y ↔ good_l φ η B C g t₀ t₁ t₂ r y := by
  rcases hRelocation with ⟨a, ha, hq, rfl⟩ | ⟨k, i, _, hi, hq, hr⟩ |
    ⟨k, l, p, i, j, s, _, _, hp, hq, hi, hj, hs, hr⟩
  · rw [constant_l φ η hTags ha hq, constant_l φ η hTags ha hq]
  · rw [call_l φ η hTags hq, call_l φ η hTags hr]
    exact exists_congr fun x => and_congr (hRead k i hi x) Iff.rfl
  · rw [pair_l φ η hTags hp hq, pair_l φ η hTags hs hr]
    exact exists_congr fun x => exists_congr fun z =>
      and_congr (hRead k i hi x) (and_congr (hRead l j hj z) Iff.rfl)

theorem computed_congr_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {B C ω A f g t₀ t₁ t₂ q r : type_l hℳ}
    (hTags : t₀ ≠ t₁ ∧ t₀ ≠ t₂ ∧ t₁ ≠ t₂)
    (hRelocation : PowerlessRelativeFiniteProgramRelocation.relation_l C ω A t₀ t₁ t₂ q r)
    (hRead : reading_l A f g) (y : type_l hℳ) :
    computed_l φ η B C f t₀ t₁ t₂ q y ↔ computed_l φ η B C g t₀ t₁ t₂ r y := by
  have hGood := good_congr_l φ η (B := B) hTags hRelocation hRead
  simp only [computed_l, hGood]

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω A f g t₀ t₁ t₂ q r : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeFiniteProgramInstruction.tags_m t₀ t₁ t₂) <|
    .imp (PowerlessRelativeFiniteProgramRelocation.formula_m C ω A t₀ t₁ t₂ q r) <|
      .imp (reading_m A f g) (result_m φ B C f g t₀ t₁ t₂ q r)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω A f g t₀ t₁ t₂ q r : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B C ω A f g t₀ t₁ t₂ q r)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (B C ω A f g t₀ t₁ t₂ q r : Term ℒ [] Δ .set) :
    (sentence_m φ B C ω A f g t₀ t₁ t₂ q r).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, result_m, Formula.satisfies,
    PowerlessRelativeFiniteProgramInstruction.tags_m, PowerlessRelativeFiniteProgramRelocation.formula_l,
    reading_formula_l, PowerlessRelativeFiniteProgramInstruction.computed_formula_l K,
    parameters_pushBound_l, parameters_empty_l, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here]
  intro η hTags hRelocation hRead y
  exact computed_congr_l φ η hTags hRelocation hRead y

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω A f g t₀ t₁ t₂ q r : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B C ω A f g t₀ t₁ t₂ q r)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 φ B C ω A f g t₀ t₁ t₂ q r)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramRelocationComputed
