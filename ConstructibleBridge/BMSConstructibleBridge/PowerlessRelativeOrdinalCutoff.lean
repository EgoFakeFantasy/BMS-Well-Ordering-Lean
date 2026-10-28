import BMSConstructibleBridge.PowerlessWeakSetInduction
import BMSConstructibleBridge.PowerlessRelativeClassValueCoordinates
import BMSConstructibleBridge.SecondOrderOrdinalComparison

/-! # 相对类内可数序数的实际分界

可数性要求单射图属于给定相对类，不能用环境可数枚举代替。使用原模型
可定义类的隶属极小元，得到全部序数类内可数，或唯一首个类内不可数序数
的二分。全部量词包含模型内部非标准对象；不调用 Collection，也不在
Type 中固定分支或序数。最后将带实际 ω 与传递基集 guard 的闭句回传 Z₂。
本文件尚不证明截断域满足完整 Separation 或 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeOrdinalCutoff

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderObjectSyntax (member_m map_m injective_m)
open PowerlessRelativeHierarchySyntax (class_m ordinal_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def countable_m {Γ Δ : SortContext ℒ} (B ω a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .conj (class_m (up B) (.bvar .here)) <|
    .conj (map_m (.bvar .here) (up a) (up ω)) (injective_m (.bvar .here))

def first_m {Γ Δ : SortContext ℒ} (B ω α : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (ordinal_m α) <| .conj (.neg (countable_m B ω α)) <|
    .forallE .set <| .imp (member_m (.bvar .here) (up α)) (countable_m (up B) (up ω) (.bvar .here))

def dichotomy_m {Γ Δ : SortContext ℒ} (B ω : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (.forallE .set (.imp (ordinal_m (.bvar .here)) (countable_m (up B) (up ω) (.bvar .here)))) <|
    .existsE .set <| .conj (first_m (up B) (up ω) (.bvar .here)) <|
      .forallE .set <| .imp (first_m (up (up B)) (up (up ω)) (.bvar .here))
        (.equal (.bvar .here) (.bvar (.there .here)))

def sentence_m : Sentence ℒ :=
  .forallE .set <| .forallE .set <| .imp
    (.conj (PowerlessRelativeHierarchyDerives.transitive_m (.bvar (.there .here)))
      (SecondOrderOmegaSyntax.omega_m (.bvar .here)))
    (dichotomy_m (.bvar (.there .here)) (.bvar .here))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def countable_l (B ω a : type_l hℳ) : Prop :=
  ∃ f, PowerlessRelativeClassCorrespondence.member_l hℳ B f ∧
    ThirdOrderSemantics.map_l (ℳ := 𝒱) f a ω ∧ ThirdOrderSemantics.injective_l (ℳ := 𝒱) f

def first_l (B ω α : type_l hℳ) : Prop :=
  SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) α ∧
    ¬countable_l B ω α ∧ ∀ β, mem_l hℳ β α → countable_l B ω β

theorem countable_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (B ω a : Term ℒ Γ Δ .set) :
    (countable_m B ω a).satisfies η ↔ countable_l (B.eval η) (ω.eval η) (a.eval η) := by
  simp only [countable_m, countable_l, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.class_formula_l K, map_formula_l, injective_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  rfl

theorem first_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (B ω α : Term ℒ Γ Δ .set) :
    (first_m B ω α).satisfies η ↔ first_l (B.eval η) (ω.eval η) (α.eval η) := by
  simp only [first_m, first_l, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.ordinal_formula_l, countable_formula_l K,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem first_unique_l {B ω α β : type_l hℳ} (hα : first_l B ω α) (hβ : first_l B ω β) : α = β := by
  rcases SecondOrderOrdinalComparison.compare_l hℳ hα.1 hβ.1 with h | h | h
  · exact h
  · exact False.elim (hα.2.1 (hβ.2.2 α h))
  · exact False.elim (hβ.2.1 (hα.2.2 β h))

theorem dichotomy_l (K : source_coding_l hℳ) (B ω : type_l hℳ) :
    (∀ α, SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) α →
      countable_l B ω α) ∨ ∃! α, first_l B ω α := by
  classical
  by_cases hAll : ∀ α, SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) α → countable_l B ω α
  · exact Or.inl hAll
  · obtain ⟨a, ha⟩ := not_forall.mp hAll
    obtain ⟨haOrd, haBad⟩ := Classical.not_imp.mp ha
    let φ : Formula ℒ [] [.set, .set, .set] := .conj (ordinal_m (.fvar .here))
      (.neg (countable_m (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)))
    let η : Env 𝒱 [] [.set, .set] := (Env.empty.pushFree B).pushFree ω
    have hRead α : φ.satisfies (η.pushFree α) ↔
        SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) α ∧
          ¬countable_l B ω α := by
      simp only [φ, Formula.satisfies, PowerlessRelativeHierarchySemantics.ordinal_formula_l,
        countable_formula_l K, Term.eval]
      rfl
    obtain ⟨α, hα, hMin⟩ := PowerlessWeakSetInduction.minimum_l
      (SecondOrderWeakSetTheory.models_l hℳ) φ η ⟨a, (hRead a).mpr ⟨haOrd, haBad⟩⟩
    obtain ⟨hαOrd, hαBad⟩ := (hRead α).mp hα
    have hFirst : first_l B ω α := by
      refine ⟨hαOrd, hαBad, fun β hβ => ?_⟩
      by_contra hBad
      exact hMin β hβ ((hRead β).mpr ⟨SetTheory.Structure.IsOrdinal.mem hαOrd hβ, hBad⟩)
    exact Or.inr ⟨α, hFirst, fun β hβ => first_unique_l hβ hFirst⟩

theorem dichotomy_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (B ω : Term ℒ Γ Δ .set) :
    (dichotomy_m B ω).satisfies η ↔
      (∀ α, SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) α →
        countable_l (B.eval η) (ω.eval η) α) ∨ ∃! α, first_l (B.eval η) (ω.eval η) α := by
  simp only [dichotomy_m, Formula.satisfies, PowerlessRelativeHierarchySemantics.ordinal_formula_l,
    countable_formula_l K, first_formula_l K, ExistsUnique, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) : sentence_m.TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  simp only [sentence_m, Formula.TrueIn, Formula.satisfies]
  intro B ω _
  exact (dichotomy_formula_l K (((Env.empty (M := 𝒱)).pushBound B).pushBound ω)
    (.bvar (.there .here)) (.bvar .here)).mpr (dichotomy_l K B ω)

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeOrdinalCutoff
