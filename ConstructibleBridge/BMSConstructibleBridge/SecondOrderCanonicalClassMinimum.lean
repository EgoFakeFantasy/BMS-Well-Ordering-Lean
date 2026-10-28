import BMSConstructibleBridge.SecondOrderCanonicalClassOrder
import BMSConstructibleBridge.SecondOrderCanonicalLevelDerives

/-! # 规范类序下可定义候选的唯一最小元：原 Z₂ 模式

模式参数是实际纯公式及其有限自由参数，不是任意宿主谓词。保留同一
原图翻译，通过任意原 Z₂ 模型的商语义与既有完备性接口回到 Derives。
只在一个候选所在层内分离；没有声称全体候选构成集合或共同有界。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalClassMinimum

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeHierarchySyntax (class_m)
open PowerlessWeakSetInduction (at_m at_formula_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_l parameters_pushBound_l parameters_empty_l)
open SecondOrderCanonicalClassOrder (edge_m edge_l edge_formula_l)
open SecondOrderCanonicalLevelDerives (guard_m guard_l guard_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)
private abbrev up₆ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up₃ (up₃ t)

def minimum_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (ω e t₁ t₂ t₃ Pair Valid B P₀ x : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (class_m B x) <| .conj (at_m φ x) <|
    .forallE .set <| .imp (at_m φ (.bvar .here)) <|
      .neg (edge_m (up ω) (up e) (up t₁) (up t₂) (up t₃) (up Pair) (up Valid)
        (up B) (up P₀) (.bvar .here) (up x))

def mode_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (ω e t₁ t₂ t₃ Pair Valid : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <|
    let B : Term ℒ (.set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let P₀ := .bvar .here
    .imp (guard_m B P₀) <|
      .imp (.existsE .set (.conj (class_m (up B) (.bvar .here)) (at_m φ (.bvar .here)))) <|
        .existsE .set <|
          .conj (minimum_m φ (up₃ ω) (up₃ e) (up₃ t₁) (up₃ t₂) (up₃ t₃)
            (up₃ Pair) (up₃ Valid) (up B) (up P₀) (.bvar .here)) <|
            .forallE .set <|
              .imp (minimum_m φ (up (up₃ ω)) (up (up₃ e)) (up (up₃ t₁)) (up (up₃ t₂))
                (up (up₃ t₃)) (up (up₃ Pair)) (up (up₃ Valid)) (up₂ B) (up₂ P₀) (.bvar .here))
                (.equal (.bvar .here) (.bvar (.there .here)))

def total_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) (ω : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .existsE .set <| .existsE .set <| .existsE .set <|
      .existsE .set <| .existsE .set <| .existsE .set <|
        mode_m φ (up₆ ω) (.bvar (.there (.there (.there (.there (.there .here))))))
          (.bvar (.there (.there (.there (.there .here))))) (.bvar (.there (.there (.there .here))))
          (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) : Formula ℒ [] Δ :=
  .forallE .set (total_m φ (.bvar .here))

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
private abbrev zero_l (K : source_coding_l hℳ) := (numberCode_l K (SecondOrderModel.zero_l ℳ)).val

def minimum_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) (η : Env 𝒱 [] Δ)
    (ω e t₁ t₂ t₃ Pair Valid B P₀ x : SecondOrderQuotient.type_l hℳ) : Prop :=
  PowerlessRelativeClassCorrespondence.member_l hℳ B x ∧ φ.satisfies (η.pushFree x) ∧
    ∀ y, φ.satisfies (η.pushFree y) → ¬edge_l ω e t₁ t₂ t₃ Pair Valid B P₀ y x

theorem minimum_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) (η : Env 𝒱 Γ Δ)
    (ω e t₁ t₂ t₃ Pair Valid B P₀ x : Term ℒ Γ Δ .set) :
    (minimum_m φ ω e t₁ t₂ t₃ Pair Valid B P₀ x).satisfies η ↔
      minimum_l φ (parameters_l η) (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
        (Pair.eval η) (Valid.eval η) (B.eval η) (P₀.eval η) (x.eval η) := by
  simp only [minimum_m, minimum_l, Formula.satisfies, PowerlessRelativeHierarchySemantics.class_formula_l K,
    at_formula_l, edge_formula_l K, parameters_pushBound_l, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem mode_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) (η : Env 𝒱 Γ Δ)
    (ω e t₁ t₂ t₃ Pair Valid : Term ℒ Γ Δ .set) :
    (mode_m φ ω e t₁ t₂ t₃ Pair Valid).satisfies η ↔
      ∀ B P₀, guard_l B P₀ →
        (∃ x, PowerlessRelativeClassCorrespondence.member_l hℳ B x ∧
          φ.satisfies ((parameters_l η).pushFree x)) →
        ∃! x, minimum_l φ (parameters_l η) (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η)
          (t₃.eval η) (Pair.eval η) (Valid.eval η) B P₀ x := by
  simp only [mode_m, Formula.satisfies, ExistsUnique, guard_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, at_formula_l, minimum_formula_l K,
    parameters_pushBound_l, up₃, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem exists_unique_l (K : source_coding_l hℳ)
    {t₁ t₂ t₃ Pair Valid B P₀ : SecondOrderQuotient.type_l hℳ}
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
    (hGuard : guard_l B P₀) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) (η : Env 𝒱 [] Δ)
    (hSome : ∃ x, PowerlessRelativeClassCorrespondence.member_l hℳ B x ∧ φ.satisfies (η.pushFree x)) :
    ∃! x, minimum_l φ η K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ x := by
  have hBase x hx y hy := hGuard.2.1 x y hx hy
  obtain ⟨x, hx⟩ := SecondOrderCanonicalClassOrder.minimum_l K hCoding
    hGuard.1 hBase hGuard.2.2.1 hGuard.2.2.2 φ η hSome
  refine ⟨x, hx, ?_⟩
  intro y hy
  rcases SecondOrderCanonicalClassOrder.compare_l K hCoding
    hGuard.1 hBase hGuard.2.2.1 hGuard.2.2.2 hy.1 hx.1 with hyx | hEq | hxy
  · exact False.elim (hx.2.2 y hy.2.1 hyx)
  · exact hEq
  · exact False.elim (hy.2.2 x hx.2.1 hxy)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) : (sentence_m φ).TrueIn 𝒱 := by
  obtain ⟨K₀⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, total_m, Formula.satisfies, omega_formula_l,
    up₆, up₃, up₂, up, Term.eval]
  intro ω hω
  obtain ⟨K, e, t₁, t₂, t₃, Pair, Valid, hωEq, he, hCoding⟩ := SecondOrderComparisonCoding.exists_l hω
  refine ⟨e, t₁, t₂, t₃, Pair, Valid, ?_⟩
  rw [mode_formula_l K₀]
  simp only [parameters_pushBound_l, parameters_empty_l, Term.eval_weakenBound, Term.eval]
  rw [hωEq, he]
  intro B P₀ hGuard hSome
  exact exists_unique_l K hCoding hGuard φ η hSome

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ φ)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalClassMinimum
