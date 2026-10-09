import BMSConstructibleBridge.SecondOrderCanonicalLevel
import BMSConstructibleBridge.SecondOrderComparisonCoding

/-! # 全体实际层的唯一相容规范序：原 Z₂ 对象推导

同一编码包在所有基底和阶段之前固定。给定非空传递基底及其完整初始
良序图，每个原层都有唯一规范序，较早层为较晚层的初段。出口是原
二阶算术推导核中纯集合句的实际图翻译，不是宿主良基性断言。
这仍是 BMS 下降证明的辅助模式，并非最终固定行数良序句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalLevelDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderObjectSyntax (member_m ordered_m)
open SecondOrderCanonicalLevelSyntax (level_m level_l level_formula_l)
open PowerlessMemberDefClosureDerives (transitive_m transitive_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)
private abbrev up₆ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up₃ (up₃ t)

def guard_m {Γ Δ : SortContext ℒ} (B P₀ : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (.existsE .set (member_m (.bvar .here) (up B))) <|
    .conj (transitive_m B) <|
      .conj (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m B P₀) <|
        .forallE .set <| .imp (member_m (.bvar .here) (up P₀)) <|
          .existsE .set <| .existsE .set <|
            .conj (member_m (.bvar (.there .here)) (up₃ B)) <|
              .conj (member_m (.bvar .here) (up₃ B))
                (ordered_m (.bvar (.there .here)) (.bvar .here) (.bvar (.there (.there .here))))

def totality_m {Γ Δ : SortContext ℒ}
    (ω e t₁ t₂ t₃ Pair Valid B P₀ : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <|
    let a : Term ℒ (.set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let X := .bvar .here
    .imp (PowerlessRelativeHierarchySyntax.level_m (up₂ B) a X) <|
      .existsE .set <|
        let P : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar .here
        .conj (level_m (up₃ ω) (up₃ e) (up₃ t₁) (up₃ t₂) (up₃ t₃) (up₃ Pair)
          (up₃ Valid) (up₃ B) (up₃ P₀) (up a) (up X) P) <|
          .conj (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m (up X) P) <|
            .forallE .set <|
              .imp (level_m (up (up₃ ω)) (up (up₃ e)) (up (up₃ t₁)) (up (up₃ t₂))
                (up (up₃ t₃)) (up (up₃ Pair)) (up (up₃ Valid)) (up (up₃ B)) (up (up₃ P₀))
                (up₂ a) (up₂ X) (.bvar .here)) (.equal (.bvar .here) (up P))

def coherence_m {Γ Δ : SortContext ℒ}
    (ω e t₁ t₂ t₃ Pair Valid B P₀ : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <|
    .forallE .set <| .forallE .set <| .forallE .set <|
      let a : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
        .bvar (.there (.there (.there (.there (.there .here)))))
      let X := .bvar (.there (.there (.there (.there .here))))
      let P := .bvar (.there (.there (.there .here)))
      let b := .bvar (.there (.there .here))
      let Y := .bvar (.there .here)
      let Q := .bvar .here
      .imp (member_m a b) <|
        .imp (level_m (up₆ ω) (up₆ e) (up₆ t₁) (up₆ t₂) (up₆ t₃) (up₆ Pair)
          (up₆ Valid) (up₆ B) (up₆ P₀) a X P) <|
          .imp (level_m (up₆ ω) (up₆ e) (up₆ t₁) (up₆ t₂) (up₆ t₃) (up₆ Pair)
            (up₆ Valid) (up₆ B) (up₆ P₀) b Y Q)
            (SecondOrderWellOrderCoherentUnionDerives.extension_m X P Y Q)

def mode_m {Γ Δ : SortContext ℒ} (ω e t₁ t₂ t₃ Pair Valid : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <|
    let B : Term ℒ (.set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let P₀ := .bvar .here
    .imp (guard_m B P₀) <|
      .conj (totality_m (up₂ ω) (up₂ e) (up₂ t₁) (up₂ t₂) (up₂ t₃) (up₂ Pair) (up₂ Valid) B P₀)
        (coherence_m (up₂ ω) (up₂ e) (up₂ t₁) (up₂ t₂) (up₂ t₃) (up₂ Pair) (up₂ Valid) B P₀)

def total_m {Γ Δ : SortContext ℒ} (ω : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .existsE .set <| .existsE .set <| .existsE .set <|
      .existsE .set <| .existsE .set <| .existsE .set <|
        mode_m (up₆ ω) (.bvar (.there (.there (.there (.there (.there .here))))))
          (.bvar (.there (.there (.there (.there .here))))) (.bvar (.there (.there (.there .here))))
          (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)

def schema_m : Formula ℒ [] [.set] := total_m (.fvar .here)
def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def guard_l (B P₀ : SecondOrderQuotient.type_l hℳ) : Prop :=
  (∃ b, SecondOrderQuotient.mem_l hℳ b B) ∧
  (∀ x y, SecondOrderQuotient.mem_l hℳ x B → SecondOrderQuotient.mem_l hℳ y x →
    SecondOrderQuotient.mem_l hℳ y B) ∧ wellOrder_l (ℳ := 𝒱) B P₀ ∧
  ∀ p, SecondOrderQuotient.mem_l hℳ p P₀ → ∃ x y,
    SecondOrderQuotient.mem_l hℳ x B ∧ SecondOrderQuotient.mem_l hℳ y B ∧
      SecondOrderPairObjects.ordered_l hℳ x y p

theorem guard_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ) (B P₀ : Term ℒ Γ Δ .set) :
    (guard_m B P₀).satisfies η ↔ guard_l (B.eval η) (P₀.eval η) := by
  simp only [guard_m, guard_l, Formula.satisfies, member_m, transitive_formula_l,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l, ordered_formula_l,
    up₃, up₂, up, Arguments.eval, Term.eval_weakenBound, Term.eval]
  rfl

theorem totality_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (ω e t₁ t₂ t₃ Pair Valid B P₀ : Term ℒ Γ Δ .set) :
    (totality_m ω e t₁ t₂ t₃ Pair Valid B P₀).satisfies η ↔
      ∀ a X, PowerlessRelativeHierarchySemantics.level_l hℳ (B.eval η) a X → ∃ P,
        level_l (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (Pair.eval η)
          (Valid.eval η) (B.eval η) (P₀.eval η) a X P ∧ wellOrder_l (ℳ := 𝒱) X P ∧
        ∀ Q, level_l (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (Pair.eval η)
          (Valid.eval η) (B.eval η) (P₀.eval η) a X Q → Q = P := by
  simp only [totality_m, Formula.satisfies, PowerlessRelativeHierarchySemantics.level_formula_l K,
    level_formula_l K, PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    up₃, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem coherence_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (ω e t₁ t₂ t₃ Pair Valid B P₀ : Term ℒ Γ Δ .set) :
    (coherence_m ω e t₁ t₂ t₃ Pair Valid B P₀).satisfies η ↔
      ∀ a X P b Y Q, SecondOrderQuotient.mem_l hℳ a b →
        level_l (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (Pair.eval η)
          (Valid.eval η) (B.eval η) (P₀.eval η) a X P →
        level_l (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (Pair.eval η)
          (Valid.eval η) (B.eval η) (P₀.eval η) b Y Q →
        SecondOrderWellOrderCoherentUnion.extension_l (ℳ₀ := 𝒱) X P Y Q := by
  simp only [coherence_m, Formula.satisfies, member_m, level_formula_l K,
    SecondOrderWellOrderCoherentUnionDerives.extension_formula_l,
    up₆, up₃, up₂, up, Arguments.eval, Term.eval_weakenBound, Term.eval]
  rfl

set_option maxHeartbeats 1000000 in
theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) : sentence_m.TrueIn 𝒱 := by
  obtain ⟨K₀⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, total_m, Formula.satisfies, omega_formula_l,
    up₆, up₃, up₂, up, Term.eval]
  intro hω
  let ω : SecondOrderQuotient.type_l hℳ := η.freeVal .here
  obtain ⟨K, e, t₁, t₂, t₃, Pair, Valid, hωEq, he, hCoding⟩ :=
    SecondOrderComparisonCoding.exists_l (ω := ω) hω
  refine ⟨e, t₁, t₂, t₃, Pair, Valid, ?_⟩
  simp only [mode_m, Formula.satisfies, guard_formula_l, totality_formula_l K₀, coherence_formula_l K₀,
    up₂, up, Term.eval_weakenBound, Term.eval]
  intro C P₀ hGuard
  have hTrans x hx y hy := hGuard.2.1 x y hx hy
  have hωRaw : ω = K.omega := hωEq
  change (∀ a X, PowerlessRelativeHierarchySemantics.level_l hℳ C a X → ∃ P,
    level_l ω e t₁ t₂ t₃ Pair Valid C P₀ a X P ∧ wellOrder_l (ℳ := 𝒱) X P ∧
    ∀ Q, level_l ω e t₁ t₂ t₃ Pair Valid C P₀ a X Q → Q = P) ∧
    (∀ a X P b Y Q, SecondOrderQuotient.mem_l hℳ a b →
      level_l ω e t₁ t₂ t₃ Pair Valid C P₀ a X P →
      level_l ω e t₁ t₂ t₃ Pair Valid C P₀ b Y Q →
      SecondOrderWellOrderCoherentUnion.extension_l (ℳ₀ := 𝒱) X P Y Q)
  rw [hωRaw, he]
  constructor
  · intro a X hX
    obtain ⟨P, hP, hUnique⟩ := SecondOrderCanonicalLevel.exists_unique_l K hCoding
      hGuard.1 hTrans hGuard.2.2.1 hGuard.2.2.2 hX
    exact ⟨P, hP, SecondOrderCanonicalLevel.order_l hP, hUnique⟩
  · intro a X P b Y Q hab hP hQ
    exact SecondOrderCanonicalLevel.extension_l K hCoding hab hP hQ

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms totality_formula_l
#print axioms coherence_formula_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalLevelDerives
