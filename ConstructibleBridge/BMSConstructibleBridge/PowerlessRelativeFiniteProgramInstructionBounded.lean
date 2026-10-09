import BMSConstructibleBridge.PowerlessRelativeFiniteProgramLimitStep
import BMSConstructibleBridge.PowerlessMapBounded

/-! # 同母界内的实际指令计算正文

Kuratowski 解码和存储读数的见证留在共同层 W。Class 输出守卫
改为 W 成员守卫，缺省分支的否定存在也限制到 W；原保层定理
证明这没有删去任何可用输出。算子正文为纯 Δ₀ 时，整段指令
计算正文为纯 Δ₀。不声称任意原算子已具有这种复杂度。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramInstructionBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)
open PowerlessBMSQuotientSubsetImageDerives
  (at_m at_formula_l parameters_l parameters_pushBound_l parameters_empty_l)
open PowerlessRelativeFiniteProgramLimitStep (coordinates_l reading_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)
private abbrev up₅ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up₂ (up₃ t)

def good_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (C W f t₀ t₁ t₂ q y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (membershipLevyBound.boundedExists C <|
    .conj (PowerlessPairBounded.ordered_m (up t₀) (.bvar .here) (up q))
      (.equal (up y) (.bvar .here))) <|
    .disj (membershipLevyBound.boundedExists W <|
      membershipLevyBound.boundedExists (up W) <|
        .conj (PowerlessPairBounded.ordered_m (up₂ t₁) (.bvar (.there .here)) (up₂ q)) <|
          .conj (PowerlessValueBounded.formula_m (up₂ f) (.bvar (.there .here)) (.bvar .here))
            (at_m φ (.bvar .here) (up₂ y))) <|
      membershipLevyBound.boundedExists W <|
        membershipLevyBound.boundedExists (up W) <|
          membershipLevyBound.boundedExists (up₂ W) <|
            membershipLevyBound.boundedExists (up₃ W) <|
              membershipLevyBound.boundedExists (up (up₃ W)) <|
                let p : Term ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
                  .bvar (.there (.there (.there (.there .here))))
                let k := .bvar (.there (.there (.there .here)))
                let l := .bvar (.there (.there .here))
                let x := .bvar (.there .here)
                let z := .bvar .here
                .conj (PowerlessPairBounded.ordered_m (up₅ t₂) p (up₅ q)) <|
                  .conj (PowerlessPairBounded.ordered_m k l p) <|
                    .conj (PowerlessValueBounded.formula_m (up₅ f) k x) <|
                      .conj (PowerlessValueBounded.formula_m (up₅ f) l z)
                        (PowerlessPairBounded.ordered_m x z (up₅ y))

def computed_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C W f t₀ t₁ t₂ q y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (SecondOrderObjectSyntax.member_m y W) <| .disj
    (good_m φ C W f t₀ t₁ t₂ q y) <| .conj
      (.neg (membershipLevyBound.boundedExists W <|
        good_m φ (up C) (up W) (up f) (up t₀) (up t₁) (up t₂) (up q) (.bvar .here)))
      (.equal y B)

private theorem at_delta_l {Γ Δ : SortContext ℒ}
    {φ : Formula ℒ [] (.set :: .set :: Δ)} (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (x y : Term ℒ Γ Δ .set) : Formula.IsDelta0 membershipLevyBound (at_m φ x y) := by
  unfold at_m
  exact Formula.IsDelta0.substituteMapped
    (boundSubstitution := fun {s} (v : Variable ([] : SortContext ℒ) s) => nomatch v)
    (freeSubstitution := _) hφ

theorem good_delta_l {Γ Δ : SortContext ℒ}
    {φ : Formula ℒ [] (.set :: .set :: Δ)} (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (C W f t₀ t₁ t₂ q y : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (good_m φ C W f t₀ t₁ t₂ q y) :=
  .disj (.bounded_exists C (.conj (PowerlessPairBounded.ordered_delta_l _ _ _) (.equal _ _))) <|
    .disj (.bounded_exists W (.bounded_exists (up W) <|
      .conj (PowerlessPairBounded.ordered_delta_l _ _ _)
        (.conj (PowerlessValueBounded.delta_l _ _ _) (at_delta_l hφ _ _)))) <|
      .bounded_exists W <| .bounded_exists (up W) <| .bounded_exists (up₂ W) <|
        .bounded_exists (up₃ W) <| .bounded_exists (up (up₃ W)) <|
          .conj (PowerlessPairBounded.ordered_delta_l _ _ _) <|
            .conj (PowerlessPairBounded.ordered_delta_l _ _ _) <|
              .conj (PowerlessValueBounded.delta_l _ _ _) <|
                .conj (PowerlessValueBounded.delta_l _ _ _) (PowerlessPairBounded.ordered_delta_l _ _ _)

theorem computed_delta_l {Γ Δ : SortContext ℒ}
    {φ : Formula ℒ [] (.set :: .set :: Δ)} (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (B C W f t₀ t₁ t₂ q y : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (computed_m φ B C W f t₀ t₁ t₂ q y) :=
  .conj (.rel _ _) (.disj (good_delta_l hφ _ _ _ _ _ _ _ _)
    (.conj (.neg (.bounded_exists W (good_delta_l hφ _ _ _ _ _ _ _ _))) (.equal _ _)))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def good_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (C W f t₀ t₁ t₂ q y : type_l hℳ) : Prop :=
  (∃ a, mem_l hℳ a C ∧ ordered_l (ℳ := 𝒱) t₀ a q ∧ y = a) ∨
    (∃ k, mem_l hℳ k W ∧ ∃ x, mem_l hℳ x W ∧ ordered_l (ℳ := 𝒱) t₁ k q ∧
      value_l (ℳ := 𝒱) f k x ∧ φ.satisfies ((η.pushFree x).pushFree y)) ∨
      ∃ p, mem_l hℳ p W ∧ ∃ k, mem_l hℳ k W ∧ ∃ l, mem_l hℳ l W ∧
        ∃ x, mem_l hℳ x W ∧ ∃ z, mem_l hℳ z W ∧ ordered_l (ℳ := 𝒱) t₂ p q ∧
          ordered_l (ℳ := 𝒱) k l p ∧ value_l (ℳ := 𝒱) f k x ∧
            value_l (ℳ := 𝒱) f l z ∧ ordered_l (ℳ := 𝒱) x z y

theorem good_formula_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 Γ Δ) (C W f t₀ t₁ t₂ q y : Term ℒ Γ Δ .set) :
    (good_m φ C W f t₀ t₁ t₂ q y).satisfies η ↔ good_l φ (parameters_l η)
      (C.eval η) (W.eval η) (f.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (q.eval η) (y.eval η) := by
  simp only [good_m, good_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessPairBounded.ordered_formula_l,
    PowerlessValueBounded.formula_l, at_formula_l, parameters_pushBound_l, Arguments.eval,
    up₅, up₃, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem good_iff_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {B β W C f t₀ t₁ t₂ q y : type_l hℳ}
    (hB : ∀ x, mem_l hℳ x B → ∀ z, mem_l hℳ z x → mem_l hℳ z B)
    (hW : level_l hℳ B β W) (hf : mem_l hℳ f W) (hq : mem_l hℳ q W) (hy : mem_l hℳ y W) :
    good_l φ η C W f t₀ t₁ t₂ q y ↔
      PowerlessRelativeFiniteProgramInstruction.good_l φ η B C f t₀ t₁ t₂ q y := by
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hB hW
  constructor
  · rintro (⟨a, ha, hqa, hya⟩ | ⟨k, _, x, _, hqk, hx, hxy⟩ |
      ⟨p, _, k, _, l, _, x, _, z, _, hqp, hkl, hx, hz, hxy⟩)
    · exact Or.inl ⟨a, hqa, ha, hya⟩
    · exact Or.inr (Or.inl ⟨k, x, hqk, hx, ⟨β, W, hW, hy⟩, hxy⟩)
    · exact Or.inr (Or.inr ⟨p, k, l, x, z, hqp, hkl, hx, hz, hxy⟩)
  · rintro (⟨a, hqa, ha, hya⟩ | ⟨k, x, hqk, hx, _, hxy⟩ |
      ⟨p, k, l, x, z, hqp, hkl, hx, hz, hxy⟩)
    · exact Or.inl ⟨a, ha, hqa, hya⟩
    · exact Or.inr (Or.inl ⟨k, (coordinates_l hTrans hq hqk).2,
        x, reading_l hTrans hf hx, hqk, hx, hxy⟩)
    · have hp := (coordinates_l hTrans hq hqp).2
      obtain ⟨hk, hl⟩ := coordinates_l hTrans hp hkl
      exact Or.inr (Or.inr ⟨p, hp, k, hk, l, hl, x, reading_l hTrans hf hx,
        z, reading_l hTrans hf hz, hqp, hkl, hx, hz, hxy⟩)

theorem computed_formula_l {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B β C W f t₀ t₁ t₂ q y : Term ℒ Γ Δ .set)
    (hB : ∀ x, mem_l hℳ x (B.eval η) → ∀ z, mem_l hℳ z x → mem_l hℳ z (B.eval η))
    (hβ : limit_l hℳ (β.eval η)) (hW : level_l hℳ (B.eval η) (β.eval η) (W.eval η))
    (hBW : mem_l hℳ (B.eval η) (W.eval η))
    (hC : ∀ x, mem_l hℳ x (C.eval η) → mem_l hℳ x (W.eval η))
    (hf : mem_l hℳ (f.eval η) (W.eval η)) (hq : mem_l hℳ (q.eval η) (W.eval η))
    (hφ : PowerlessRelativeFiniteProgramLimitStep.closed_l φ (parameters_l η) (B.eval η) (W.eval η)) :
    (computed_m φ B C W f t₀ t₁ t₂ q y).satisfies η ↔
      PowerlessRelativeFiniteProgramInstruction.computed_l φ (parameters_l η)
        (B.eval η) (C.eval η) (f.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (q.eval η) (y.eval η) := by
  have hSome : (∃ z, mem_l hℳ z (W.eval η) ∧ good_l φ (parameters_l η)
      (C.eval η) (W.eval η) (f.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (q.eval η) z) ↔
      ∃ z, PowerlessRelativeFiniteProgramInstruction.good_l φ (parameters_l η)
        (B.eval η) (C.eval η) (f.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (q.eval η) z := by
    constructor
    · rintro ⟨z, hz, h⟩
      exact ⟨z, (good_iff_l φ (parameters_l η) hB hW hf hq hz).mp h⟩
    · rintro ⟨z, h⟩
      have hz := PowerlessRelativeFiniteProgramLimitStep.good_l φ (parameters_l η) hB hβ hW hC hf hφ h
      exact ⟨z, hz, (good_iff_l φ (parameters_l η) hB hW hf hq hz).mpr h⟩
  simp only [computed_m, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, good_formula_l, parameters_pushBound_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  change (mem_l hℳ (y.eval η) (W.eval η) ∧
    (good_l φ (parameters_l η) (C.eval η) (W.eval η) (f.eval η)
      (t₀.eval η) (t₁.eval η) (t₂.eval η) (q.eval η) (y.eval η) ∨
      ((¬∃ z, mem_l hℳ z (W.eval η) ∧ good_l φ (parameters_l η)
        (C.eval η) (W.eval η) (f.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (q.eval η) z) ∧
        y.eval η = B.eval η))) ↔ _
  rw [hSome]
  constructor
  · rintro ⟨hy, h⟩
    refine ⟨⟨β.eval η, W.eval η, hW, hy⟩, ?_⟩
    exact (or_congr (good_iff_l φ (parameters_l η) hB hW hf hq hy) Iff.rfl).mp h
  · intro h
    have hy := PowerlessRelativeFiniteProgramLimitStep.computed_l φ (parameters_l η) hB hβ hW hBW hC hf hφ h
    exact ⟨hy, (or_congr (good_iff_l φ (parameters_l η) hB hW hf hq hy) Iff.rfl).mpr h.2⟩

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β C W f t₀ t₁ t₂ q y : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.limit_m β) <|
      .imp (PowerlessRelativeHierarchySyntax.level_m B β W) <|
        .imp (SecondOrderObjectSyntax.member_m B W) <|
          .imp (ThirdOrderTheory.subset_m C W) <|
            .imp (SecondOrderObjectSyntax.member_m f W) <|
              .imp (SecondOrderObjectSyntax.member_m q W) <|
                .imp (PowerlessRelativeFiniteProgramLimitStep.closed_m φ B W) <|
                  .iff (computed_m φ B C W f t₀ t₁ t₂ q y)
                    (PowerlessRelativeFiniteProgramInstruction.computed_m φ B C f t₀ t₁ t₂ q y)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β C W f t₀ t₁ t₂ q y : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B β C W f t₀ t₁ t₂ q y)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (B β C W f t₀ t₁ t₂ q y : Term ℒ [] Δ .set) :
    (sentence_m φ B β C W f t₀ t₁ t₂ q y).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.limit_formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeFiniteProgramLimitStep.closed_formula_l K, subset_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  intro η hB hβ hW hBW hC hf hq hφ
  exact (computed_formula_l φ η B β C W f t₀ t₁ t₂ q y hB hβ hW hBW hC hf hq hφ).trans
    (PowerlessRelativeFiniteProgramInstruction.computed_formula_l K φ η B C f t₀ t₁ t₂ q y).symm

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β C W f t₀ t₁ t₂ q y : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B β C W f t₀ t₁ t₂ q y)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ h𝒩 => models_l h𝒩 φ B β C W f t₀ t₁ t₂ q y)

#print axioms good_delta_l
#print axioms computed_delta_l
#print axioms good_iff_l
#print axioms computed_formula_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramInstructionBounded
