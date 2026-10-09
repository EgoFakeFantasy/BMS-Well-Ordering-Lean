import BMSConstructibleBridge.PowerlessRelativeFiniteProgramOutput
import BMSConstructibleBridge.PowerlessRelativeClassProduct

/-! # 三类程序指令的实际 Class 字母表

常量参数来自实际母集 C，父坐标来自实际 ω。三类指令分别是
{t₀}×C、{t₁}×ω、{t₂}×(ω×ω)，字母表是它们的精确二元并。
使用已有实际 Class 积与并集，不消费 Collection 或任意像集原则。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramAlphabet

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderObjectSyntax (ordered_m member_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)

def instruction_m {Γ Δ : SortContext ℒ}
    (C ω t₀ t₁ t₂ q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (.existsE .set <| .conj (member_m (.bvar .here) (up C))
      (ordered_m (up t₀) (.bvar .here) (up q))) <|
    .disj (.existsE .set <| .conj (member_m (.bvar .here) (up ω))
      (ordered_m (up t₁) (.bvar .here) (up q))) <|
      .existsE .set <| .existsE .set <| .existsE .set <|
        .conj (member_m (.bvar (.there (.there .here))) (up₃ ω)) <|
          .conj (member_m (.bvar (.there .here)) (up₃ ω)) <|
            .conj (ordered_m (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))
              (ordered_m (up₃ t₂) (.bvar .here) (up₃ q))

def alphabet_m {Γ Δ : SortContext ℒ}
    (C ω t₀ t₁ t₂ Q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .iff (member_m (.bvar .here) (up Q))
    (instruction_m (up C) (up ω) (up t₀) (up t₁) (up t₂) (.bvar .here))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def instruction_l (C ω t₀ t₁ t₂ q : type_l hℳ) : Prop :=
  (∃ a, mem_l hℳ a C ∧ ordered_l (ℳ := 𝒱) t₀ a q) ∨
    (∃ k, mem_l hℳ k ω ∧ ordered_l (ℳ := 𝒱) t₁ k q) ∨
      ∃ k l p, mem_l hℳ k ω ∧ mem_l hℳ l ω ∧ ordered_l (ℳ := 𝒱) k l p ∧
        ordered_l (ℳ := 𝒱) t₂ p q

theorem instruction_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (C ω t₀ t₁ t₂ q : Term ℒ Γ Δ .set) :
    (instruction_m C ω t₀ t₁ t₂ q).satisfies η ↔ instruction_l
      (C.eval η) (ω.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (q.eval η) := by
  simp only [instruction_m, instruction_l, Formula.satisfies, ordered_formula_l, member_m,
    Arguments.eval, up₃, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem alphabet_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (C ω t₀ t₁ t₂ Q : Term ℒ Γ Δ .set) :
    (alphabet_m C ω t₀ t₁ t₂ Q).satisfies η ↔ ∀ q, mem_l hℳ q (Q.eval η) ↔
      instruction_l (C.eval η) (ω.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) q := by
  simp only [alphabet_m, Formula.satisfies, instruction_formula_l, member_m, Arguments.eval,
    up, Term.eval_weakenBound, Term.eval]
  rfl

private theorem product_l {B X Y : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ z, mem_l hℳ z x → mem_l hℳ z B)
    (hX : PowerlessRelativeClassCorrespondence.member_l hℳ B X)
    (hY : PowerlessRelativeClassCorrespondence.member_l hℳ B Y) :
    ∃ P, PowerlessRelativeClassCorrespondence.member_l hℳ B P ∧
      ∀ p, mem_l hℳ p P ↔ ∃ x y, mem_l hℳ x X ∧ mem_l hℳ y Y ∧ ordered_l (ℳ := 𝒱) x y p := by
  obtain ⟨P, hP⟩ := SecondOrderDefinableRelationImage.exists_l hℳ (Δ := []) .truth Env.empty X Y
  have hRead : ∀ p, mem_l hℳ p P ↔
      ∃ x y, mem_l hℳ x X ∧ mem_l hℳ y Y ∧ ordered_l (ℳ := 𝒱) x y p := by
    simpa only [Formula.satisfies, true_and, SecondOrderPairObjects.ordered_l,
      SecondOrderPairObjects.pair_l, ThirdOrderSemantics.ordered_l,
      ThirdOrderSemantics.pair_l, ThirdOrderSemantics.member_l,
      SecondOrderQuotient.structure_l] using hP
  exact ⟨P, PowerlessRelativeClassProduct.member_l hBase hX hY hRead, hRead⟩

private theorem singleton_l {B t : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ z, mem_l hℳ z x → mem_l hℳ z B)
    (ht : PowerlessRelativeClassCorrespondence.member_l hℳ B t) :
    ∃ T, PowerlessRelativeClassCorrespondence.member_l hℳ B T ∧ ∀ x, mem_l hℳ x T ↔ x = t := by
  obtain ⟨T, hT⟩ := SecondOrderPairObjects.pair_exists_l hℳ t t
  exact ⟨T, PowerlessRelativeClassPair.pair_l hℳ hBase ht ht hT,
    fun x => by simpa only [or_self] using hT x⟩

private theorem union_l {B U V : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ z, mem_l hℳ z x → mem_l hℳ z B)
    (hU : PowerlessRelativeClassCorrespondence.member_l hℳ B U)
    (hV : PowerlessRelativeClassCorrespondence.member_l hℳ B V) :
    ∃ W, PowerlessRelativeClassCorrespondence.member_l hℳ B W ∧
      ∀ x, mem_l hℳ x W ↔ mem_l hℳ x U ∨ mem_l hℳ x V := by
  obtain ⟨P, hP⟩ := SecondOrderPairObjects.pair_exists_l hℳ U V
  have hUnion := SecondOrderUnion.models_l hℳ
  change ∀ P : type_l hℳ, ∃ W, ∀ x, mem_l hℳ x W ↔
    ∃ Y, mem_l hℳ Y P ∧ mem_l hℳ x Y at hUnion
  obtain ⟨W, hW⟩ := hUnion P
  refine ⟨W, PowerlessRelativeClassBasicClosure.union_l hℳ hBase
    (PowerlessRelativeClassPair.pair_l hℳ hBase hU hV hP) hW, ?_⟩
  intro x
  apply (hW x).trans
  constructor
  · rintro ⟨Y, hY, hx⟩
    rcases (hP Y).mp hY with rfl | rfl
    · exact Or.inl hx
    · exact Or.inr hx
  · rintro (hx | hx)
    · exact ⟨U, (hP U).mpr (Or.inl rfl), hx⟩
    · exact ⟨V, (hP V).mpr (Or.inr rfl), hx⟩

theorem exists_l {B C ω t₀ t₁ t₂ : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ z, mem_l hℳ z x → mem_l hℳ z B)
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ B C)
    (hω : PowerlessRelativeClassCorrespondence.member_l hℳ B ω)
    (h₀ : PowerlessRelativeClassCorrespondence.member_l hℳ B t₀)
    (h₁ : PowerlessRelativeClassCorrespondence.member_l hℳ B t₁)
    (h₂ : PowerlessRelativeClassCorrespondence.member_l hℳ B t₂) :
    ∃ Q, PowerlessRelativeClassCorrespondence.member_l hℳ B Q ∧
      ∀ q, mem_l hℳ q Q ↔ instruction_l C ω t₀ t₁ t₂ q := by
  obtain ⟨T₀, hT₀, hRead₀⟩ := singleton_l hBase h₀
  obtain ⟨T₁, hT₁, hRead₁⟩ := singleton_l hBase h₁
  obtain ⟨T₂, hT₂, hRead₂⟩ := singleton_l hBase h₂
  obtain ⟨P, hP, hPairs⟩ := product_l hBase hω hω
  obtain ⟨Q₀, hQ₀, hConst⟩ := product_l hBase hT₀ hC
  obtain ⟨Q₁, hQ₁, hCall⟩ := product_l hBase hT₁ hω
  obtain ⟨Q₂, hQ₂, hPair⟩ := product_l hBase hT₂ hP
  obtain ⟨U, hU, hReadU⟩ := union_l hBase hQ₁ hQ₂
  obtain ⟨Q, hQ, hReadQ⟩ := union_l hBase hQ₀ hU
  refine ⟨Q, hQ, ?_⟩
  intro q
  rw [hReadQ, hReadU, hConst, hCall, hPair]
  constructor
  · rintro (⟨t, a, ht, ha, hq⟩ | ⟨t, k, ht, hk, hq⟩ | ⟨t, p, ht, hp, hq⟩)
    · exact Or.inl ⟨a, ha, (hRead₀ t).mp ht ▸ hq⟩
    · exact Or.inr (Or.inl ⟨k, hk, (hRead₁ t).mp ht ▸ hq⟩)
    · obtain ⟨k, l, hk, hl, hkl⟩ := (hPairs p).mp hp
      exact Or.inr (Or.inr ⟨k, l, p, hk, hl, hkl, (hRead₂ t).mp ht ▸ hq⟩)
  · rintro (⟨a, ha, hq⟩ | ⟨k, hk, hq⟩ | ⟨k, l, p, hk, hl, hkl, hq⟩)
    · exact Or.inl ⟨t₀, a, (hRead₀ t₀).mpr rfl, ha, hq⟩
    · exact Or.inr (Or.inl ⟨t₁, k, (hRead₁ t₁).mpr rfl, hk, hq⟩)
    · exact Or.inr (Or.inr ⟨t₂, p, (hRead₂ t₂).mpr rfl, (hPairs p).mpr ⟨k, l, hk, hl, hkl⟩, hq⟩)

def schema_m {Δ : SortContext ℒ} (B C ω t₀ t₁ t₂ : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B C) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B ω) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B t₀) <|
          .imp (PowerlessRelativeHierarchySyntax.class_m B t₁) <|
            .imp (PowerlessRelativeHierarchySyntax.class_m B t₂) <|
              .existsE .set <| .conj (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here))
                (alphabet_m (up C) (up ω) (up t₀) (up t₁) (up t₂) (.bvar .here))

def sentence_m {Δ : SortContext ℒ} (B C ω t₀ t₁ t₂ : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B C ω t₀ t₁ t₂)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B C ω t₀ t₁ t₂ : Term ℒ [] Δ .set) :
    (sentence_m B C ω t₀ t₁ t₂).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.class_formula_l K, alphabet_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  intro η hBase hC hω h₀ h₁ h₂
  exact exists_l hBase hC hω h₀ h₁ h₂

theorem derives_m {Δ : SortContext ℒ} (B C ω t₀ t₁ t₂ : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m B C ω t₀ t₁ t₂)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 B C ω t₀ t₁ t₂)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramAlphabet
