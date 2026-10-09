import BMSConstructibleBridge.PowerlessKleeneBrouwerSyntax
import BMSConstructibleBridge.PowerlessRelativeClassFiniteSequences
import BMSConstructibleBridge.SecondOrderOmegaOrdinal

/-! # KB 比较的实际决定位置

纯隶属 ℒ，原 Z₂。决定点前两图相同；该点上左图仍有值，
右图或恰在此终止，或有严格较大值。全部条件均为有界 AST。
内部有限长度只用实际 ω 成员证据，不转换为外部 Nat。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerDecisive

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open PowerlessRelativeClassSequenceSplit (prefix_l)
open PowerlessKleeneBrouwerSyntax (compare_l compare_m compare_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def decisive_m {Γ Δ : SortContext ℒ} (I f g i : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessRelativeClassSequenceSplitDerives.prefix_m i I f g) <|
    membershipLevyBound.boundedExists I <|
      .conj (PowerlessValueBounded.formula_m (up f) (up i) (.bvar .here)) <|
        .disj (PowerlessMapBounded.formula_m (up g) (up i) (up I)) <|
          membershipLevyBound.boundedExists (up I) <|
            .conj (PowerlessValueBounded.formula_m (up (up g)) (up (up i)) (.bvar .here))
              (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (.bvar .here))

theorem decisive_delta_l {Γ Δ : SortContext ℒ} (I f g i : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (decisive_m I f g i) :=
  .conj (PowerlessRelativeClassSequenceSplitDerives.prefix_delta_l _ _ _ _) <|
    .bounded_exists _ (.conj (PowerlessValueBounded.delta_l _ _ _) <|
      .disj (PowerlessMapBounded.delta_l _ _ _) <|
        .bounded_exists _ (.conj (PowerlessValueBounded.delta_l _ _ _) (.rel _ _)))

def decisive_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (I f g i : carrier_l 𝒩) : Prop :=
  prefix_l i I f g ∧ ∃ a, member_l 𝒩 a I ∧ value_l f i a ∧
    (map_l g i I ∨ ∃ b, member_l 𝒩 b I ∧ value_l g i b ∧ member_l 𝒩 a b)

theorem decisive_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (I f g i : Term ℒ Γ Δ .set) :
    (decisive_m I f g i).satisfies η ↔
      decisive_l (I.eval η) (f.eval η) (g.eval η) (i.eval η) := by
  simp only [decisive_m, decisive_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessRelativeClassSequenceSplitDerives.prefix_formula_l,
    PowerlessValueBounded.formula_l, PowerlessMapBounded.formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem domain_unique_l {f n m I : Raw} (hf : map_l (ℳ := 𝒱) f n I)
    (hg : map_l (ℳ := 𝒱) f m I) : n = m := by
  apply SecondOrderQuotient.ext_l hℳ n m
  intro i
  constructor
  · intro hi
    obtain ⟨a, ha, _⟩ := hf.2 i hi
    exact (SecondOrderFunctionProperties.value_mem_l hℳ hg ha.2).1
  · intro hi
    obtain ⟨a, ha, _⟩ := hg.2 i hi
    exact (SecondOrderFunctionProperties.value_mem_l hℳ hf ha.2).1

theorem of_compare_l {ω I f g : Raw} (hω : SecondOrderOmega.omega_l hℳ ω)
    (hCompare : compare_l (𝒩 := 𝒱) ω I f g) :
    ∃ i, SecondOrderQuotient.mem_l hℳ i ω ∧ decisive_l (𝒩 := 𝒱) I f g i := by
  obtain ⟨n, m, hn, hm, hf, hg, hCompare⟩ := hCompare
  have hOrd := SecondOrderOmegaOrdinal.ordinal_l hℳ hω
  rcases hCompare with ⟨hmn, hPrefix⟩ | ⟨i, a, b, hin, _him, ha, hb, hfa, hgb, hab, hPrefix⟩
  · obtain ⟨a, ha, _⟩ := hf.2 m hmn
    exact ⟨m, hm, hPrefix, a, ha.1, ha.2, Or.inl hg⟩
  · exact ⟨i, hOrd.transitive n hn i hin, hPrefix, a, ha, hfa, Or.inr ⟨b, hb, hgb, hab⟩⟩

theorem to_compare_l {ω I f g n m i : Raw}
    (hn : SecondOrderQuotient.mem_l hℳ n ω) (hm : SecondOrderQuotient.mem_l hℳ m ω)
    (hf : map_l (ℳ := 𝒱) f n I) (hg : map_l (ℳ := 𝒱) g m I)
    (hEvent : decisive_l (𝒩 := 𝒱) I f g i) : compare_l (𝒩 := 𝒱) ω I f g := by
  obtain ⟨hPrefix, a, ha, hfa, hRight⟩ := hEvent
  have hin := (SecondOrderFunctionProperties.value_mem_l hℳ hf hfa).1
  refine ⟨n, m, hn, hm, hf, hg, ?_⟩
  rcases hRight with hStop | ⟨b, hb, hgb, hab⟩
  · have hEq := domain_unique_l hStop hg
    subst i
    exact Or.inl ⟨hin, hPrefix⟩
  · exact Or.inr ⟨i, a, b, hin, (SecondOrderFunctionProperties.value_mem_l hℳ hg hgb).1,
      ha, hb, hfa, hgb, hab, hPrefix⟩

theorem compare_iff_l {ω I f g : Raw} (hω : SecondOrderOmega.omega_l hℳ ω)
    (hf : PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒱) ω I f)
    (hg : PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒱) ω I g) :
    compare_l (𝒩 := 𝒱) ω I f g ↔
      ∃ i, SecondOrderQuotient.mem_l hℳ i ω ∧ decisive_l (𝒩 := 𝒱) I f g i := by
  constructor
  · exact of_compare_l hω
  · rintro ⟨i, _hi, hEvent⟩
    obtain ⟨n, hn, hF⟩ := hf
    obtain ⟨m, hm, hG⟩ := hg
    exact to_compare_l hn hm hF hG hEvent

def schema_m {Δ : SortContext ℒ} (ω I f g : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .imp (PowerlessRelativeClassFiniteSequences.sequence_m ω I f) <|
      .imp (PowerlessRelativeClassFiniteSequences.sequence_m ω I g) <|
        .iff (compare_m ω I f g) (membershipLevyBound.boundedExists ω
          (decisive_m (up I) (up f) (up g) (.bvar .here)))

def sentence_m {Δ : SortContext ℒ} (ω I f g : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m ω I f g)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (ω I f g : Term ℒ [] Δ .set) : (sentence_m ω I f g).TrueIn 𝒱 := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeClassFiniteSequences.sequence_formula_l, compare_formula_l,
    Formula.LevyBound.boundedExists, Formula.LevyBound.membership, membershipLevyBound,
    decisive_formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  exact fun hω hf hg => compare_iff_l (hℳ := hℳ) hω hf hg

theorem derives_m {Δ : SortContext ℒ} (ω I f g : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m ω I f g)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ ω I f g)

#print axioms decisive_formula_l
#print axioms of_compare_l
#print axioms to_compare_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerDecisive
