import BMSConstructibleBridge.PowerlessKleeneBrouwerPathMinimum
import BMSConstructibleBridge.PowerlessKleeneBrouwerPathClass
import BMSConstructibleBridge.PowerlessRelativeClassEnumerationWellOrder

/-! # 实际类内路径比较图的环境良序

纯隶属 ℒ，原 Z₂。真实 Class 路径集和 KB 比较图由有界分离构造，
原 H 输出内部归纳给出全部 raw 子集最小元，再装配非自返、传递和三歧性。
此处仍以实际原坍缩 H 为前提；读数不单独保证关系图没有非有序对垃圾。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerPathWellOrder

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessKleeneBrouwerPath (path_l)
open PowerlessKleeneBrouwerSyntax (compare_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem of_reading_l {ω I A z r T H S J : Raw}
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hSub : ∀ b, mem_l hℳ b I → mem_l hℳ b ω)
    (hZero : PowerlessNatural.zero_l (ℳ := 𝒱) z) (hz : mem_l hℳ z ω) (hr : mem_l hℳ r I)
    (hH : SecondOrderCollapseFunction.spec_l hℳ A I T H)
    (hS : PowerlessKleeneBrouwerPathClass.reading_l ω I A z r S)
    (hJ : PowerlessKleeneBrouwerGraph.reading_l ω I S J) :
    wellOrder_l (ℳ := 𝒱) S J := by
  have hSeq (f : Raw) (hf : mem_l hℳ f S) :
      PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒱) ω I f := by
    obtain ⟨n, hn, hMap, _, _⟩ := (hS f).mp hf
    exact ⟨n, hn, hMap⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f _hf hff
    exact PowerlessKleeneBrouwerSyntax.irreflexive_l ((hJ f f).mp hff).2.2
  · intro f g k hfgk hfg hgk
    exact (hJ f k).mpr ⟨hfgk.1, hfgk.2.2,
      PowerlessKleeneBrouwerTransitivity.transitive_l hω hSub
        (hSeq f hfgk.1) (hSeq g hfgk.2.1) (hSeq k hfgk.2.2)
        ((hJ f g).mp hfg).2.2 ((hJ g k).mp hgk).2.2⟩
  · intro f g hfg
    rcases PowerlessKleeneBrouwerComparison.comparison_l hω hSub
        (hSeq f hfg.1) (hSeq g hfg.2) with hlt | hEq | hgt
    · exact Or.inl ((hJ f g).mpr ⟨hfg.1, hfg.2, hlt⟩)
    · exact Or.inr (Or.inl hEq)
    · exact Or.inr (Or.inr ((hJ g f).mpr ⟨hfg.2, hfg.1, hgt⟩))
  · intro U hU
    obtain ⟨f, hf, hMin⟩ := PowerlessKleeneBrouwerPathMinimum.minimum_l hω hSub hZero hz hr hH
      (fun g hg => (hS g).mp (hU.1 g hg)) hU.2
    exact ⟨f, hf, fun g hg hgf => hMin g hg ((hJ g f).mp hgf).2.2⟩

theorem exists_l {B ω I A z r T H : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hI : PowerlessRelativeClassCorrespondence.member_l hℳ B I)
    (hA : PowerlessRelativeClassCorrespondence.member_l hℳ B A)
    (hSub : ∀ b, mem_l hℳ b I → mem_l hℳ b ω)
    (hZero : PowerlessNatural.zero_l (ℳ := 𝒱) z) (hz : mem_l hℳ z ω) (hr : mem_l hℳ r I)
    (hH : SecondOrderCollapseFunction.spec_l hℳ A I T H) :
    ∃ S J, PowerlessRelativeClassCorrespondence.member_l hℳ B S ∧
      PowerlessRelativeClassCorrespondence.member_l hℳ B J ∧
        PowerlessKleeneBrouwerPathClass.reading_l ω I A z r S ∧
          PowerlessKleeneBrouwerGraph.reading_l ω I S J ∧ wellOrder_l (ℳ := 𝒱) S J := by
  obtain ⟨S, J, hSClass, hJClass, hS, hJ⟩ :=
    PowerlessKleeneBrouwerPathClass.graph_exists_l hBase hω hI hA hz hr
  exact ⟨S, J, hSClass, hJClass, hS, hJ, of_reading_l hω hSub hZero hz hr hH hS hJ⟩

def result_m {Γ Δ : SortContext ℒ} (B ω I A z r : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <|
    let w (t : Term ℒ Γ Δ .set) := up (up t)
    let S : Term ℒ (.set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let J : Term ℒ (.set :: .set :: Γ) Δ .set := .bvar .here
    .conj (PowerlessRelativeHierarchySyntax.class_m (w B) S) <|
      .conj (PowerlessRelativeHierarchySyntax.class_m (w B) J) <|
        .conj (PowerlessKleeneBrouwerPathClass.reading_m (w ω) (w I) (w A) (w z) (w r) S) <|
          .conj (PowerlessKleeneBrouwerGraph.reading_m (w ω) (w I) S J)
            (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m S J)

def schema_m {Δ : SortContext ℒ} (B ω I A z r T H : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <| .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B I) <| .imp (PowerlessRelativeHierarchySyntax.class_m B A) <|
      .imp (ThirdOrderTheory.subset_m I ω) <|
        .imp (.forallE .set (.neg (SecondOrderObjectSyntax.member_m (.bvar .here) (up z)))) <|
          .imp (SecondOrderObjectSyntax.member_m z ω) <| .imp (SecondOrderObjectSyntax.member_m r I) <|
            .imp (SecondOrderCollapseSyntax.formula_m A I T H) (result_m B ω I A z r)

def sentence_m {Δ : SortContext ℒ} (B ω I A z r T H : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B ω I A z r T H)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B ω I A z r T H : Term ℒ [] Δ .set) : (sentence_m B ω I A z r T H).TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, result_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeHierarchySemantics.class_formula_l K,
    ThirdOrderSemantics.subset_formula_l, subset_l, SecondOrderObjectSyntax.member_m,
    SecondOrderCollapseSyntax.formula_l, PowerlessKleeneBrouwerPathClass.reading_formula_l,
    PowerlessKleeneBrouwerGraph.reading_formula_l,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  exact exists_l (hℳ := hℳ)

theorem derives_m {Δ : SortContext ℒ} (B ω I A z r T H : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m B ω I A z r T H)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B ω I A z r T H)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerPathWellOrder
