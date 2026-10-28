import BMSConstructibleBridge.PowerlessKleeneBrouwerFirstDifference
import BMSConstructibleBridge.PowerlessKleeneBrouwerTransitivity
import BMSConstructibleBridge.SecondOrderPairObjects

/-! # KB 顺序的内部比较性

纯隶属 ℒ，原 Z₂。取两个内部长度中的较小者；共同前缀有差异时
按已构造的最小差异点比较，否则比较真扩展或由函数外延性识别两图。
这里完成线序条款，不把全部有限序列误称为良序。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerComparison

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassSequenceSplit (prefix_l)
open PowerlessKleeneBrouwerSyntax (compare_l compare_m compare_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem prefix_ext_l {I f g n : Raw} (hf : map_l (ℳ := 𝒱) f n I)
    (hg : map_l (ℳ := 𝒱) g n I) (hPrefix : prefix_l (ℳ₀ := 𝒱) n I f g) : f = g := by
  apply SecondOrderQuotient.ext_l hℳ f g
  intro p
  constructor
  · intro hp
    obtain ⟨i, a, hi, ha, hPair⟩ := hf.1 p hp
    obtain ⟨q, hq, hPair'⟩ := (hPrefix i hi a ha).mpr ⟨p, hp, hPair⟩
    exact (SecondOrderPairObjects.ordered_unique_l hℳ hPair' hPair) ▸ hq
  · intro hp
    obtain ⟨i, a, hi, ha, hPair⟩ := hg.1 p hp
    obtain ⟨q, hq, hPair'⟩ := (hPrefix i hi a ha).mp ⟨p, hp, hPair⟩
    exact (SecondOrderPairObjects.ordered_unique_l hℳ hPair' hPair) ▸ hq

private theorem of_difference_l {ω I f g n m i : Raw}
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hSub : ∀ a, mem_l hℳ a I → mem_l hℳ a ω)
    (hn : mem_l hℳ n ω) (hm : mem_l hℳ m ω)
    (hf : map_l (ℳ := 𝒱) f n I) (hg : map_l (ℳ := 𝒱) g m I)
    (hin : mem_l hℳ i n) (him : mem_l hℳ i m)
    (hPrefix : prefix_l (ℳ₀ := 𝒱) i I f g)
    (hDiff : PowerlessKleeneBrouwerFirstDifference.mismatch_l (𝒩 := 𝒱) I f g i) :
    compare_l (𝒩 := 𝒱) ω I f g ∨ compare_l (𝒩 := 𝒱) ω I g f := by
  obtain ⟨a, ha, b, hb, hfa, hgb, hNe⟩ := hDiff
  have hOrd := SecondOrderOmegaOrdinal.ordinal_l hℳ hω
  rcases hOrd.wellOrder.linear.compare a (hSub a ha) b (hSub b hb) with hEq | hab | hba
  · exact (hNe (SecondOrderQuotient.ext_l hℳ a b hEq)).elim
  · exact Or.inl ⟨n, m, hn, hm, hf, hg, Or.inr ⟨i, a, b, hin, him, ha, hb, hfa, hgb, hab, hPrefix⟩⟩
  · exact Or.inr ⟨m, n, hm, hn, hg, hf, Or.inr ⟨i, b, a, him, hin, hb, ha, hgb, hfa, hba,
      fun j hj c hc => (hPrefix j hj c hc).symm⟩⟩

theorem comparison_l {ω I f g : Raw} (hω : SecondOrderOmega.omega_l hℳ ω)
    (hSub : ∀ a, mem_l hℳ a I → mem_l hℳ a ω)
    (hF : PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒱) ω I f)
    (hG : PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒱) ω I g) :
    compare_l (𝒩 := 𝒱) ω I f g ∨ f = g ∨ compare_l (𝒩 := 𝒱) ω I g f := by
  obtain ⟨n, hn, hf⟩ := hF
  obtain ⟨m, hm, hg⟩ := hG
  have hOrd := SecondOrderOmegaOrdinal.ordinal_l hℳ hω
  rcases hOrd.wellOrder.linear.compare n hn m hm with hEq | hnm | hmn
  · have hSame : n = m := SecondOrderQuotient.ext_l hℳ n m hEq
    subst m
    rcases PowerlessKleeneBrouwerFirstDifference.least_l hω hn
        (fun _ h => h) (fun _ h => h) hf hg with hPrefix | ⟨i, hi, hPrefix, hDiff⟩
    · exact Or.inr (Or.inl (prefix_ext_l hf hg hPrefix))
    · exact (of_difference_l hω hSub hn hn hf hg hi hi hPrefix hDiff).elim
        Or.inl (fun h => Or.inr (Or.inr h))
  · have hmOrd : SetTheory.Structure.IsOrdinal
        (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) m :=
      SetTheory.Structure.IsOrdinal.mem hOrd hm
    have hInclude : ∀ j, mem_l hℳ j n → mem_l hℳ j m :=
      fun j hj => hmOrd.transitive n hnm j hj
    rcases PowerlessKleeneBrouwerFirstDifference.least_l hω hn
        (fun _ h => h) hInclude hf hg with hPrefix | ⟨i, hi, hPrefix, hDiff⟩
    · exact Or.inr (Or.inr (PowerlessKleeneBrouwerSyntax.extension_l hm hn hg hf hnm
        (fun j hj a ha => (hPrefix j hj a ha).symm)))
    · exact (of_difference_l hω hSub hn hm hf hg hi (hInclude i hi) hPrefix hDiff).elim
        Or.inl (fun h => Or.inr (Or.inr h))
  · have hnOrd : SetTheory.Structure.IsOrdinal
        (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) n :=
      SetTheory.Structure.IsOrdinal.mem hOrd hn
    have hInclude : ∀ j, mem_l hℳ j m → mem_l hℳ j n :=
      fun j hj => hnOrd.transitive m hmn j hj
    rcases PowerlessKleeneBrouwerFirstDifference.least_l hω hm
        hInclude (fun _ h => h) hf hg with hPrefix | ⟨i, hi, hPrefix, hDiff⟩
    · exact Or.inl (PowerlessKleeneBrouwerSyntax.extension_l hn hm hf hg hmn hPrefix)
    · exact (of_difference_l hω hSub hn hm hf hg (hInclude i hi) hi hPrefix hDiff).elim
        Or.inl (fun h => Or.inr (Or.inr h))

theorem asymmetric_l {ω I f g : Raw} (hω : SecondOrderOmega.omega_l hℳ ω)
    (hSub : ∀ a, mem_l hℳ a I → mem_l hℳ a ω)
    (hf : PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒱) ω I f)
    (hg : PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒱) ω I g)
    (hFG : compare_l (𝒩 := 𝒱) ω I f g) : ¬compare_l (𝒩 := 𝒱) ω I g f :=
  fun hGF => PowerlessKleeneBrouwerSyntax.irreflexive_l
    (PowerlessKleeneBrouwerTransitivity.transitive_l hω hSub hf hg hf hFG hGF)

def schema_m {Δ : SortContext ℒ} (ω I f g : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <| .imp (ThirdOrderTheory.subset_m I ω) <|
    .imp (PowerlessRelativeClassFiniteSequences.sequence_m ω I f) <|
      .imp (PowerlessRelativeClassFiniteSequences.sequence_m ω I g) <|
        .disj (compare_m ω I f g) (.disj (.equal f g) (compare_m ω I g f))

def sentence_m {Δ : SortContext ℒ} (ω I f g : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m ω I f g)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (ω I f g : Term ℒ [] Δ .set) : (sentence_m ω I f g).TrueIn 𝒱 := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, SecondOrderOmegaSyntax.omega_l,
    ThirdOrderSemantics.subset_formula_l, subset_l,
    PowerlessRelativeClassFiniteSequences.sequence_formula_l, compare_formula_l]
  exact fun hω hSub hf hg => comparison_l (hℳ := hℳ) hω hSub hf hg

theorem derives_m {Δ : SortContext ℒ} (ω I f g : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m ω I f g)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ ω I f g)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerComparison
