import BMSConstructibleBridge.PowerlessKleeneBrouwerDecisive

/-! # KB 决定位置的内部传递性

纯隶属 ℒ，原 Z₂。两次比较的决定点按内部 ω 比较：
较早点保留；同一点时右图终止或两次数值比较传递。
没有外部长度归纳、Type 选择或预设路径树良序性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerTransitivity

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassSequenceSplit (prefix_l)
open PowerlessKleeneBrouwerSyntax (compare_l compare_m compare_formula_l)
open PowerlessKleeneBrouwerDecisive (decisive_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private theorem restrict_prefix_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {i j I f g : carrier_l 𝒩}
    (hSub : ∀ k, member_l 𝒩 k i → member_l 𝒩 k j)
    (hPrefix : prefix_l j I f g) : prefix_l i I f g :=
  fun k hk a ha => hPrefix k (hSub k hk) a ha

private theorem compose_prefix_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {i I f g h : carrier_l 𝒩}
    (hFG : prefix_l i I f g) (hGH : prefix_l i I g h) : prefix_l i I f h :=
  fun k hk a ha => (hGH k hk a ha).trans (hFG k hk a ha)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

private theorem not_self_l (x : Raw) : ¬mem_l hℳ x x := by
  obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
  exact SecondOrderFoundation.irrefl_l hℳ X

theorem decisive_transitive_l {ω I f g h m i j : Raw}
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hSub : ∀ a, mem_l hℳ a I → mem_l hℳ a ω)
    (hG : map_l (ℳ := 𝒱) g m I)
    (hi : mem_l hℳ i ω) (hj : mem_l hℳ j ω)
    (hFG : decisive_l (𝒩 := 𝒱) I f g i)
    (hGH : decisive_l (𝒩 := 𝒱) I g h j) :
    ∃ k, mem_l hℳ k ω ∧ decisive_l (𝒩 := 𝒱) I f h k := by
  have hOrd := SecondOrderOmegaOrdinal.ordinal_l hℳ hω
  have hiOrd : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) i :=
    SetTheory.Structure.IsOrdinal.mem hOrd hi
  have hjOrd : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) j :=
    SetTheory.Structure.IsOrdinal.mem hOrd hj
  obtain ⟨hPrefixFG, a, ha, hfa, hRightG⟩ := hFG
  obtain ⟨hPrefixGH, c, hc, hgc, hRightH⟩ := hGH
  rcases hOrd.wellOrder.linear.compare i hi j hj with hSame | hij | hji
  · have hEq : i = j := SecondOrderQuotient.ext_l hℳ i j hSame
    subst j
    rcases hRightG with hStopG | ⟨b, hb, hgb, hab⟩
    · exact (not_self_l i (SecondOrderFunctionProperties.value_mem_l hℳ hStopG hgc).1).elim
    · have hEqBC := SecondOrderFunctionProperties.value_unique_l hℳ hG hgb hgc
      subst c
      refine ⟨i, hi, compose_prefix_l hPrefixFG hPrefixGH, a, ha, hfa, ?_⟩
      rcases hRightH with hStopH | ⟨d, hd, hhd, hbd⟩
      · exact Or.inl hStopH
      · have hdOrd : SetTheory.Structure.IsOrdinal
            (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) d :=
          SetTheory.Structure.IsOrdinal.mem hOrd (hSub d hd)
        exact Or.inr ⟨d, hd, hhd, hdOrd.transitive b hbd a hab⟩
  · have hPrefix := compose_prefix_l hPrefixFG
      (restrict_prefix_l (𝒩 := 𝒱) (i := i) (j := j)
        (fun k hk => hjOrd.transitive i hij k hk) hPrefixGH)
    rcases hRightG with hStopG | ⟨b, hb, hgb, hab⟩
    · have hji := (SecondOrderFunctionProperties.value_mem_l hℳ hStopG hgc).1
      exact (not_self_l j (hjOrd.transitive i hij j hji)).elim
    · exact ⟨i, hi, hPrefix, a, ha, hfa, Or.inr
        ⟨b, hb, (hPrefixGH i hij b hb).mpr hgb, hab⟩⟩
  · have hPrefix := compose_prefix_l
      (restrict_prefix_l (𝒩 := 𝒱) (i := j) (j := i)
        (fun k hk => hiOrd.transitive j hji k hk) hPrefixFG) hPrefixGH
    exact ⟨j, hj, hPrefix, c, hc, (hPrefixFG j hji c hc).mp hgc, hRightH⟩

theorem transitive_l {ω I f g h : Raw}
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hSub : ∀ a, mem_l hℳ a I → mem_l hℳ a ω)
    (hf : PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒱) ω I f)
    (hg : PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒱) ω I g)
    (hh : PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒱) ω I h)
    (hFG : compare_l (𝒩 := 𝒱) ω I f g) (hGH : compare_l (𝒩 := 𝒱) ω I g h) :
    compare_l (𝒩 := 𝒱) ω I f h := by
  obtain ⟨i, hi, hEventFG⟩ := PowerlessKleeneBrouwerDecisive.of_compare_l hω hFG
  obtain ⟨j, hj, hEventGH⟩ := PowerlessKleeneBrouwerDecisive.of_compare_l hω hGH
  obtain ⟨_m, _hm, hG⟩ := hg
  exact (PowerlessKleeneBrouwerDecisive.compare_iff_l hω hf hh).mpr
    (decisive_transitive_l hω hSub hG hi hj hEventFG hEventGH)

def schema_m {Δ : SortContext ℒ} (ω I f g h : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .imp (ThirdOrderTheory.subset_m I ω) <|
      .imp (PowerlessRelativeClassFiniteSequences.sequence_m ω I f) <|
        .imp (PowerlessRelativeClassFiniteSequences.sequence_m ω I g) <|
          .imp (PowerlessRelativeClassFiniteSequences.sequence_m ω I h) <|
            .imp (compare_m ω I f g) <| .imp (compare_m ω I g h) (compare_m ω I f h)

def sentence_m {Δ : SortContext ℒ} (ω I f g h : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m ω I f g h)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (ω I f g h : Term ℒ [] Δ .set) : (sentence_m ω I f g h).TrueIn 𝒱 := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, SecondOrderOmegaSyntax.omega_l,
    ThirdOrderSemantics.subset_formula_l, ThirdOrderSemantics.subset_l, ThirdOrderSemantics.member_l,
    PowerlessRelativeClassFiniteSequences.sequence_formula_l, compare_formula_l]
  exact fun hω hSub hf hg hh hFG hGH => transitive_l (hℳ := hℳ) hω hSub hf hg hh hFG hGH

theorem derives_m {Δ : SortContext ℒ} (ω I f g h : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m ω I f g h)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ ω I f g h)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerTransitivity
