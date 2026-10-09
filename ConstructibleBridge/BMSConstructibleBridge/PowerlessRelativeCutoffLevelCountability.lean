import BMSConstructibleBridge.PowerlessRelativeFiniteProgramFourGraphImage
import BMSConstructibleBridge.PowerlessRelativeCofinalHistorySeed
import BMSConstructibleBridge.PowerlessRelativeCofinalHistoryCoverage
import BMSConstructibleBridge.PowerlessRelativeCutoffClassHistory
import BMSConstructibleBridge.PowerlessRelativeClassFunctionRestriction

/-! # 首截断以下实际层的类内可数性

原 Z₂、纯隶属语言。基底有实际 Class 的内部 ω 满射并覆盖 ω 时，
在 γ∈α∈Ω 上构造真实较短历史；真实可数种子和四图程序像给同一个 I。
内部历史归纳覆盖原 γ 层的全部成员，再限制同一 Class 计数图。
终点为原 Z₂ 的对象可数性句，不预供层覆盖、历史或操作闭包。
计数图这里只证明属于 Class，不证明属于 W；完整源公理及 BMS 终局另证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffLevelCountability

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}

local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 限制实际单射图，空子集也不需要缺省成员或新的枚举。 -/
private theorem restriction_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (ω A I : type_l hℳ B) (hCount : PowerlessRelativeOrdinalCutoff.countable_l B ω.val I.val)
    (hSub : ∀ x, mem_l hℳ x A.val → mem_l hℳ x I.val) :
    PowerlessRelativeOrdinalCutoff.countable_l B ω.val A.val := by
  obtain ⟨f, hf, hMap, hInj⟩ := hCount
  let F : type_l hℳ B := ⟨f, hf⟩
  have hF := (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) F I ω).mpr hMap
  obtain ⟨G, hG, hRead⟩ := PowerlessRelativeClassFunctionRestriction.exists_l hF
    (show subset_l (ℳ := structure_l hℳ B hBase) A I from fun x hx => hSub x.val hx)
  refine ⟨G.val, G.property, (PowerlessRelativeClassFunctionAbsolute.map_l G A ω).mp hG, ?_⟩
  intro x z i hxi hzi
  obtain ⟨hx, hi⟩ := PowerlessRelativeClassValueCoordinates.value_l hBase G hxi
  obtain ⟨hz, _hi⟩ := PowerlessRelativeClassValueCoordinates.value_l hBase G hzi
  let x₀ : type_l hℳ B := ⟨x, hx⟩
  let z₀ : type_l hℳ B := ⟨z, hz⟩
  let i₀ : type_l hℳ B := ⟨i, hi⟩
  have hFx := ((hRead x₀ i₀).mp
    ((PowerlessRelativeClassFunctionAbsolute.value_l G x₀ i₀).mpr hxi)).2
  have hFz := ((hRead z₀ i₀).mp
    ((PowerlessRelativeClassFunctionAbsolute.value_l G z₀ i₀).mpr hzi)).2
  exact hInj x z i ((PowerlessRelativeClassFunctionAbsolute.value_l F x₀ i₀).mp hFx)
    ((PowerlessRelativeClassFunctionAbsolute.value_l F z₀ i₀).mp hFz)

theorem countable_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (K : source_coding_l hℳ) {ω Ω W γ A : Raw} (G : type_l hℳ B)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B ω Ω)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W) (hBW : mem_l hℳ B W)
    (hωB : ∀ x, mem_l hℳ x ω → mem_l hℳ x B)
    (hG : map_l (ℳ := 𝒱) G.val ω B)
    (hOnto : ∀ x, mem_l hℳ x B → ∃ i, mem_l hℳ i ω ∧ value_l (ℳ := 𝒱) G.val i x)
    (hγ : mem_l hℳ γ Ω) (hA : PowerlessRelativeHierarchySemantics.level_l hℳ B γ A) :
    PowerlessRelativeOrdinalCutoff.countable_l B ω A := by
  have hLimit := PowerlessRelativeCutoffLimit.limit_l K hBase hω hΩ
  obtain ⟨α, hαΩ, hγα⟩ := hLimit.2 γ hγ
  have hα : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) α := by
    apply SetTheory.Structure.IsOrdinal.mem hΩ.1
    exact hαΩ
  have hωW := PowerlessRelativeOrdinalCoverage.covered_l hℳ K hBase Ω W hW ω
    (PowerlessRelativeCutoffBelow.omega_below_l (hBase := hBase) K hω hΩ)
  have hαW := PowerlessRelativeOrdinalCoverage.covered_l hℳ K hBase Ω W hW α hαΩ
  have hClass := PowerlessRelativeLevelClosure.class_l hℳ hBase hW
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hW
  let O : type_l hℳ B :=
    ⟨ω, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hClass hωW⟩
  let a : type_l hℳ B :=
    ⟨α, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hClass hαW⟩
  obtain ⟨C, E, hE, hEOnto, hSeed⟩ := PowerlessRelativeCofinalHistorySeed.exists_l
    (hBase := hBase) O a G hω hG hOnto (hΩ.2.2 α hαΩ)
  have hCW := PowerlessRelativeCofinalHistorySeed.subset_l hSeed
    (hTrans B hBW) (hTrans α hαW) hBW hαW hωW
  have hBC : ∀ x, mem_l hℳ x B → mem_l hℳ x C.val :=
    fun x hx => (hSeed x).mpr (Or.inl hx)
  have hαC : ∀ x, mem_l hℳ x α → mem_l hℳ x C.val :=
    fun x hx => (hSeed x).mpr (Or.inr (Or.inl hx))
  have hωC : ∀ x, mem_l hℳ x ω → mem_l hℳ x C.val := fun x hx => hBC x (hωB x hx)
  have hBCObject : mem_l hℳ B C.val := (hSeed B).mpr (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨D, _hDMap, hD⟩ := PowerlessRelativeCutoffDefFunction.exists_l K hBase hω hΩ hW
  obtain ⟨H, hHistory⟩ := PowerlessRelativeCutoffClassHistory.class_exists_l hℳ K hBase D hD hα hW
    (fun x hx => hΩ.1.transitive α hαΩ x hx)
  obtain ⟨e, t₁, t₂, t₃, Pair, N, Valid, Translation, S, L, hCode⟩ :=
    PowerlessRelativeCofinalDefCoding.exists_l hBase K hLimit hW
      (PowerlessRelativeCutoffInnerLimits.cofinal_l K hBase hω hΩ) O hωW
      (SecondOrderOmega.unique_l hℳ hω K.omega_spec)
  obtain ⟨P, U, J, F, hP, hU, hJ, hF, hPRead, hURead, hJRead, hFRead⟩ :=
    PowerlessRelativeCofinalProgramGraphs.exists_l hBase K hLimit hW
      H O e t₁ t₂ t₃ Pair N Valid Translation S hCode hωW hHistory
  obtain ⟨I, hCount, hIW, hCI, hPair, hPCall, hUCall, hJCall, hFCall⟩ :=
    PowerlessRelativeFiniteProgramFourGraphImage.exists_l hBase K hLimit hW hBW C E O P U J F
      hω hωW hCW hωC hBCObject hE hEOnto hP hU hJ hF
  have hBasis : PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) I.val := by
    have hOperation (b : Bool) (R : Raw)
        (hRead : ∀ s Z, mem_l hℳ s W →
          PowerlessRelativeFiniteProgramBasicOperator.call_l (𝒩 := 𝒱) b W s Z →
            value_l (ℳ := 𝒱) R s Z)
        (hCall : ∀ s Z, mem_l hℳ s I.val → value_l (ℳ := 𝒱) R s Z → mem_l hℳ Z I.val) :
        ∀ X Y Z, mem_l hℳ X I.val → mem_l hℳ Y I.val →
          PowerlessRelativeFiniteProgramBasicOperator.operation_l (𝒩 := 𝒱) b X Y Z →
            mem_l hℳ Z I.val := by
      intro X Y Z hX hY hZ
      obtain ⟨s, hsI, hs⟩ := hPair X Y hX hY
      exact hCall s Z hsI (hRead s Z (hIW s hsI) ⟨X, Y, hIW X hX, hIW Y hY, hs, hZ⟩)
    exact ⟨hOperation true P.val hPRead hPCall, hOperation false U.val hURead hUCall⟩
  have hGetter : ∀ x Y : Raw, mem_l hℳ x I.val →
      SecondOrderFunctionObjects.value_l hℳ H.val x Y → mem_l hℳ Y I.val :=
    fun x Y hx hY => hJCall x Y hx (hJRead x Y (hIW x hx) hY)
  have hωI : ∀ x, mem_l hℳ x K.omega → mem_l hℳ x I.val := by
    intro x hx
    exact hCI x (hωC x ((SecondOrderOmega.unique_l hℳ hω K.omega_spec).symm ▸ hx))
  have hCover := PowerlessRelativeCofinalHistoryCoverage.subset_l hBase K hLimit hW
    O e t₁ t₂ t₃ Pair N Valid Translation S hCode hωW hHistory
    (fun x hx => hCI x (hBC x hx)) (fun x hx => hCI x (hαC x hx)) hωI
    hBasis hFRead hFCall hGetter
  have hAI := PowerlessRelativeCofinalHistoryCoverage.level_l hα hHistory hCover hγα hA
  exact restriction_l hBase O ⟨A, PowerlessRelativeLevelClosure.class_l hℳ hBase hA⟩ I hCount hAI

/-- W 的每个实际成员落入一个可数传递低层；其计数图仍只要求 Class。 -/
theorem member_countable_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (K : source_coding_l hℳ) {ω Ω W X : Raw} (G : type_l hℳ B)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B ω Ω)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W) (hBW : mem_l hℳ B W)
    (hωB : ∀ x, mem_l hℳ x ω → mem_l hℳ x B)
    (hG : map_l (ℳ := 𝒱) G.val ω B)
    (hOnto : ∀ x, mem_l hℳ x B → ∃ i, mem_l hℳ i ω ∧ value_l (ℳ := 𝒱) G.val i x)
    (hXW : mem_l hℳ X W) : PowerlessRelativeOrdinalCutoff.countable_l B ω X := by
  have hLimit := PowerlessRelativeCutoffLimit.limit_l K hBase hω hΩ
  obtain ⟨γ, A, hγ, hA, hXA⟩ := (PowerlessRelativeLimitClosure.value_l hℳ hBase hLimit hW X).mp hXW
  let O : type_l hℳ B := ⟨ω, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ hω)⟩
  let Y : type_l hℳ B := ⟨X, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase
    (PowerlessRelativeLevelClosure.class_l hℳ hBase hW) hXW⟩
  let I : type_l hℳ B := ⟨A, PowerlessRelativeLevelClosure.class_l hℳ hBase hA⟩
  exact restriction_l hBase O Y I (countable_l hBase K G hω hΩ hW hBW hωB hG hOnto hγ hA)
    (PowerlessRelativeLevelClosure.transitive_l hℳ hBase hA X hXA)

def schema_m {Δ : SortContext ℒ} (B ω Ω W G γ A : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeOrdinalCutoff.first_m B ω Ω) <|
        .imp (PowerlessRelativeHierarchySyntax.level_m B Ω W) <|
          .imp (SecondOrderObjectSyntax.member_m B W) <|
            .imp (ThirdOrderTheory.subset_m ω B) <|
              .imp (PowerlessRelativeHierarchySyntax.class_m B G) <|
                .imp (SecondOrderObjectSyntax.map_m G ω B) <|
                  .imp (PowerlessRelativeClassEnumerationSectionDerives.onto_m G ω B) <|
                    .imp (SecondOrderObjectSyntax.member_m γ Ω) <|
                      .imp (PowerlessRelativeHierarchySyntax.level_m B γ A)
                        (PowerlessRelativeOrdinalCutoff.countable_m B ω A)

def sentence_m {Δ : SortContext ℒ} (B ω Ω W G γ A : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B ω Ω W G γ A)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B ω Ω W G γ A : Term ℒ [] Δ .set) :
    (sentence_m B ω Ω W G γ A).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeOrdinalCutoff.first_formula_l K,
    PowerlessRelativeOrdinalCutoff.countable_formula_l K,
    PowerlessRelativeHierarchySemantics.level_formula_l K, subset_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, map_formula_l,
    PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  intro η hBase hω hΩ hW hBW hωB hGClass hG hOnto hγ hA
  exact countable_l hBase K ⟨G.eval η, hGClass⟩ hω hΩ hW hBW hωB hG hOnto hγ hA

theorem derives_m {Δ : SortContext ℒ} (B ω Ω W G γ A : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m B ω Ω W G γ A)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 B ω Ω W G γ A)

def member_schema_m {Δ : SortContext ℒ} (B ω Ω W G X : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeOrdinalCutoff.first_m B ω Ω) <|
        .imp (PowerlessRelativeHierarchySyntax.level_m B Ω W) <|
          .imp (SecondOrderObjectSyntax.member_m B W) <|
            .imp (ThirdOrderTheory.subset_m ω B) <|
              .imp (PowerlessRelativeHierarchySyntax.class_m B G) <|
                .imp (SecondOrderObjectSyntax.map_m G ω B) <|
                  .imp (PowerlessRelativeClassEnumerationSectionDerives.onto_m G ω B) <|
                    .imp (SecondOrderObjectSyntax.member_m X W)
                      (PowerlessRelativeOrdinalCutoff.countable_m B ω X)

def member_sentence_m {Δ : SortContext ℒ} (B ω Ω W G X : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (member_schema_m B ω Ω W G X)

theorem member_models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B ω Ω W G X : Term ℒ [] Δ .set) :
    (member_sentence_m B ω Ω W G X).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [member_schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeOrdinalCutoff.first_formula_l K,
    PowerlessRelativeOrdinalCutoff.countable_formula_l K,
    PowerlessRelativeHierarchySemantics.level_formula_l K, subset_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, map_formula_l,
    PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  intro η hBase hω hΩ hW hBW hωB hGClass hG hOnto hX
  exact member_countable_l hBase K ⟨G.eval η, hGClass⟩ hω hΩ hW hBW hωB hG hOnto hX

theorem member_derives_m {Δ : SortContext ℒ} (B ω Ω W G X : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (member_sentence_m B ω Ω W G X)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => member_models_l h𝒩 B ω Ω W G X)

#print axioms countable_l
#print axioms member_countable_l
#print axioms derives_m
#print axioms member_derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffLevelCountability
