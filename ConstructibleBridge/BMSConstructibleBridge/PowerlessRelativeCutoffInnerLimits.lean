import BMSConstructibleBridge.PowerlessRelativeClassCountableTailLimit
import BMSConstructibleBridge.PowerlessRelativeCutoffBelow
import BMSConstructibleBridge.PowerlessRelativeCofinalLimitBounds

/-! # 首个类内不可数序数以下的非零极限序数共尾

不是从“Ω 为极限”直接推得，而是对任意较小序数实际构造仍类内可数的
内部 ω 尾极限，再用首个不可数的特征将它放回 Ω 以下。
闭句使用原图翻译及原 Z₂ 推导核；不假定截断层的源理论模型。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffInnerLimits

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mk_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Ordinal" => SetTheory.Structure.IsOrdinal
  (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱)

theorem countable_exists_l (K : source_coding_l hℳ) {B α : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hα : Ordinal α) (hCount : PowerlessRelativeOrdinalCutoff.countable_l B K.omega α) :
    ∃ β : type_l hℳ, Ordinal β ∧ mem_l hℳ α β ∧
      PowerlessRelativeHierarchySemantics.limit_l hℳ β ∧
        PowerlessRelativeOrdinalCutoff.countable_l B K.omega β := by
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ α
  obtain ⟨S, hS⟩ := SecondOrderValidRootGraph.exists_l hℳ A.real
  have hW := SecondOrderValidRootGraph.wf_l hS
  have hEq : mk_l hℳ A = mk_l hℳ ⟨S, A.root, hW A.root⟩ :=
    (SecondOrderQuotient.eq_iff_l hℳ _ _).mpr
      (SecondOrderValidRootGraph.agrees_l hℳ hS A.root A.wf)
  obtain ⟨G, hG⟩ := SecondOrderOrdinalTailGraph.exists_l hℳ S A.root
  obtain ⟨C, hC⟩ := SecondOrderOrdinalTailRange.exists_l hℳ hG hW
  obtain ⟨hOrd, hMem, hNoMax⟩ := SecondOrderOrdinalTailLimit.properties_l hℳ hG hW
    (hEq ▸ hα) C hC
  have hMem' : mem_l hℳ (mk_l hℳ A) (mk_l hℳ C) := hEq.symm ▸ hMem
  exact ⟨mk_l hℳ C, hOrd, hMem', ⟨⟨mk_l hℳ A, hMem'⟩, hNoMax⟩,
    PowerlessRelativeClassCountableTailLimit.countable_l (hBase := hBase) K hG hW
      (hEq ▸ hα) (hEq ▸ hCount) C hC⟩

theorem exists_l (K : source_coding_l hℳ) {B ω Ω α : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hω : SecondOrderOmega.omega_l hℳ ω) (hΩ : PowerlessRelativeOrdinalCutoff.first_l B ω Ω)
    (hα : mem_l hℳ α Ω) : ∃ β : type_l hℳ, Ordinal β ∧ mem_l hℳ α β ∧ mem_l hℳ β Ω ∧
      PowerlessRelativeHierarchySemantics.limit_l hℳ β := by
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  have hαOrd : Ordinal α := by
    apply SetTheory.Structure.IsOrdinal.mem hΩ.1
    exact hα
  obtain ⟨β, hβ, hαβ, hLimit, hCount⟩ := countable_exists_l K hBase
    hαOrd (hωEq ▸ hΩ.2.2 α hα)
  exact ⟨β, hβ, hαβ, (PowerlessRelativeCutoffBelow.countable_iff_below_l
    (hBase := hBase) K hω hΩ hβ).mp (hωEq.symm ▸ hCount), hLimit⟩

theorem cofinal_l (K : source_coding_l hℳ) {B ω Ω : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hω : SecondOrderOmega.omega_l hℳ ω) (hΩ : PowerlessRelativeOrdinalCutoff.first_l B ω Ω) :
    PowerlessRelativeCofinalLimitBounds.cofinal_l Ω := by
  intro α hα
  obtain ⟨β, _, hαβ, hβΩ, hLimit⟩ := exists_l K hBase hω hΩ hα
  exact ⟨β, hβΩ, hαβ, hLimit⟩

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def schema_m : Formula ℒ [] [.set, .set, .set, .set] :=
  let α : Term ℒ [] [.set, .set, .set, .set] .set := .fvar .here
  let Ω := .fvar (.there .here)
  let ω := .fvar (.there (.there .here))
  let B := .fvar (.there (.there (.there .here)))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeOrdinalCutoff.first_m B ω Ω) <|
        .imp (SecondOrderObjectSyntax.member_m α Ω) <| .existsE .set <|
          .conj (PowerlessRelativeHierarchySyntax.ordinal_m (.bvar .here)) <|
            .conj (SecondOrderObjectSyntax.member_m (up α) (.bvar .here)) <|
              .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up Ω))
                (PowerlessRelativeHierarchySyntax.limit_m (.bvar .here))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) : sentence_m.TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeOrdinalCutoff.first_formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval, PowerlessRelativeHierarchySemantics.ordinal_formula_l,
    PowerlessRelativeHierarchySemantics.limit_formula_l, up, Term.eval_weakenBound, Term.eval]
  intro η hBase hω hΩ hα
  exact exists_l K hBase hω hΩ hα

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffInnerLimits
