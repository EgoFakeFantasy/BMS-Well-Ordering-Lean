import BMSConstructibleBridge.PowerlessRelativeCutoffBelow
import BMSConstructibleBridge.PowerlessHereditarySuccessor
import BMSConstructibleBridge.SecondOrderOrdinalSuccessor

/-! # 首个类内不可数序数是极限序数

每个较小序数具有遗传包络，其实际后继仍在遗传域，因而仍类内可数
且低于截断点。ω<Ω 保证非空。这是内部序数与实际类内函数的证明，
不将环境可数性误作类内可数性，也不调用截断层的 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffLimit

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeOrdinalCutoff (first_l first_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Ordinal" => SetTheory.Structure.IsOrdinal
  (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱)

/-- 实际纯后继沿商代表传回已有图序数后继定理。 -/
theorem successor_ordinal_l {a b : SecondOrderQuotient.type_l hℳ} (ha : Ordinal a)
    (hSucc : PowerlessRelativeHierarchySemantics.successor_l hℳ a b) : Ordinal b := by
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ a
  obtain ⟨U, rfl⟩ := SecondOrderQuotient.surj_l hℳ b
  apply SecondOrderOrdinalSuccessor.ordinal_l hℳ A U ha
  intro X
  exact (hSucc (SecondOrderQuotient.mk_l hℳ X)).trans
    (or_congr Iff.rfl (SecondOrderQuotient.eq_iff_l hℳ X A))

theorem limit_l (K : source_coding_l hℳ) {B ω Ω : SecondOrderQuotient.type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hω : SecondOrderOmega.omega_l hℳ ω) (hΩ : first_l B ω Ω) :
    PowerlessRelativeHierarchySemantics.limit_l hℳ Ω := by
  refine ⟨⟨ω, PowerlessRelativeCutoffBelow.omega_below_l (hBase := hBase) K hω hΩ⟩, ?_⟩
  intro a ha
  have haOrd : Ordinal a := by
    apply SetTheory.Structure.IsOrdinal.mem hΩ.1
    exact ha
  have haHereditary := (PowerlessHereditaryOrdinalCountability.ordinal_iff_l
    (hBase := hBase) K hω haOrd).mp (hΩ.2.2 a ha)
  obtain ⟨b, hbHereditary, hSucc⟩ := PowerlessHereditarySuccessor.exists_l hBase haHereditary
  have hbOrd := successor_ordinal_l haOrd hSucc
  have hbCount := PowerlessHereditaryOrdinalCountability.countable_of_hereditary_l
    (hBase := hBase) K hω hbHereditary
  exact ⟨b, (PowerlessRelativeCutoffBelow.countable_iff_below_l
    (hBase := hBase) K hω hΩ hbOrd).mp hbCount, (hSucc a).mpr (Or.inr rfl)⟩

def schema_m : Formula ℒ [] [.set, .set, .set] :=
  let B : Term ℒ [] [.set, .set, .set] .set := .fvar .here
  let ω := .fvar (.there .here)
  let Ω := .fvar (.there (.there .here))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <| .imp (first_m B ω Ω)
      (PowerlessRelativeHierarchySyntax.limit_m Ω)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) : sentence_m.TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ,
    SecondOrderOmegaSyntax.omega_l hℳ, PowerlessRelativeOrdinalCutoff.first_formula_l K,
    PowerlessRelativeHierarchySemantics.limit_formula_l, Term.eval]
  exact fun hBase hω hΩ => limit_l K hBase hω hΩ

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffLimit
