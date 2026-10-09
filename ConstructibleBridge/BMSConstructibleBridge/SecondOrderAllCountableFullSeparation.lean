import BMSConstructibleBridge.SecondOrderAllCountableUniformBounding

/-! # 全类可数分支的完整 Separation

任意原有限公式先在母集赋值域上统一有界化，再使用已证的类内
Δ₀ 分离。见证界与有限参数只在 Prop 中消去；无完整源理论前提，
不把这一分支结论当作最终无条件的 BMS 对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAllCountableFullSeparation

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding StabilityFrame
open SecondOrderQuotient (mem_l)
open SecondOrderCanonicalLevelDerives (guard_l)
open _root_.YesMetaZFC.Automation

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.type_l PowerlessRelativeClassStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}
  {t₁ t₂ t₃ Pair Valid P₀ S : SecondOrderQuotient.type_l hℳ}

local notation "ClassModel" => PowerlessRelativeClassStructure.structure_l hℳ B hBase
local notation "CType" => PowerlessRelativeClassStructure.type_l hℳ B

private theorem opening_delta_l {Γ Δ : SortContext ℒ} {φ : Formula ℒ Γ Δ}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) :
    Formula.IsDelta0 membershipLevyBound (PowerlessSourceOpening.form_m φ) := by
  change Formula.IsDelta0 membershipLevyBound (φ.substituteMapped
    (fun {s} v => match s with | .set => .fvar (PowerlessSourceOpening.slot_m v))
    (fun {s} v => match s with | .set => .fvar (PowerlessSourceOpening.skip_m Γ.length v)))
  exact Formula.IsDelta0.substituteMapped _ _ hφ

private theorem opening_formula_l {Ξ : SortContext ℒ} (ψ : Formula ℒ [.set] Ξ)
    (θ : Env ClassModel [] Ξ) (x : CType) :
    (PowerlessSourceOpening.form_m ψ).satisfies (θ.pushFree x) ↔
      ψ.satisfies (ParameterFusion.join_l ((Env.empty).pushBound (sort := SetTheory.SetSort.set) x) θ) := by
  rw [PowerlessSourceOpening.form_m, Formula.satisfies_substitute]
  apply Iff.of_eq
  apply congrArg (fun ζ => ψ.satisfies ζ)
  apply Env.ext
  · intro s v
    cases s
    cases v with
    | here => rfl
    | there v => nomatch v
  · intro s v; cases s; rfl

variable (K : source_coding_l hℳ)
  (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
  (hGuard : guard_l B P₀)
  (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega S)
  (hAll : ∀ a, SetTheory.Structure.IsOrdinal
    (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)) a →
    PowerlessRelativeOrdinalCutoff.countable_l B K.omega a)

include K hCoding hGuard hS hAll in
/-- 无公式复杂度限制的原参数分离实例。 -/
theorem exists_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (η : Env ClassModel [] Δ) (A : CType) :
    ∃ Y : CType, ∀ x : CType, mem_l hℳ x.val Y.val ↔
      mem_l hℳ x.val A.val ∧ φ.satisfies (η.pushFree x) := by
  obtain ⟨Ξ, ψ, hψ, θ, hRead⟩ := SecondOrderAllCountableUniformBounding.exists_l
    K hCoding hGuard hS hAll φ.abstractFreeTop η A
  obtain ⟨Y, hY⟩ := PowerlessRelativeClassDeltaSeparation.exists_l (hBase := hBase) (opening_delta_l hψ) θ A
  refine ⟨Y, fun x => (hY x).trans (and_congr_right (fun hx => ?_))⟩
  have hρ : SecondOrderAllCountableUniformBounding.domain_l A
      (((Env.empty) : Env ClassModel [] []).pushBound (sort := SetTheory.SetSort.set) x) := by
    intro v
    cases v with
    | here => exact hx
    | there v => nomatch v
  have h := hRead (((Env.empty) : Env ClassModel [] []).pushBound (sort := SetTheory.SetSort.set) x) hρ
  have hAbstract : φ.abstractFreeTop.satisfies
      (ParameterFusion.join_l (((Env.empty) : Env ClassModel [] []).pushBound (sort := SetTheory.SetSort.set) x) η) ↔
      φ.satisfies (η.pushFree x) := by
    rw [ParameterFusion.push_bound_l, ParameterFusion.empty_join_l]
    exact Formula.satisfies_abstractFreeTop η x φ
  exact (opening_formula_l ψ θ x).trans (h.symm.trans hAbstract)

include K hCoding hGuard hS hAll in
theorem bound_exists_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ (.set :: Γ) Δ)
    (η : Env ClassModel Γ Δ) (A : CType) :
    ∃ Y : CType, ∀ x : CType, mem_l hℳ x.val Y.val ↔
      mem_l hℳ x.val A.val ∧ φ.satisfies (η.pushBound x) := by
  obtain ⟨Y, hY⟩ := exists_l K hCoding hGuard hS hAll (PowerlessSourceOpening.form_m φ)
    (PowerlessSourceOpening.env_l η) A
  exact ⟨Y, fun x => (hY x).trans
    (and_congr Iff.rfl (PowerlessSourceOpening.witness_l φ η x))⟩

include K hCoding hGuard hS hAll in
theorem source_models_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    (SecondOrderSeparationAxiom.sentence_m φ).TrueIn ClassModel := by
  apply (ModelClosure.forall_close_iff _).mpr
  intro η
  apply (PowerlessWeakSeparationSyntax.schema_formula_l φ η).mpr
  exact exists_l K hCoding hGuard hS hAll φ η

#print axioms exists_l
#print axioms source_models_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAllCountableFullSeparation
