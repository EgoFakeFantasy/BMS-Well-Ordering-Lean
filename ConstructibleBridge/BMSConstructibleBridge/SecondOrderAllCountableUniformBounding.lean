import BMSConstructibleBridge.SecondOrderAllCountableUniformWitness
import YesMetaZFC.Automation.BoundedFormulaCertificate

/-! # 全类可数分支中任意有限公式的统一有界化

对原 Formula 作结构归纳。每个量词使用自身的共同见证界，并在
一个包含旧赋值和新见证的类集合上归纳其正文。独立布尔分支的
界参数显式拼接，绝不以同一个任意扩大界替换全部量词。
这一步是完整 Separation 的语义中间结果，不是最终 BMS Derives。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAllCountableUniformBounding

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding StabilityFrame
open SecondOrderQuotient (mem_l)
open SecondOrderCanonicalLevelDerives (guard_l)
open _root_.YesMetaZFC.Automation

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.type_l PowerlessRelativeClassStructure.structure_l

universe u

/-- 排序字段直接可约化；与公开的标准成员界定义相同。 -/
private abbrev setBound : Formula.LevyBound ℒ :=
  ⟨SetTheory.SetSort.set, SetTheory.RelationSymbol.membership, rfl⟩

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}
  {t₁ t₂ t₃ Pair Valid P₀ S : SecondOrderQuotient.type_l hℳ}

local notation "ClassModel" => PowerlessRelativeClassStructure.structure_l hℳ B hBase
local notation "CType" => PowerlessRelativeClassStructure.type_l hℳ B

def domain_l {Γ : SortContext ℒ} (D : CType) (ρ : Env ClassModel Γ []) : Prop :=
  ∀ v : Variable Γ .set, member_l ClassModel (ρ.boundVal v) D

private theorem common_l (D C : CType) : ∃ E : CType,
    (∀ x : CType, member_l ClassModel x D → member_l ClassModel x E) ∧
    (∀ x : CType, member_l ClassModel x C → member_l ClassModel x E) := by
  obtain ⟨α, L, hL, hDL, hCL⟩ := PowerlessRelativeClassBounds.common_l hℳ hBase D.property C.property
  let E : CType := ⟨L, PowerlessRelativeLevelClosure.class_l hℳ hBase hL⟩
  exact ⟨E, fun x hx => PowerlessRelativeLevelClosure.transitive_l hℳ hBase hL D.val hDL x.val hx,
    fun x hx => PowerlessRelativeLevelClosure.transitive_l hℳ hBase hL C.val hCL x.val hx⟩

private theorem push_domain_l {Γ : SortContext ℒ} {D C E : CType}
    (hD : ∀ x : CType, member_l ClassModel x D → member_l ClassModel x E)
    (hC : ∀ x : CType, member_l ClassModel x C → member_l ClassModel x E)
    {ρ : Env ClassModel Γ []} (hρ : domain_l D ρ) {y : CType} (hy : member_l ClassModel y C) :
    domain_l E (ρ.pushBound (sort := SetTheory.SetSort.set) y) := by
  intro v
  cases v with
  | here => exact hC y hy
  | there v => exact hD (ρ.boundVal v) (hρ v)

private theorem weaken_delta_l {Γ Ξ : SortContext ℒ} {ψ : Formula ℒ Γ Ξ}
    (hψ : Formula.IsDelta0 setBound ψ) :
    Formula.IsDelta0 setBound (ψ.weakenFree SetTheory.SetSort.set) := by
  rw [Formula.weakenFree_eq_renameMapped, ← Formula.substituteMapped_of_renaming]
  exact Formula.IsDelta0.substituteMapped (fun v => .bvar v) (fun v => .fvar (.there v)) hψ

private theorem exists_formula_l {Γ Ξ : SortContext ℒ} (ψ : Formula ℒ (.set :: Γ) Ξ)
    (ρ : Env ClassModel Γ []) (θ : Env ClassModel [] Ξ) (C : CType) :
    (setBound.boundedExists (.fvar .here : Term ℒ Γ (.set :: Ξ) .set)
      (show Formula ℒ (.set :: Γ) (.set :: Ξ) from ψ.weakenFree SetTheory.SetSort.set)).satisfies
      (ParameterFusion.join_l ρ (θ.pushFree C)) ↔
    ∃ y : CType, member_l ClassModel y C ∧ ψ.satisfies (ParameterFusion.join_l (ρ.pushBound y) θ) := by
  change (∃ y : CType, member_l ClassModel y C ∧
    (ψ.weakenFree SetTheory.SetSort.set).satisfies
      ((ParameterFusion.join_l (ρ.pushBound y) θ).pushFree C)) ↔ _
  simp only [Formula.satisfies_weakenFree]

private theorem forall_formula_l {Γ Ξ : SortContext ℒ} (ψ : Formula ℒ (.set :: Γ) Ξ)
    (ρ : Env ClassModel Γ []) (θ : Env ClassModel [] Ξ) (C : CType) :
    (setBound.boundedForall (.fvar .here : Term ℒ Γ (.set :: Ξ) .set)
      (show Formula ℒ (.set :: Γ) (.set :: Ξ) from ψ.weakenFree SetTheory.SetSort.set)).satisfies
      (ParameterFusion.join_l ρ (θ.pushFree C)) ↔
    ∀ y : CType, member_l ClassModel y C → ψ.satisfies (ParameterFusion.join_l (ρ.pushBound y) θ) := by
  change (∀ y : CType, member_l ClassModel y C →
    (ψ.weakenFree SetTheory.SetSort.set).satisfies
      ((ParameterFusion.join_l (ρ.pushBound y) θ).pushFree C)) ↔ _
  simp only [Formula.satisfies_weakenFree]

variable (K : source_coding_l hℳ)
  (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
  (hGuard : guard_l B P₀)
  (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega S)
  (hAll : ∀ a, SetTheory.Structure.IsOrdinal
    (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)) a →
    PowerlessRelativeOrdinalCutoff.countable_l B K.omega a)

include K hCoding hGuard hS hAll in
/-- 原有限公式在指定集合内的全部绑定赋值上有一个带有限参数的 Δ₀ 等价式。 -/
theorem exists_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ Γ Δ)
    (η : Env ClassModel [] Δ) (D : CType) :
    BoundedFormulaCertificate.certificate_l membershipLevyBound φ η (domain_l D) := by
  classical
  change BoundedFormulaCertificate.certificate_l setBound φ η (domain_l D)
  induction φ generalizing D with
  | falsum => exact ⟨_, .falsum, .falsum, η, fun _ _ => Iff.rfl⟩
  | truth => exact ⟨_, .truth, .truth, η, fun _ _ => Iff.rfl⟩
  | rel r a => exact ⟨_, .rel r a, .rel r a, η, fun _ _ => Iff.rfl⟩
  | equal a b => exact ⟨_, .equal a b, .equal a b, η, fun _ _ => Iff.rfl⟩
  | neg φ ih =>
    obtain ⟨Ξ, ψ, hψ, θ, hRead⟩ := ih η D
    exact ⟨Ξ, .neg ψ, .neg hψ, θ, fun ρ hρ => not_congr (hRead ρ hρ)⟩
  | conj φ χ ihφ ihχ =>
    exact BoundedFormulaCertificate.combine_l (fun a b => .conj a b) And
      (fun ha hb => .conj ha hb) (fun _ _ _ => Iff.rfl) (fun hp hq => and_congr hp hq) (ihφ η D) (ihχ η D)
  | disj φ χ ihφ ihχ =>
    exact BoundedFormulaCertificate.combine_l (fun a b => .disj a b) Or
      (fun ha hb => .disj ha hb) (fun _ _ _ => Iff.rfl) (fun hp hq => or_congr hp hq) (ihφ η D) (ihχ η D)
  | imp φ χ ihφ ihχ =>
    exact BoundedFormulaCertificate.combine_l (fun a b => .imp a b) (fun p q => p → q)
      (fun ha hb => .imp ha hb) (fun _ _ _ => Iff.rfl) (fun hp hq => imp_congr hp hq) (ihφ η D) (ihχ η D)
  | iff φ χ ihφ ihχ =>
    exact BoundedFormulaCertificate.combine_l (fun a b => .iff a b) Iff
      (fun ha hb => .iff ha hb) (fun _ _ _ => Iff.rfl) (fun hp hq => iff_congr hp hq) (ihφ η D) (ihχ η D)
  | existsE s φ ih =>
    cases s
    obtain ⟨C, hC⟩ := SecondOrderAllCountableUniformWitness.bound_l K hCoding hGuard hS hAll φ η D
    obtain ⟨E, hDE, hCE⟩ := common_l (hBase := hBase) D C
    obtain ⟨Ξ, ψ, hψ, θ, hRead⟩ := ih η E
    refine ⟨.set :: Ξ, setBound.boundedExists (.fvar .here : Term ℒ _ (.set :: Ξ) .set)
      (show Formula ℒ _ (.set :: Ξ) from ψ.weakenFree SetTheory.SetSort.set),
      .bounded_exists _ (weaken_delta_l hψ), θ.pushFree C, fun ρ hρ => ?_⟩
    change (∃ y : CType, φ.satisfies ((ParameterFusion.join_l ρ η).pushBound y)) ↔ _
    exact (hC ρ hρ).trans ((exists_congr (fun y => and_congr_right (fun hy =>
      hRead (ρ.pushBound y) (push_domain_l (hBase := hBase) hDE hCE hρ hy)))).trans (exists_formula_l ψ ρ θ C).symm)
  | forallE s φ ih =>
    cases s
    obtain ⟨C, hC⟩ := SecondOrderAllCountableUniformWitness.bound_l K hCoding hGuard hS hAll (.neg φ) η D
    obtain ⟨E, hDE, hCE⟩ := common_l (hBase := hBase) D C
    obtain ⟨Ξ, ψ, hψ, θ, hRead⟩ := ih η E
    refine ⟨.set :: Ξ, setBound.boundedForall (.fvar .here : Term ℒ _ (.set :: Ξ) .set)
      (show Formula ℒ _ (.set :: Ξ) from ψ.weakenFree SetTheory.SetSort.set),
      .bounded_forall _ (weaken_delta_l hψ), θ.pushFree C, fun ρ hρ => ?_⟩
    have hCounter := not_congr (hC ρ hρ)
    change (¬∃ y : CType, ¬φ.satisfies ((ParameterFusion.join_l ρ η).pushBound y)) ↔
      (¬∃ y : CType, mem_l hℳ y.val C.val ∧ ¬φ.satisfies ((ParameterFusion.join_l ρ η).pushBound y)) at hCounter
    have hForall : (∀ y : CType, φ.satisfies ((ParameterFusion.join_l ρ η).pushBound y)) ↔
        ∀ y : CType, mem_l hℳ y.val C.val → φ.satisfies ((ParameterFusion.join_l ρ η).pushBound y) := by
      simpa only [not_exists, not_and, not_not] using hCounter
    exact hForall.trans ((forall_congr' (fun y => imp_congr_right (fun hy =>
      hRead (ρ.pushBound y) (push_domain_l (hBase := hBase) hDE hCE hρ hy)))).trans (forall_formula_l ψ ρ θ C).symm)

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAllCountableUniformBounding
