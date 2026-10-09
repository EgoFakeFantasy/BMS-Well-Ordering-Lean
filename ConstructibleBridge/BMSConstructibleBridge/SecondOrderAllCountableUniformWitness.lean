import BMSConstructibleBridge.SecondOrderAllCountableQuantifiedSeparation
import BMSConstructibleBridge.PowerlessRelativeClassTupleCoding
import BMSConstructibleBridge.PowerlessRelativeLimitClosure
import BMSConstructibleBridge.PowerlessRelativeOrdinalCoverage
import YesMetaZFC.Automation.ParameterFusion

/-! # 集合界内全部有限赋值的共同见证界

先在实际极限层中编码有限赋值，再对原 SourceTuple 请求使用已证
Collection。界覆盖母集中的全部内部值，不依赖模型 ω 的外部标准性。
公式及编码存在量词保留在 Prop，不以完整源理论为循环前提。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAllCountableUniformWitness

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

variable (K : source_coding_l hℳ)
  (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
  (hGuard : guard_l B P₀)
  (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega S)
  (hAll : ∀ a, SetTheory.Structure.IsOrdinal
    (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)) a →
    PowerlessRelativeOrdinalCutoff.countable_l B K.omega a)

include K hCoding hGuard hS hAll in
/-- 一个集合界同时处理固定外部元数的所有内部赋值。 -/
theorem tuple_bound_l {Δ : SortContext ℒ} (n : Nat)
    (φ : Formula ℒ [] (.set :: (List.replicate n .set ++ Δ)))
    (η : Env ClassModel [] Δ) (D : CType) :
    ∃ C : CType, ∀ v : Values (ClassModel).Carrier (List.replicate n .set),
      PowerlessSourceTuple.bounded_l D n v →
      ((∃ y : CType, φ.satisfies ((PowerlessSourceTuple.env_l η n v).pushFree y)) ↔
        ∃ y : CType, mem_l hℳ y.val C.val ∧
          φ.satisfies ((PowerlessSourceTuple.env_l η n v).pushFree y)) := by
  obtain ⟨α, D₀, hD₀, hDD₀⟩ := D.property
  obtain ⟨β, hβ, hαβ, hNoMax⟩ := SecondOrderOrdinalLimitDerives.exists_l hℳ α
    (PowerlessRelativeLevelClosure.ordinal_l hℳ hD₀)
  obtain ⟨L, hL⟩ := PowerlessRelativeOrdinalCoverage.level_exists_l hℳ hBase hβ
  let L' : CType := ⟨L, PowerlessRelativeLevelClosure.class_l hℳ hBase hL⟩
  have hDL : mem_l hℳ D.val L :=
    PowerlessRelativeLevelClosure.subset_l hℳ hBase hαβ hD₀ hL D.val hDD₀
  have hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β := ⟨⟨α, hαβ⟩, hNoMax⟩
  have hClosed (a b p : CType) (ha : member_l ClassModel a L')
      (hb : member_l ClassModel b L') (hp : ordered_l (ℳ := ClassModel) a b p) :
      member_l ClassModel p L' :=
    PowerlessRelativeLimitClosure.ordered_l hℳ hBase hLimit hL ha hb
      ((PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) a b p).mp hp)
  obtain ⟨C, hC⟩ := SecondOrderAllCountableQuantifiedSeparation.bound_l
    K hCoding hGuard hS hAll (PowerlessSourceTuple.form_m n φ) η L'
  refine ⟨C, fun v hv => ⟨?_, fun ⟨y, _, hy⟩ => ⟨y, hy⟩⟩⟩
  rintro ⟨y, hy⟩
  have hvL := PowerlessRelativeClassTupleCoding.bounded_mono_l
    (𝒩 := ClassModel) (A := D) (D := L')
    (fun x hx => PowerlessRelativeLevelClosure.transitive_l hℳ hBase hL D.val hDL x.val hx)
    n v hv
  obtain ⟨p, hpL, hp⟩ := PowerlessRelativeClassTupleCoding.code_exists_l (hBase := hBase) L' D hDL hClosed n v hvL
  have hRead (z : CType) := PowerlessRelativeClassTupleCoding.formula_l (hBase := hBase) η n φ v hp z
  obtain ⟨z, hzC, hz⟩ := (hC p hpL).mp ⟨y, (hRead y).mpr hy⟩
  exact ⟨z, hzC, (hRead z).mp hz⟩

private theorem values_join_l {Γ Δ : SortContext ℒ}
    (ρ : Env ClassModel Γ []) (η : Env ClassModel [] Δ) :
    PowerlessSourceOpening.values_l (ParameterFusion.join_l ρ η) = PowerlessSourceOpening.values_l ρ := by
  cases Γ with
  | nil => rfl
  | cons s Γ =>
    cases s
    exact congrArg (fun v => Values.cons (ρ.boundVal .here) v)
      (values_join_l (PowerlessSourceOpening.tail_l ρ) η)

private theorem opening_join_l {Γ Δ : SortContext ℒ}
    (ρ : Env ClassModel Γ []) (η : Env ClassModel [] Δ) :
    PowerlessSourceOpening.env_l (ParameterFusion.join_l ρ η) =
      PowerlessSourceTuple.env_l η Γ.length (PowerlessSourceOpening.values_l ρ) := by
  unfold PowerlessSourceOpening.env_l
  rw [values_join_l]
  have hFree : PowerlessSourceClass.free_l (ParameterFusion.join_l ρ η) = η := by
    apply Env.ext
    · intro s v; nomatch v
    · intro s v; rfl
  rw [hFree]

include K hCoding hGuard hS hAll in
/-- 绑定上下文中的所有值均在 D 内时，存在量词有统一的类内见证界。 -/
theorem bound_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ (.set :: Γ) Δ)
    (η : Env ClassModel [] Δ) (D : CType) :
    ∃ C : CType, ∀ (ρ : Env ClassModel Γ []),
      (∀ v : Variable Γ .set, member_l ClassModel (ρ.boundVal v) D) →
      ((∃ y : CType, φ.satisfies ((ParameterFusion.join_l ρ η).pushBound y)) ↔
        ∃ y : CType, mem_l hℳ y.val C.val ∧
          φ.satisfies ((ParameterFusion.join_l ρ η).pushBound y)) := by
  obtain ⟨C, hC⟩ := tuple_bound_l K hCoding hGuard hS hAll Γ.length
    (PowerlessSourceOpening.form_m φ) η D
  refine ⟨C, fun ρ hρ => ?_⟩
  have hRead (y : CType) :
      (PowerlessSourceOpening.form_m φ).satisfies
        ((PowerlessSourceTuple.env_l η Γ.length (PowerlessSourceOpening.values_l ρ)).pushFree y) ↔
      φ.satisfies ((ParameterFusion.join_l ρ η).pushBound y) := by
    rw [← opening_join_l]
    exact PowerlessSourceOpening.witness_l φ (ParameterFusion.join_l ρ η) y
  exact (exists_congr hRead).symm.trans ((hC (PowerlessSourceOpening.values_l ρ)
    (PowerlessSourceOpening.bounded_l ρ D hρ)).trans
      (exists_congr (fun y => and_congr_right (fun _ => hRead y))))

#print axioms tuple_bound_l
#print axioms bound_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAllCountableUniformWitness
