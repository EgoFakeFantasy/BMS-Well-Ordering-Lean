import BMSConstructibleBridge.PowerlessBMSStrictDescent
import BMSConstructibleBridge.PowerlessBMSChainMinimum
import BMSConstructibleBridge.PowerlessArithmeticRelation
import BMSConstructibleBridge.PowerlessArithmeticNumeral
import BMSConstructibleBridge.SecondOrderNormalizedCounterexample

/-!
# 无幂集背景中的原固定行数良序句

对同一内部反例实数，最小化链中可表示项的序数上界；真实严格展开使该上界更小，
与最小性矛盾。标签预算固定，反例链、宽度、复制次数都允许非标准内部值。
结论是 PowerlessTheory 模型的算术约化满足原 closed_m H；尚非 Z₂ 的推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSWellOrder

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderModel (succ_l zero_l)
open SecondOrderProgramSemantics SecondOrderProgramTotality SecondOrderProgramArithmetic
open PrimitiveProgram (graph_m)

set_option autoImplicit false

attribute [local implicit_reducible] PowerlessArithmetic.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  {ω e : carrier_l ℳ} {he : PowerlessNatural.zero_l e} {h₀ : member_l ℳ e ω}
  {F : PowerlessArithmetic.operations_l ω e}

local notation "𝒩" => PowerlessArithmetic.structure_l he h₀ F

/-- 固定行界内不存在全部步骤均为真实严格展开的内部数组函数。 -/
theorem no_chain_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    {X L E Y : PowerlessArithmetic.set_l ω}
    (hX : graph_semantics_l (ℳ := 𝒩) (graph_m SecondOrderProgramExpansion.expand_m) X)
    (hL : graph_semantics_l (ℳ := 𝒩) (graph_m SecondOrderProgramLength.length_m) L)
    (hE : graph_semantics_l (ℳ := 𝒩) (graph_m SecondOrderProgramListLookup.lookup_m) E)
    (hY : SecondOrderFunctions.function_l (ℳ := 𝒩) Y)
    {H : Nat} {bound : carrier_l ℳ} (hbound : PowerlessNumeral.numeral_l e H bound)
    (hshape : ∀ i x, SecondOrderPairing.relation_l (ℳ := 𝒩) Y i x →
      ∃ q height, SecondOrderProgramRectangular.rectangular_l (ℳ := 𝒩) L E x q height ∧
        subset_l height.val bound)
    (hstep : ∀ i x y, SecondOrderPairing.relation_l (ℳ := 𝒩) Y i x →
      SecondOrderPairing.relation_l (ℳ := 𝒩) Y (succ_l i) y →
      ∃ k, SecondOrderPairing.relation_l (ℳ := 𝒩) X (SecondOrderPairing.value_l x k) y ∧ y ≠ x) : False := by
  have h𝒩 := PowerlessArithmeticComprehension.models_l hℳ hω (he := he) (h₀ := h₀) (F := F)
  obtain ⟨t₁, t₂, t₃, ht⟩ := PowerlessEvaluationTags.exists_l hℳ he
  obtain ⟨T, hT⟩ := PowerlessTriangular.exists_l hℳ hω he
  obtain ⟨c, N, n, σ, hc₀, hN, hc, _, hσ, hInitial⟩ :=
    PowerlessBMSRepresentation.initial_l hℳ hω (he := he) (h₀ := h₀) (F := F) ht hT H
  obtain ⟨G, hG⟩ := PowerlessArithmeticRelation.exists_l hℳ hω (he := he) (h₀ := h₀) (F := F) Y
  obtain ⟨x₀, hx₀, _⟩ := hY (zero_l 𝒩)
  obtain ⟨q₀, f₀, hf₀⟩ := hInitial x₀
  obtain ⟨β, hσβ⟩ := hσ.1
  apply PowerlessBMSChainMinimum.no_chain_l hℳ hω
    (T := T) (t₁ := t₁) (t₂ := t₂) (t₃ := t₃) (c := c) (N := N) (H := H) (G := G)
    ⟨σ, hσβ.1.2.1.1, zero_l 𝒩, x₀, q₀, f₀, (PowerlessArithmeticRelation.value_l hℳ hG _ _).mpr hx₀, hf₀⟩
  intro i x q σ f hix hf
  have hx := (PowerlessArithmeticRelation.value_l hℳ hG i x).mp hix
  let j : PowerlessArithmetic.num_l ω := F.succ_l i
  obtain ⟨y, hy, _⟩ := hY j
  obtain ⟨k, hxy, hne⟩ := hstep i x y hx hy
  obtain ⟨width, height, hrect, hheight⟩ := hshape i x hx
  have hwidth : width = q := SecondOrderProgramSemantics.function_value_unique_l
    (function_of_semantics_l h𝒩 SecondOrderProgramLength.length_m hL) hrect.1
      ((PowerlessBMSRepresentation.width_graph_l hL x q).mp hf.width_l)
  subst width
  obtain ⟨r, α, g, hασ, hg⟩ := PowerlessBMSStrictDescent.exists_l hℳ hω
    hX hL hE hrect hxy hne ht hT hc hc₀ hN hbound hheight hf
  have hyG : ThirdOrderSemantics.value_l G j.val y.val :=
    (PowerlessArithmeticRelation.value_l hℳ hG j y).mpr hy
  exact ⟨j, y, r, α, g, hyG, hασ, hg⟩

/-- 原具体矩阵的任意内部候选实数均不能给出固定当前行界下的反例。 -/
theorem matrix_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    (H : Nat) (η : Env 𝒩 [.set] [.num])
    (hη : η.freeVal .here = numeral_val_l (ℳ := 𝒩) H) :
    SecondOrderConcreteFormula.matrix_m.satisfies η := by
  classical
  by_contra hbad
  have h𝒩 := PowerlessArithmeticComprehension.models_l hℳ hω (he := he) (h₀ := h₀) (F := F)
  obtain ⟨D, _, hD⟩ := graph_total_l h𝒩 SecondOrderProgramGeneratedDecode.decode_m
  obtain ⟨X, _, hX⟩ := graph_total_l h𝒩 SecondOrderProgramExpansion.expand_m
  obtain ⟨Z, _, hZ⟩ := graph_total_l h𝒩 SecondOrderProgramTrimHeight.trim_m
  obtain ⟨L, _, hL⟩ := graph_total_l h𝒩 SecondOrderProgramLength.length_m
  obtain ⟨E, _, hE⟩ := graph_total_l h𝒩 SecondOrderProgramListLookup.lookup_m
  obtain ⟨Y, hY, _, hshape, hstep⟩ := SecondOrderNormalizedCounterexample.arrays_l h𝒩 hD hX hZ hL hE H η hη hbad
  apply no_chain_l hℳ hω hX hL hE hY (PowerlessArithmeticNumeral.numeral_l (he := he) (h₀ := h₀) (F := F) H) ?_ hstep
  intro i x hx
  obtain ⟨q, k, hk, hrect, _, _⟩ := hshape i x hx
  exact ⟨q, numeral_val_l (ℳ := 𝒩) k, hrect,
    PowerlessSourceStandardBudget.numeral_le_subset_l hℳ e hk
      (PowerlessArithmeticNumeral.numeral_l (he := he) (h₀ := h₀) (F := F) k)
      (PowerlessArithmeticNumeral.numeral_l (he := he) (h₀ := h₀) (F := F) H)⟩

/-- 任意无幂集背景模型的同一算术约化满足原闭句；未声称背景消去已经完成。 -/
theorem models_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω) (H : Nat) :
    (SecondOrderConcreteFormula.closed_m H).TrueIn 𝒩 := by
  change Formula.satisfies (Env.empty (M := 𝒩))
    (PureSecondOrder.closed_m SecondOrderConcreteFormula.matrix_m H)
  rw [PureSecondOrder.closed_m, Formula.satisfies_instantiateFreeTop]
  intro X
  exact matrix_l hℳ hω H _ rfl

#print axioms no_chain_l
#print axioms matrix_l
#print axioms models_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSWellOrder
