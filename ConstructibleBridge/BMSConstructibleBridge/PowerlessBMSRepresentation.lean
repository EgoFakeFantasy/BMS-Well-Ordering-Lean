import BMSConstructibleBridge.PowerlessBMSAncestor
import BMSConstructibleBridge.PowerlessGoodChain
import BMSConstructibleBridge.PowerlessConcatenation

/-!
# 原数组码的实际初始标签表示

长度取自原 length 程序，祖先边取自原统一成员程序；二者均允许非标准内部输入。
H 只指定本表示检查的有限行，不声称数组实际高度已经小于等于 H。
本模块构造初始表示，尚不证明原展开保持或最终下降。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSRepresentation

open Logic FirstOrder ThirdOrderSemantics
open PowerlessRelabelLevels (level_m)

set_option autoImplicit false

attribute [local implicit_reducible] PowerlessArithmetic.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  {ω e : carrier_l ℳ} {he : PowerlessNatural.zero_l e} {h₀ : member_l ℳ e ω}
  {F : PowerlessArithmetic.operations_l ω e}

local notation "𝒩" => PowerlessArithmetic.structure_l he h₀ F

def width_l (x q : PowerlessArithmetic.num_l ω) : Prop :=
  (PrimitiveProgram.form_m SecondOrderProgramLength.length_m (.fvar .here) (.fvar (.there .here))).satisfies
    (((Env.empty (M := 𝒩)).pushFree (σ := SecondOrderSyntax.signature_m) (sort := .num) q).pushFree
      (σ := SecondOrderSyntax.signature_m) (sort := .num) x)

theorem width_graph_l {L : PowerlessArithmetic.set_l ω}
    (hL : SecondOrderProgramSemantics.graph_semantics_l (ℳ := 𝒩)
      (PrimitiveProgram.graph_m SecondOrderProgramLength.length_m) L) (x q : PowerlessArithmetic.num_l ω) :
    width_l (he := he) (h₀ := h₀) (F := F) x q ↔ SecondOrderPairing.relation_l (ℳ := 𝒩) L x q :=
  hL _ _ _

structure representation_l (T t₁ t₂ t₃ c N : carrier_l ℳ) (H : Nat)
    (x q : PowerlessArithmetic.num_l ω) (β f : carrier_l ℳ) : Prop where
  width_l : PowerlessBMSRepresentation.width_l (he := he) (h₀ := h₀) (F := F) x q
  map_l : ThirdOrderSemantics.map_l f q.val β
  labels_l : ∀ i a, value_l f i a → PowerlessCodedDiagram.good_l ω e T t₁ t₂ t₃ c N a
  order_l : PowerlessConcatenation.increasing_l f
  edge_l : ∀ j, j < H → ∀ r : PowerlessArithmetic.num_l ω, PowerlessNumeral.numeral_l e j r.val →
    ∀ i t : PowerlessArithmetic.num_l ω, PowerlessBMSAncestor.ancestor_l (he := he) (h₀ := h₀) (F := F) x r t i →
      ∀ a b, value_l f i.val a → value_l f t.val b →
        ∃ m, PowerlessNumeral.numeral_l e (level_m (H + 1) j) m ∧
          PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ m a b

/-- 全对稳定的内部链为原祖先关系提供初始表示，祖先严格向左来自原程序定理。 -/
theorem of_chain_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    {T t₁ t₂ t₃ c N β f : carrier_l ℳ} {H : Nat} {x q : PowerlessArithmetic.num_l ω}
    (hx : width_l (he := he) (h₀ := h₀) (F := F) x q) (hf : map_l f q.val β)
    (hF : ∀ i a, value_l f i a → PowerlessCodedDiagram.good_l ω e T t₁ t₂ t₃ c N a)
    (hS : ∀ i j a b, member_l ℳ i j → value_l f i a → value_l f j b →
      member_l ℳ a b ∧ PowerlessGoodLabels.stable_l ω e T t₁ t₂ t₃ c N (H + 1) a b) :
    representation_l (he := he) (h₀ := h₀) (F := F) T t₁ t₂ t₃ c N H x q β f := by
  refine ⟨hx, hf, hF, fun i j a b hij ha hb => (hS i j a b hij ha hb).1, ?_⟩
  intro j hj r _ i t h a b ha hb
  have hit := PowerlessBMSAncestor.bound_l hℳ hω h
  obtain ⟨m, hm, h₁⟩ := (hS i.val t.val a b hit ha hb).2 j (Nat.lt_trans hj (Nat.lt_succ_self H))
  exact ⟨m, hm, h₁.2.2⟩

/-- 同一支持码与最小边界容纳所有原数组码的实际内部宽度，不逐数组重选背景。 -/
theorem initial_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    {T t₁ t₂ t₃ : carrier_l ℳ} (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T) (H : Nat) :
    ∃ c N n σ, member_l ℳ c ω ∧ member_l ℳ N ω ∧
      PowerlessGoodBoundary.code_l ω e T t₁ t₂ t₃ c N (level_m (H + 1) (H + 1)) ∧
      PowerlessNumeral.numeral_l e (level_m (H + 1) (H + 1)) n ∧
      PowerlessGoodBoundary.boundary_l ω e T t₁ t₂ t₃ c N n σ ∧
      ∀ x : PowerlessArithmetic.num_l ω, ∃ q : PowerlessArithmetic.num_l ω, ∃ f,
        representation_l (he := he) (h₀ := h₀) (F := F) T t₁ t₂ t₃ c N H x q σ f := by
  obtain ⟨c, N, n, σ, hc₀, hN, hc, hn, hσ, h⟩ := PowerlessGoodChain.initial_l hℳ hω ht hT H
  have h𝒩 := PowerlessArithmeticComprehension.models_l hℳ hω (he := he) (h₀ := h₀) (F := F)
  obtain ⟨L, hLf, hL⟩ := SecondOrderProgramTotality.graph_total_l h𝒩 SecondOrderProgramLength.length_m
  refine ⟨c, N, n, σ, hc₀, hN, hc, hn, hσ, fun x => ?_⟩
  obtain ⟨q, hq, _⟩ := hLf x
  obtain ⟨f, hf, hF, hS⟩ := h q.val q.property
  exact ⟨q, f, of_chain_l hℳ hω ((width_graph_l hL x q).mpr hq) hf
    (fun i a ha => (hF i a ha).1) hS⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSRepresentation
