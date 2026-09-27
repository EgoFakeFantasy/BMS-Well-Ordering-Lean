import BMSConstructibleBridge.PowerlessBMSRepresentation
import BMSConstructibleBridge.SecondOrderProgramCopiesBlockParentAncestor

/-!
# 同一内部数域中的副本段祖先对应

复制输入与输出取自原 copy_m、copies_m 程序的实际公式，不假设宿主执行结果。
段内祖先对应消费弱父平移与出段同步；不加入错误的缺项双向对应。
副本下标、总次数、行列和块宽均允许为非标准内部自然数。
本模块只处理副本段内部，不声称前缀或跨副本区域已经闭合。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSCopyAncestor

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderProgramSemantics SecondOrderProgramTotality
open PrimitiveProgram (graph_m)

set_option autoImplicit false

attribute [local implicit_reducible] PowerlessArithmetic.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  {ω e : carrier_l ℳ} {he : PowerlessNatural.zero_l e} {h₀ : member_l ℳ e ω}
  {F : PowerlessArithmetic.operations_l ω e}

local notation "𝒩" => PowerlessArithmetic.structure_l he h₀ F

private def application_l (c : PrimitiveProgram.code_m) (x y : PowerlessArithmetic.num_l ω) : Prop :=
  (PrimitiveProgram.form_m c (.fvar .here) (.fvar (.there .here))).satisfies
    (((Env.empty (M := 𝒩)).pushFree (σ := SecondOrderSyntax.signature_m) (sort := .num) y).pushFree
      (σ := SecondOrderSyntax.signature_m) (sort := .num) x)

private theorem application_graph_l {c : PrimitiveProgram.code_m} {X : PowerlessArithmetic.set_l ω}
    (hX : graph_semantics_l (ℳ := 𝒩) (graph_m c) X) (x y : PowerlessArithmetic.num_l ω) :
    application_l (he := he) (h₀ := h₀) (F := F) c x y ↔ SecondOrderPairing.relation_l (ℳ := 𝒩) X x y :=
  hX _ _ _

def copy_l (b A k l y : PowerlessArithmetic.num_l ω) : Prop :=
  application_l (he := he) (h₀ := h₀) (F := F) SecondOrderProgramCopyBlock.copy_m
    (SecondOrderPairing.value_l (ℳ := 𝒩) b
      (SecondOrderPairing.value_l A (SecondOrderPairing.value_l k l))) y

def copies_l (b A l n y : PowerlessArithmetic.num_l ω) : Prop :=
  application_l (he := he) (h₀ := h₀) (F := F) SecondOrderProgramCopies.copies_m
    (SecondOrderPairing.value_l (ℳ := 𝒩) (SecondOrderPairing.value_l b (SecondOrderPairing.value_l A l)) n) y

theorem ancestor_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    {b w A l k v n y : PowerlessArithmetic.num_l ω}
    (hb : PowerlessBMSRepresentation.width_l (he := he) (h₀ := h₀) (F := F) b w)
    (hk : member_l ℳ k.val n.val)
    (hv : copy_l (he := he) (h₀ := h₀) (F := F) b A k l v)
    (hy : copies_l (he := he) (h₀ := h₀) (F := F) b A l n y)
    (r t i : PowerlessArithmetic.num_l ω) (ht : member_l ℳ t.val w.val) :
    PowerlessBMSAncestor.ancestor_l (he := he) (h₀ := h₀) (F := F) y r
        (SecondOrderModel.add_l (ℳ := 𝒩) (SecondOrderModel.mul_l w k) t)
        (SecondOrderModel.add_l (ℳ := 𝒩) (SecondOrderModel.mul_l w k) i) ↔
      PowerlessBMSAncestor.ancestor_l (he := he) (h₀ := h₀) (F := F) v r t i := by
  have h𝒩 := PowerlessArithmeticComprehension.models_l hℳ hω (he := he) (h₀ := h₀) (F := F)
  obtain ⟨R, _, hR⟩ := graph_total_l h𝒩 SecondOrderProgramCopies.copies_m
  obtain ⟨C, _, hC⟩ := graph_total_l h𝒩 SecondOrderProgramCopyBlock.copy_m
  obtain ⟨O, _, hO⟩ := graph_total_l h𝒩 SecondOrderProgramOptionalLookup.optional_m
  obtain ⟨L, _, hL⟩ := graph_total_l h𝒩 SecondOrderProgramLength.length_m
  obtain ⟨E, _, hE⟩ := graph_total_l h𝒩 SecondOrderProgramListLookup.lookup_m
  obtain ⟨J, _, hJ⟩ := graph_total_l h𝒩 SecondOrderProgramEntry.entry_m
  obtain ⟨P, _, hP⟩ := graph_total_l h𝒩 SecondOrderProgramUniformParent.parent_m
  obtain ⟨M, _, hM⟩ := graph_total_l h𝒩 PowerlessBMSAncestor.program_m
  have hb₀ := (PowerlessBMSRepresentation.width_graph_l hL b w).mp hb
  have hk₀ := (PowerlessArithmeticOrder.lt_l hℳ hω (he := he) (h₀ := h₀) (F := F) k n).mpr hk
  have ht₀ := (PowerlessArithmeticOrder.lt_l hℳ hω (he := he) (h₀ := h₀) (F := F) t w).mpr ht
  have hv₀ := (application_graph_l hC _ v).mp hv
  have hy₀ := (application_graph_l hR _ y).mp hy
  have h := SecondOrderProgramCopiesBlockParentAncestor.reloc_ge_rows_l
    h𝒩 hR hC hO hL hE hJ hP hM hb₀ hk₀ hv₀ hy₀ r
  exact (PowerlessBMSAncestor.graph_l hM _ _ _ _).trans
    ((SecondOrderProgramCopiesBlockParentAncestor.ancestor_sync_l
      h𝒩 hR hC hO hL hE hJ hP hM hb₀ hk₀ hv₀ hy₀ ht₀ h i).trans
      (PowerlessBMSAncestor.graph_l hM _ _ _ _).symm)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSCopyAncestor
