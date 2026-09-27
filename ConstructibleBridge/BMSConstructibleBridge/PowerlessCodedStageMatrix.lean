import BMSConstructibleBridge.PowerlessCodedStageTheory
import BMSConstructibleBridge.PowerlessCodedStageEntry
import BMSConstructibleBridge.PowerlessCodedStageSource
import BMSConstructibleBridge.PowerlessCodedStageAbsoluteness
import BMSConstructibleBridge.PowerlessSourceGraphAbsolute
import BMSConstructibleBridge.PowerlessStageOrdinal
import BMSConstructibleBridge.PowerlessFiniteStageSystem
import BMSConstructibleBridge.PowerlessDiagramFamily

/-!
# 编码条目在反射端点高处层中的共同见证

§16 条目 4 的收口半：把固定的九槽编码式接成 `DiagramFamily` 的矩阵条目，
并证明反射端点给出的高处层实际携带该条目的共同见证函数图。
小层只需满足有限支持基，正是端点携带的强度，不要求完整集合论。
两个共同见证绑定槽不被条目读取，条目只经自由槽取层参数、两个码与标签。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCodedStageMatrix

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure
open PowerlessCodedStageTheory

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {U δ : carrier_l ℳ}
  {hU₀ : ∃ x, ThirdOrderSemantics.member_l ℳ x U} (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val)
  (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
  (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
  (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val δ U)
  (hδ : PowerlessStagePair.limit_l δ)
  (hωδ : ThirdOrderSemantics.member_l ℳ ω.val δ)

/-- 矩阵条目额外的两个共同见证绑定槽，其下是九个自由参数槽。 -/
abbrev witness_m : SortContext ℒ := .set :: .set :: []

abbrev params_m : SortContext ℒ := PowerlessCodedStageEntry.context_m

/-- 绑定两槽后自由槽索引不变，故九份选择器与扩充前逐字同形。 -/
def w₀ : Term ℒ witness_m params_m .set := .fvar .here

def w₁ : Term ℒ witness_m params_m .set := .fvar (.there .here)

def w₂ : Term ℒ witness_m params_m .set := .fvar (.there (.there .here))

def w₃ : Term ℒ witness_m params_m .set := .fvar (.there (.there (.there .here)))

def w₄ : Term ℒ witness_m params_m .set := .fvar (.there (.there (.there (.there .here))))

def w₅ : Term ℒ witness_m params_m .set :=
  .fvar (.there (.there (.there (.there (.there .here)))))

def w₆ : Term ℒ witness_m params_m .set :=
  .fvar (.there (.there (.there (.there (.there (.there .here))))))

def w₇ : Term ℒ witness_m params_m .set :=
  .fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))

def w₈ : Term ℒ witness_m params_m .set :=
  .fvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))

/-- 矩阵条目：固定编码式只读九个自由槽。 -/
def entry_m : Formula ℒ witness_m params_m :=
  holds_m w₈ w₇ w₆ w₅ w₄ w₃ w₂ w₁ w₀

include hℳ hω ht hT hU hδ hωδ

/-- §16 条目 4 的收口：高处层 U 以 δ 为标签并满足有限支持基时，对任意属于 δ 的标签
及其满足同一支持基的层，U 内实际存在两个内部自然数码与一个共同见证函数图，
使矩阵存在式 `realize_m [entry_m] length_slot` 在 U 中成立；该共同见证即该标签层的赋值图。 -/
theorem matrix_witness_l (k : Nat)
    (h𝒰 : Theory.Models (structure_l U hU₀)
      (Theory.ofList (PowerlessStabilitySupport.basis_m k)))
    {α : type_l U} (hα : ThirdOrderSemantics.member_l ℳ α.val δ)
    {A S F : carrier_l ℳ} (hA₀ : ∃ x, ThirdOrderSemantics.member_l ℳ x A)
    (hA : PowerlessStageEvaluation.system_l ω.val e.val T.val t₁.val t₂.val t₃.val α.val A S F)
    (h𝒜 : Theory.Models (structure_l A hA₀)
      (Theory.ofList (PowerlessStabilitySupport.basis_m k))) :
    ∃ c N : type_l U, member_l ℳ c.val ω.val ∧ member_l ℳ N.val ω.val ∧
      (PowerlessDiagramFamily.realize_m [entry_m] PowerlessCodedStageEntry.length_slot).satisfies
        (PowerlessCodedStageEntry.env_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ c N α) := by
  obtain ⟨c, N, hc, hN, hcode⟩ :=
    PowerlessCodedStageTheory.code_l hℳ hω ht hT (PowerlessStabilitySupport.basis_m k)
  have h : holds_l ω.val e.val T.val t₁.val t₂.val t₃.val c N α.val := (hcode hA₀ hA).mpr h𝒜
  have hcase : holds_l ω.val e.val T.val t₁.val t₂.val t₃.val c N α.val := h
  obtain ⟨a, _, _, hsys, ⟨g, hg, _⟩⟩ := hcase
  have h𝒩 := PowerlessStabilitySupport.hierarchy_l h𝒰
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  have hδU := PowerlessStageOrdinal.subset_l hℳ hω ht hT hU
  have hcU : member_l ℳ c U := hδU c (PowerlessOrdinal.transitive_l hδ.1 ω.val c hωδ hc)
  have hNU : member_l ℳ N U := hδU N (PowerlessOrdinal.transitive_l hδ.1 ω.val N hωδ hN)
  have hASF := PowerlessFiniteStageSystem.member_l hℳ hω ht hT hU hδ h𝒩 hωδ hα hsys
  have hgU := PowerlessCodedStageAbsoluteness.graph_member_l hℳ hω ht hT hU hδ hωδ hN hASF.1 hg
  set η : Env (structure_l U hU₀) [] params_m :=
    PowerlessCodedStageEntry.env_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ ⟨c, hcU⟩ ⟨N, hNU⟩ α
  set η' : Env (structure_l U hU₀) witness_m params_m :=
    (η.pushBound ⟨g, hgU⟩).pushBound ⟨a, hASF.1⟩
  have hsat : entry_m.satisfies η' :=
    (PowerlessCodedStageSource.holds_source_l hℳ hω ht hT hU hδ h𝒩 hωδ η'
      w₈ w₇ w₆ w₅ w₄ w₃ w₂ w₁ w₀ rfl rfl rfl rfl rfl rfl hN hα).mpr h
  refine ⟨⟨c, hcU⟩, ⟨N, hNU⟩, hc, hN,
    (PowerlessDiagramFamily.realize_formula_l [entry_m]
      PowerlessCodedStageEntry.length_slot η).mpr ?_⟩
  refine ⟨⟨g, hgU⟩, ⟨a, hASF.1⟩, (PowerlessSourceGraphAbsolute.map_l hUT).mpr hg, ?_⟩
  intro φ hφ
  have hφ' : φ = entry_m := List.mem_singleton.mp hφ
  subst hφ'
  exact hsat

#print axioms matrix_witness_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCodedStageMatrix
