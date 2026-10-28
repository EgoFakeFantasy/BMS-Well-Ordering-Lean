import BMSConstructibleBridge.PowerlessBMSRepresentationFormula
import BMSConstructibleBridge.PowerlessRestriction

/-!
# 固定原数组上的前缀标签表示

域长只指定已经标号的列，不断言它等于数组的完整宽度。这样可以在同一个最终展开上
逐次增长标签域，最后再用实际宽度封口。边约束仍调用原祖先程序，内部列不作外部递推。
给出与四项语义条件完全一致的纯公式，供后续模型内部归纳使用。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSPrefixRepresentation

open Logic FirstOrder ThirdOrderSemantics
open PowerlessBMSRepresentationSyntax
open PowerlessBMSRepresentationFormula (rows_m rows_formula_l)
open PowerlessRelabelLevels (level_m)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessArithmetic.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  {ω e : carrier_l ℳ} {he : PowerlessNatural.zero_l e} {h₀ : member_l ℳ e ω}
  {F : PowerlessArithmetic.operations_l ω e}

structure representation_l (T t₁ t₂ t₃ c N : carrier_l ℳ) (H : Nat)
    (x q : PowerlessArithmetic.num_l ω) (β f : carrier_l ℳ) : Prop where
  map_l : ThirdOrderSemantics.map_l f q.val β
  labels_l : ∀ i a, value_l f i a → PowerlessCodedDiagram.good_l ω e T t₁ t₂ t₃ c N a
  order_l : PowerlessConcatenation.increasing_l f
  edge_l : ∀ j, j < H → PowerlessBMSRepresentationRows.row_l (he := he) (h₀ := h₀) (F := F)
    j (level_m (H + 1) j) T t₁ t₂ t₃ f x

def representation_m {Γ Δ : SortContext ℒ} (H : Nat)
    (ω e T t₁ t₂ t₃ c N x q β f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (SecondOrderObjectSyntax.map_m f q β)
    (.conj (labels_m ω e T t₁ t₂ t₃ c N f)
      (.conj (order_m f) (rows_m (level_m (H + 1)) ω e T t₁ t₂ t₃ x f H)))

theorem formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (H : Nat)
    (w z T t₁ t₂ t₃ c N a b β f : Term ℒ Γ Δ .set) (x q : PowerlessArithmetic.num_l ω)
    (hw : w.eval η = ω) (hz : z.eval η = e) (ha : a.eval η = x.val) (hb : b.eval η = q.val) :
    (representation_m H w z T t₁ t₂ t₃ c N a b β f).satisfies η ↔
      representation_l (he := he) (h₀ := h₀) (F := F)
        (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (c.eval η) (N.eval η) H x q (β.eval η) (f.eval η) := by
  simp only [representation_m, Formula.satisfies, map_formula_l,
    labels_formula_l hℳ, order_formula_l,
    rows_formula_l hℳ hω (he := he) (h₀ := h₀) (F := F) η _ H w z T t₁ t₂ t₃ a f x hw hz ha,
    hw, hz, hb]
  exact ⟨fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃, h₄⟩,
    fun h => ⟨h.map_l, h.labels_l, h.order_l, h.edge_l⟩⟩

variable {T t₁ t₂ t₃ c N β f : carrier_l ℳ} {H : Nat}
  {x y p q : PowerlessArithmetic.num_l ω}

theorem of_full_l
    (h : PowerlessBMSRepresentation.representation_l (he := he) (h₀ := h₀) (F := F)
      T t₁ t₂ t₃ c N H x q β f) :
    representation_l (he := he) (h₀ := h₀) (F := F) T t₁ t₂ t₃ c N H x q β f :=
  ⟨h.map_l, h.labels_l, h.order_l, h.edge_l⟩

/-- 域已达到实际数组宽度时，前缀表示就是完整表示。 -/
theorem complete_l
    (h : representation_l (he := he) (h₀ := h₀) (F := F) T t₁ t₂ t₃ c N H x q β f)
    (hx : PowerlessBMSRepresentation.width_l (he := he) (h₀ := h₀) (F := F) x q) :
    PowerlessBMSRepresentation.representation_l (he := he) (h₀ := h₀) (F := F)
      T t₁ t₂ t₃ c N H x q β f :=
  ⟨hx, h.map_l, h.labels_l, h.order_l, h.edge_l⟩

/-- 实际限制标签图；返回精确值图，且保留所有已标号祖先边。 -/
theorem restrict_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (h : representation_l (he := he) (h₀ := h₀) (F := F) T t₁ t₂ t₃ c N H x q β f)
    (hp : subset_l p.val q.val) :
    ∃ g, representation_l (he := he) (h₀ := h₀) (F := F) T t₁ t₂ t₃ c N H x p β g ∧
      ∀ i a, value_l g i a ↔ member_l ℳ i p.val ∧ value_l f i a := by
  obtain ⟨g, hg, hV⟩ := PowerlessRestriction.exists_l hℳ h.map_l hp
  refine ⟨g, ⟨hg, ?_, ?_, ?_⟩, hV⟩
  · exact fun i a ha => h.labels_l i a ((hV i a).mp ha).2
  · exact fun i t a b hit ha hb => h.order_l i t a b hit
      ((hV i a).mp ha).2 ((hV t b).mp hb).2
  · exact fun j hj r hr i t hit a b ha hb => h.edge_l j hj r hr i t hit a b
      ((hV i.val a).mp ha).2 ((hV t.val b).mp hb).2

/-- 只需比较已标号域上的真实祖先边；未标号后缀不增加前提。 -/
theorem transfer_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (h : representation_l (he := he) (h₀ := h₀) (F := F) T t₁ t₂ t₃ c N H x q β f)
    (hancestor : ∀ r i t : PowerlessArithmetic.num_l ω,
      member_l ℳ i.val q.val → member_l ℳ t.val q.val →
      PowerlessBMSAncestor.ancestor_l (he := he) (h₀ := h₀) (F := F) y r t i →
      PowerlessBMSAncestor.ancestor_l (he := he) (h₀ := h₀) (F := F) x r t i) :
    representation_l (he := he) (h₀ := h₀) (F := F) T t₁ t₂ t₃ c N H y q β f := by
  refine ⟨h.map_l, h.labels_l, h.order_l, ?_⟩
  intro j hj r hr i t hit a b ha hb
  exact h.edge_l j hj r hr i t (hancestor r i t
    (PowerlessFunction.value_mem_l hℳ h.map_l ha).1
    (PowerlessFunction.value_mem_l hℳ h.map_l hb).1 hit) a b ha hb

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSPrefixRepresentation
