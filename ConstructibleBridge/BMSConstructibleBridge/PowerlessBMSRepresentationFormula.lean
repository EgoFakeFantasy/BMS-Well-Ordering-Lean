import BMSConstructibleBridge.PowerlessBMSRepresentationRows

/-!
# 原 BMS 标签表示的完整纯公式

有限行合取先对任意层号函数证明语义，随后才代入实际重标号预算。
全部宽度、映射、好标签、顺序和祖先边约束与原 representation_l 逐项一致。
这里没有把表示存在性、展开保持或最终良序性加入公式的前提。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSRepresentationFormula

open Logic FirstOrder ThirdOrderSemantics
open PowerlessBMSRepresentationSyntax PowerlessBMSRepresentationRows

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessArithmetic.structure_l

universe u

def rows_m {Γ Δ : SortContext ℒ} (k : Nat → Nat) (ω e T t₁ t₂ t₃ x f : Term ℒ Γ Δ .set) :
    Nat → Formula ℒ Γ Δ
  | 0 => .truth
  | H + 1 => .conj (rows_m k ω e T t₁ t₂ t₃ x f H) (row_m H (k H) ω e T t₁ t₂ t₃ x f)

def representation_m {Γ Δ : SortContext ℒ} (H : Nat)
    (ω e T t₁ t₂ t₃ c N x q β f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (width_m ω e x q)
    (.conj (SecondOrderObjectSyntax.map_m f q β)
      (.conj (labels_m ω e T t₁ t₂ t₃ c N f)
        (.conj (order_m f) (rows_m (PowerlessRelabelLevels.level_m (H + 1)) ω e T t₁ t₂ t₃ x f H))))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  {ω e : carrier_l ℳ} {he : PowerlessNatural.zero_l e} {h₀ : member_l ℳ e ω}
  {F : PowerlessArithmetic.operations_l ω e}

theorem rows_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (k : Nat → Nat) (H : Nat)
    (w z T t₁ t₂ t₃ y f : Term ℒ Γ Δ .set) (x : PowerlessArithmetic.num_l ω)
    (hw : w.eval η = ω) (hz : z.eval η = e) (hy : y.eval η = x.val) :
    (rows_m k w z T t₁ t₂ t₃ y f H).satisfies η ↔
      ∀ j, j < H → row_l (he := he) (h₀ := h₀) (F := F) j (k j)
        (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (f.eval η) x := by
  induction H with
  | zero => simp only [rows_m, Formula.satisfies, Nat.not_lt_zero, IsEmpty.forall_iff, implies_true]
  | succ H ih =>
    rw [rows_m, Formula.satisfies, ih, row_formula_l hℳ hω η H (k H) w z T t₁ t₂ t₃ y f x hw hz hy]
    constructor
    · rintro ⟨h, h₁⟩ j hj
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
      · exact h j hj
      · exact h₁
    · intro h
      exact ⟨fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self H)), h H (Nat.lt_succ_self H)⟩

theorem formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (H : Nat)
    (w z T t₁ t₂ t₃ c N a b β f : Term ℒ Γ Δ .set) (x q : PowerlessArithmetic.num_l ω)
    (hw : w.eval η = ω) (hz : z.eval η = e) (ha : a.eval η = x.val) (hb : b.eval η = q.val) :
    (representation_m H w z T t₁ t₂ t₃ c N a b β f).satisfies η ↔
      PowerlessBMSRepresentation.representation_l (he := he) (h₀ := h₀) (F := F)
        (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (c.eval η) (N.eval η) H x q (β.eval η) (f.eval η) := by
  simp only [representation_m, Formula.satisfies,
    width_formula_l hℳ hω (he := he) (h₀ := h₀) (F := F) η w z a b x q hw hz ha hb, map_formula_l,
    labels_formula_l hℳ, order_formula_l,
    rows_formula_l hℳ hω (he := he) (h₀ := h₀) (F := F) η _ H w z T t₁ t₂ t₃ a f x hw hz ha,
    hw, hz, hb]
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄, h₅⟩
    exact ⟨h₁, h₂, h₃, h₄, h₅⟩
  · intro h
    exact ⟨h.width_l, h.map_l, h.labels_l, h.order_l, h.edge_l⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSRepresentationFormula
