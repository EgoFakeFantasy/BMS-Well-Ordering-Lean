import BMSConstructibleBridge.GraphNaturals
import BMSConstructibleBridge.GraphClosure

/-!
# 图码解释域中的有序对与函数图

实际构造 Kuratowski 有序对并证明其坐标单射性。给定一张数指标值表后，
其有序对图是解释域中的一个对象，且在任意等价输出码上满足精确函数规格。
以此将节点坍缩函数编码到解释域内部；仍未完成对象二阶公式及推导翻译。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.GraphFunctions

set_option autoImplicit false

open CountableGraph GraphNaturals GraphClosure

private theorem pair_left (A B : code_l) : mem_l A (pair_l A B) :=
  (pair_mem_l A B A).mpr (Or.inl (refl_l A))

private theorem pair_right (A B : code_l) : mem_l B (pair_l A B) :=
  (pair_mem_l A B B).mpr (Or.inr (refl_l B))

theorem pair_congr_l {A B C D : code_l} (h : eq_l A C) (h₁ : eq_l B D) :
    eq_l (pair_l A B) (pair_l C D) := by
  apply (ext_l _ _).mpr
  intro X
  rw [pair_mem_l, pair_mem_l]
  exact or_congr ⟨fun h₂ => trans_l h₂ h, fun h₂ => trans_l h₂ (symm_l h)⟩
    ⟨fun h₂ => trans_l h₂ h₁, fun h₂ => trans_l h₂ (symm_l h₁)⟩

/-- 无序对固定一个参数后可消去该参数，包含退化为单点集的情形。 -/
theorem pair_cancel_l (A B C : code_l) (h : eq_l (pair_l A B) (pair_l A C)) :
    eq_l B C := by
  have h₁ := (pair_mem_l A C B).mp
    ((mem_congr_l (refl_l B) h).mp (pair_right A B))
  rcases h₁ with h₁ | h₁
  · have h₂ := (pair_mem_l A B C).mp
      ((mem_congr_l (refl_l C) h).mpr (pair_right A C))
    rcases h₂ with h₂ | h₂
    · exact trans_l h₁ (symm_l h₂)
    · exact symm_l h₂
  · exact h₁

/-- Kuratowski 有序对使用已经核验的无序对构造。 -/
def ordered_l (A B : code_l) : code_l := pair_l (pair_l A A) (pair_l A B)

theorem ordered_congr_l {A B C D : code_l} (h : eq_l A C) (h₁ : eq_l B D) :
    eq_l (ordered_l A B) (ordered_l C D) :=
  pair_congr_l (pair_congr_l h h) (pair_congr_l h h₁)

/-- 实际有序对的两个坐标都能从对象相等恢复，不假定图码字面单射。 -/
theorem ordered_eq_l (A B C D : code_l) : eq_l (ordered_l A B) (ordered_l C D) ↔
    eq_l A C ∧ eq_l B D := by
  constructor
  · intro h
    have h₁ := (pair_mem_l (pair_l C C) (pair_l C D) (pair_l A A)).mp
      ((mem_congr_l (refl_l (pair_l A A)) h).mp (pair_left (pair_l A A) (pair_l A B)))
    have h₂ : eq_l A C := by
      have h₃ : mem_l C (pair_l A A) := by
        rcases h₁ with h₁ | h₁
        · exact (mem_congr_l (refl_l C) h₁).mpr (pair_left C C)
        · exact (mem_congr_l (refl_l C) h₁).mpr (pair_left C D)
      exact symm_l (((pair_mem_l A A C).mp h₃).elim id id)
    have h₃ : eq_l (ordered_l C B) (ordered_l C D) :=
      trans_l (ordered_congr_l (symm_l h₂) (refl_l B)) h
    exact ⟨h₂, pair_cancel_l C B D
      (pair_cancel_l (pair_l C C) (pair_l C B) (pair_l C D) h₃)⟩
  · rintro ⟨h, h₁⟩
    exact ordered_congr_l h h₁

/-- 一张已经给出的值表在数域 P 上的内部函数图。 -/
def map_l (P : Nat → Prop) (f : Nat → code_l) : code_l :=
  family_l (fun n => ordered_l (nat_l n) (f n)) P

theorem map_mem_l (P : Nat → Prop) (f : Nat → code_l) (A : code_l) :
    mem_l A (map_l P f) ↔ ∃ n, P n ∧ eq_l A (ordered_l (nat_l n) (f n)) :=
  family_mem_l _ P A

/-- 任意输入和输出码的图规格，排除并非指定数域元素的输入。 -/
theorem map_graph_l (P : Nat → Prop) (f : Nat → code_l) (A B : code_l) :
    mem_l (ordered_l A B) (map_l P f) ↔
      ∃ n, P n ∧ eq_l A (nat_l n) ∧ eq_l B (f n) := by
  simp only [map_mem_l, ordered_eq_l]

/-- 全部输出码上的函数图规格，同时检查定义域，不能只验证选定输出。 -/
theorem map_apply_l (P : Nat → Prop) (f : Nat → code_l) (n : Nat) (A : code_l) :
    mem_l (ordered_l (nat_l n) A) (map_l P f) ↔ P n ∧ eq_l A (f n) := by
  rw [map_mem_l]
  constructor
  · rintro ⟨m, h, h₁⟩
    obtain ⟨h₁, h₂⟩ := (ordered_eq_l _ _ _ _).mp h₁
    obtain rfl := (nat_eq_l n m).mp h₁
    exact ⟨h, h₂⟩
  · rintro ⟨h, h₁⟩
    exact ⟨n, h, ordered_congr_l (refl_l _) h₁⟩

/-- 两个被同一个输入指向的输出必定是同一解释对象。 -/
theorem map_unique_l (P : Nat → Prop) (f : Nat → code_l) (A B C : code_l)
    (h : mem_l (ordered_l A B) (map_l P f))
    (h₁ : mem_l (ordered_l A C) (map_l P f)) : eq_l B C := by
  obtain ⟨n, _, h₂, h₃⟩ := (map_graph_l P f A B).mp h
  obtain ⟨m, _, h₄, h₅⟩ := (map_graph_l P f A C).mp h₁
  obtain rfl := (nat_eq_l n m).mp (trans_l (symm_l h₂) h₄)
  exact trans_l h₃ (symm_l h₅)

/-- 坍缩映射的内部图对象，不再只是从数到图码的宿主函数。 -/
def collapse_map_l (R : Nat → Nat → Prop) (h : WellFounded R) : code_l :=
  map_l (field_l R) (point_l R h)

theorem collapse_apply_l (R : Nat → Nat → Prop) (h : WellFounded R) (n : Nat) (A : code_l) :
    mem_l (ordered_l (nat_l n) A) (collapse_map_l R h) ↔
      field_l R n ∧ eq_l A (point_l R h n) := map_apply_l _ _ n A

/-- 内部函数图的值域恰为此前构造的传递坍缩像。 -/
theorem collapse_range_l (R : Nat → Nat → Prop) (h : WellFounded R) (A : code_l) :
    mem_l A (collapse_l R h) ↔
      ∃ n, mem_l (ordered_l (nat_l n) A) (collapse_map_l R h) := by
  simp only [collapse_mem_l, collapse_apply_l]

end YesMetaZFC.BMS.ConstructibleBridge.GraphFunctions
