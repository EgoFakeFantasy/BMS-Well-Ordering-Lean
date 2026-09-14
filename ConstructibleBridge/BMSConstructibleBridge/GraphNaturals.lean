import BMSConstructibleBridge.CountableGraph

/-!
# 图码解释中的标准自然数

用自然数严格序的指定根表示冯诺伊曼自然数，并实际构造包含它们的集合码。
逐值核验等词、成员和后继，得到无穷公理的语义实例。只使用自然数归纳，
没有导入宿主序数或可构造宇宙。本文件不声称任意 Henkin 模型的自然数标准，
也尚未给出纯二阶算术中的对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.GraphNaturals

set_option autoImplicit false

open CountableGraph

/-- 第 n 个自然数使用同一严格序关系，以 n 为根。 -/
def nat_l (n : Nat) : code_l := ⟨(· < ·), n, Nat.lt_wfRel.wf.apply n⟩

private theorem le (n : Nat) : ∀ m, Bisimulation.eq_l (· < ·) (· < ·) n m → n ≤ m := by
  induction n with
  | zero => intro m _; exact Nat.zero_le m
  | succ n hᵢ =>
      intro m h
      obtain ⟨k, h₁, h₂⟩ := (Bisimulation.witness_eq_l (· < ·) (· < ·) h).1
        (Nat.lt_succ_self n)
      exact Nat.succ_le_of_lt (lt_of_le_of_lt (hᵢ k h₂) h₁)

/-- 自然数在图码相等下不发生混淆。 -/
theorem nat_eq_l (n m : Nat) : eq_l (nat_l n) (nat_l m) ↔ n = m := by
  constructor
  · intro h
    exact Nat.le_antisymm (le n m h) (le m n (symm_l h))
  · rintro rfl
    exact refl_l _

theorem nat_mem_l (A : code_l) (n : Nat) : mem_l A (nat_l n) ↔
    ∃ m, m < n ∧ eq_l A (nat_l m) := Iff.rfl

/-- 成员关系也精确保留自然数严格序。 -/
theorem nat_lt_l (n m : Nat) : mem_l (nat_l n) (nat_l m) ↔ n < m := by
  rw [nat_mem_l]
  constructor
  · rintro ⟨k, h, h₁⟩
    exact (nat_eq_l n k).mp h₁ ▸ h
  · intro h
    exact ⟨n, h, refl_l _⟩

theorem zero_l : eq_l empty_l (nat_l 0) := by
  apply (ext_l _ _).mpr
  intro A
  constructor
  · intro h
    exact False.elim (empty_mem_l A h)
  · rintro ⟨n, h, _⟩
    exact False.elim (Nat.not_lt_zero n h)

/-- 图码集合后继与自然数后继逐值一致。 -/
theorem succ_l (n : Nat) : eq_l (CountableGraph.succ_l (nat_l n)) (nat_l (n + 1)) := by
  apply (ext_l _ _).mpr
  intro A
  rw [succ_mem_l, nat_mem_l, nat_mem_l]
  constructor
  · rintro (⟨m, h, h₁⟩ | h)
    · exact ⟨m, Nat.lt_trans h (Nat.lt_succ_self n), h₁⟩
    · exact ⟨n, Nat.lt_succ_self n, h⟩
  · rintro ⟨m, h, h₁⟩
    rcases (Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h)) with h | rfl
    · exact Or.inl ⟨m, h, h₁⟩
    · exact Or.inr h₁

/-- 以新根收集所有标准自然数，明确给出一个实数图码。 -/
def omega_l : code_l := collect_l (· < ·) (fun _ => True)
  (fun n _ => Nat.lt_wfRel.wf.apply n)

/-- 此语义域中的 omega 成员恰为标准自然数的任意双模拟表示。 -/
theorem omega_mem_l (A : code_l) : mem_l A omega_l ↔ ∃ n, eq_l A (nat_l n) := by
  rw [omega_l, collect_mem_l]
  constructor
  · rintro ⟨n, _, h⟩
    exact ⟨n, h⟩
  · rintro ⟨n, h⟩
    exact ⟨n, trivial, h⟩

/-- 无穷公理的实际语义见证，而非额外假定的解释域闭包。 -/
theorem infinite_l : mem_l empty_l omega_l ∧
    ∀ A, mem_l A omega_l → mem_l (CountableGraph.succ_l A) omega_l := by
  refine ⟨(omega_mem_l _).mpr ⟨0, zero_l⟩, ?_⟩
  intro A h
  obtain ⟨n, h⟩ := (omega_mem_l A).mp h
  exact (omega_mem_l _).mpr ⟨n + 1, trans_l (succ_congr_l h) (succ_l n)⟩

end YesMetaZFC.BMS.ConstructibleBridge.GraphNaturals
