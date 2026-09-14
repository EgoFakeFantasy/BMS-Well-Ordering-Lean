import BMSConstructibleBridge.GraphFunctions

/-!
# 每个图码对象到 omega 的内部单射

先在自然数枚举中保留每个双模拟类的最小指标，再反转其有序对图。所得图
本身是解释域中的对象；逐码证明定义域、输出属于 omega、全域性、函数性和
单射性。不把宿主的满射枚举直接冒充内部 Countability。

自然数最小指标的论证仍在宿主层。公式化及对象二阶算术推导须另行实现。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.GraphCountability

set_option autoImplicit false

open CountableGraph GraphNaturals GraphFunctions

/-- 同一个对象只保留其枚举中的第一个表示。 -/
def first_l (f : Nat → code_l) (n : Nat) : Prop :=
  ∀ m, m < n → ¬eq_l (f m) (f n)

theorem first_eq_l (f : Nat → code_l) {n m : Nat} (h : first_l f n)
    (h₁ : first_l f m) (h₂ : eq_l (f n) (f m)) : n = m := by
  rcases Nat.lt_trichotomy n m with h₃ | rfl | h₃
  · exact False.elim (h₁ n h₃ h₂)
  · rfl
  · exact False.elim (h m h₃ (symm_l h₂))

/-- 每个已枚举对象有自然数最小代表，不需要选择一族实数见证。 -/
theorem first_exists_l (f : Nat → code_l) (n : Nat) :
    ∃ m, first_l f m ∧ eq_l (f n) (f m) := by
  classical
  have h : ∃ m, eq_l (f n) (f m) := ⟨n, refl_l _⟩
  refine ⟨Nat.find h, ?_, Nat.find_spec h⟩
  intro m h₁ h₂
  exact Nat.find_min h h₁ (trans_l (Nat.find_spec h) (symm_l h₂))

/-- 去重后枚举的反向有序对图。 -/
def inverse_l (f : Nat → code_l) : code_l :=
  family_l (fun n => ordered_l (f n) (nat_l n)) (first_l f)

theorem inverse_graph_l (f : Nat → code_l) (A B : code_l) :
    mem_l (ordered_l A B) (inverse_l f) ↔
      ∃ n, first_l f n ∧ eq_l A (f n) ∧ eq_l B (nat_l n) := by
  simp only [inverse_l, family_mem_l, ordered_eq_l]

theorem inverse_unique_l (f : Nat → code_l) (A B C : code_l)
    (h : mem_l (ordered_l A B) (inverse_l f))
    (h₁ : mem_l (ordered_l A C) (inverse_l f)) : eq_l B C := by
  obtain ⟨n, h₂, h₃, h₄⟩ := (inverse_graph_l f A B).mp h
  obtain ⟨m, h₅, h₆, h₇⟩ := (inverse_graph_l f A C).mp h₁
  obtain rfl := first_eq_l f h₂ h₅ (trans_l (symm_l h₃) h₆)
  exact trans_l h₄ (symm_l h₇)

theorem inverse_inj_l (f : Nat → code_l) (A B C : code_l)
    (h : mem_l (ordered_l A C) (inverse_l f))
    (h₁ : mem_l (ordered_l B C) (inverse_l f)) : eq_l A B := by
  obtain ⟨n, _, h₂, h₃⟩ := (inverse_graph_l f A C).mp h
  obtain ⟨m, _, h₄, h₅⟩ := (inverse_graph_l f B C).mp h₁
  obtain rfl := (nat_eq_l n m).mp (trans_l (symm_l h₃) h₅)
  exact trans_l h₂ (symm_l h₄)

/-- 内部图 F 表示 A 到 B 的单射：所有图元素均为有序对，且严格核验域、值及唯一性。 -/
def injection_l (F A B : code_l) : Prop :=
  (∀ X, mem_l X F → ∃ C D, eq_l X (ordered_l C D)) ∧
  (∀ C D, mem_l (ordered_l C D) F → mem_l C A ∧ mem_l D B) ∧
  (∀ C, mem_l C A → ∃ D, mem_l (ordered_l C D) F) ∧
  (∀ C D E, mem_l (ordered_l C D) F → mem_l (ordered_l C E) F → eq_l D E) ∧
  (∀ C D E, mem_l (ordered_l C E) F → mem_l (ordered_l D E) F → eq_l C D)

/-- 任意解释对象确有到 omega 的内部单射图；空对象单独处理。 -/
theorem countable_l (A : code_l) : ∃ F, injection_l F A omega_l := by
  classical
  by_cases h : ∃ B, mem_l B A
  · obtain ⟨f, h₁, h₂⟩ := enumerate_l A h
    refine ⟨inverse_l f, ?_, ?_, ?_, inverse_unique_l f, inverse_inj_l f⟩
    · intro X h₃
      obtain ⟨n, _, h₄⟩ := (family_mem_l _ _ X).mp h₃
      exact ⟨f n, nat_l n, h₄⟩
    · intro B C h₃
      obtain ⟨n, _, h₄, h₅⟩ := (inverse_graph_l f B C).mp h₃
      exact ⟨(mem_congr_l h₄ (refl_l A)).mpr (h₁ n), (omega_mem_l C).mpr ⟨n, h₅⟩⟩
    · intro B h₃
      obtain ⟨n, h₄⟩ := h₂ B h₃
      obtain ⟨m, h₅, h₆⟩ := first_exists_l f n
      exact ⟨nat_l m, (inverse_graph_l f B _).mpr ⟨m, h₅, trans_l h₄ h₆, refl_l _⟩⟩
  · refine ⟨empty_l, ?_, ?_, ?_, ?_, ?_⟩
    · intro X h₁; exact False.elim (empty_mem_l X h₁)
    · intro C D h₁; exact False.elim (empty_mem_l _ h₁)
    · intro C h₁; exact False.elim (h ⟨C, h₁⟩)
    · intro C D E h₁ _; exact False.elim (empty_mem_l _ h₁)
    · intro C D E h₁ _; exact False.elim (empty_mem_l _ h₁)

end YesMetaZFC.BMS.ConstructibleBridge.GraphCountability
