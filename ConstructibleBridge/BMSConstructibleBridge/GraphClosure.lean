import BMSConstructibleBridge.CountableGraph

/-!
# 图码域的传递包含与坍缩

传递包含收集一张图中从根可达的自然数节点。坍缩则把给定良基数关系的每个
节点直接作为根，证明坍缩方程及按解释相等的唯一性。这些是实际图构造，不
调用宿主集合论的 Mostowski 坍缩或序数秩。

此处先给出坍缩值的宿主函数，`GraphFunctions` 再将它编码成解释域内部的
有序对集合。将基础公理和良基前提译为对象公式，以及在 `Z₂` 内生成推导，
仍须另行完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.GraphClosure

set_option autoImplicit false

open CountableGraph

/-- 解释成员意义的传递性。 -/
def transitive_l (A : code_l) : Prop :=
  ∀ B C, mem_l B C → mem_l C A → mem_l B A

/-- 从下方节点到上方节点的有限路径，含零步路径。 -/
inductive path_l (R : Nat → Nat → Prop) : Nat → Nat → Prop
  | refl (a : Nat) : path_l R a a
  | step {a b c : Nat} : R a b → path_l R b c → path_l R a c

private theorem path_acc {R : Nat → Nat → Prop} {a b : Nat}
    (h : path_l R a b) (h₁ : Acc R b) : Acc R a := by
  induction h with
  | refl => exact h₁
  | step h _ hᵢ => exact (hᵢ h₁).inv h

/-- 实际收集根及其全部有限后继路径，构造包含原对象的传递集合。 -/
def closure_l (A : code_l) : code_l :=
  collect_l A.rel (fun a => path_l A.rel a A.root) (fun _ h => path_acc h A.wf)

theorem closure_mem_l (A : code_l) : mem_l A (closure_l A) := by
  apply (collect_mem_l _ _ _ A).mpr
  exact ⟨A.root, .refl _, Bisimulation.refl_l A.rel A.root⟩

theorem closure_transitive_l (A : code_l) : transitive_l (closure_l A) := by
  intro B C h h₁
  obtain ⟨a, h₁, h₂⟩ := (collect_mem_l _ _ _ C).mp h₁
  obtain ⟨b, h₃, h₄⟩ := h
  obtain ⟨c, h₅, h₆⟩ := (Bisimulation.witness_eq_l C.rel A.rel h₂).1 h₃
  exact (collect_mem_l _ _ _ B).mpr
    ⟨c, .step h₅ h₁, Bisimulation.trans_l B.rel C.rel A.rel h₄ h₆⟩

/-- 不只包含 A 本身，也包含 A 的全部成员。 -/
theorem closure_subset_l (A B : code_l) (h : mem_l B A) : mem_l B (closure_l A) :=
  closure_transitive_l A B A h (closure_mem_l A)

/-- 数关系的实际定义域和值域之并，保留坍缩公理的原字段范围。 -/
def field_l (R : Nat → Nat → Prop) (a : Nat) : Prop := ∃ b, R a b ∨ R b a

/-- 每个数节点的坍缩值由同一关系及该根构成，不作对象族选择。 -/
def point_l (R : Nat → Nat → Prop) (h : WellFounded R) (a : Nat) : code_l :=
  ⟨R, a, h.apply a⟩

/-- 任意成员码满足完整坍缩方程，包含所有双模拟表示。 -/
theorem point_mem_l (R : Nat → Nat → Prop) (h : WellFounded R) (a : Nat) (A : code_l) :
    mem_l A (point_l R h a) ↔ ∃ b, R b a ∧ eq_l A (point_l R h b) := Iff.rfl

/-- 收集关系字段内的坍缩值；空关系给出空像，而非额外加入空集。 -/
def collapse_l (R : Nat → Nat → Prop) (h : WellFounded R) : code_l :=
  collect_l R (field_l R) (fun a _ => h.apply a)

theorem collapse_mem_l (R : Nat → Nat → Prop) (h : WellFounded R) (A : code_l) :
    mem_l A (collapse_l R h) ↔ ∃ a, field_l R a ∧ eq_l A (point_l R h a) :=
  collect_mem_l R (field_l R) (fun a _ => h.apply a) A

/-- 坍缩像实际传递；不要求源关系外延。 -/
theorem collapse_transitive_l (R : Nat → Nat → Prop) (h : WellFounded R) :
    transitive_l (collapse_l R h) := by
  intro A B h₁ h₂
  obtain ⟨b, _, h₃⟩ := (collapse_mem_l R h B).mp h₂
  obtain ⟨a, h₄, h₅⟩ := h₁
  obtain ⟨c, h₆, h₇⟩ := (Bisimulation.witness_eq_l B.rel R h₃).1 h₄
  exact (collapse_mem_l R h A).mpr
    ⟨c, ⟨b, Or.inl h₆⟩, Bisimulation.trans_l A.rel B.rel R h₅ h₇⟩

/-- 任意另一组满足相同坍缩方程的值，在整个关系字段上逐点相等。 -/
theorem point_unique_l (R : Nat → Nat → Prop) (h : WellFounded R) (f : Nat → code_l)
    (h₁ : ∀ a, field_l R a → ∀ A, mem_l A (f a) ↔ ∃ b, R b a ∧ eq_l A (f b)) :
    ∀ a, field_l R a → eq_l (f a) (point_l R h a) := by
  intro a
  induction a using h.induction with
  | h a hᵢ =>
      intro h₂
      apply (ext_l _ _).mpr
      intro A
      rw [h₁ a h₂ A, point_mem_l]
      constructor
      · rintro ⟨b, h₃, h₄⟩
        exact ⟨b, h₃, trans_l h₄ (hᵢ b h₃ ⟨a, Or.inl h₃⟩)⟩
      · rintro ⟨b, h₃, h₄⟩
        exact ⟨b, h₃, trans_l h₄ (symm_l (hᵢ b h₃ ⟨a, Or.inl h₃⟩))⟩

end YesMetaZFC.BMS.ConstructibleBridge.GraphClosure
