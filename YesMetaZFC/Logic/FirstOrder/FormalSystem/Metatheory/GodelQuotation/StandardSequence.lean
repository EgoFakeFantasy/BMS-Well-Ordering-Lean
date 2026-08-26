import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.OperatorReadability
/-!
# 标准有限序列的语法实现
本层只把 Lean 列表实现为对象集合论中的有限函数图。它位于通用 quotation 之前，
使任意可编号单排序签名的函数参数列和谓词参数列都能复用同一实现。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.GodelQuotation
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
/-- 从给定自然数位置开始，把列表实现为有限函数图。 -/
def standard_sequence_from : Nat → List SetTerm → SetTerm
  | _, [] => ∅ₘ
  | index, element :: rest =>
      {⟨numₘ(index), element⟩ₘ}ₘ ∪ₘ
        standard_sequence_from (index + 1) rest
/-- 标准列表从指标 `0` 开始的对象有限序列实现。 -/
abbrev standard_sequence (elements : List SetTerm) : SetTerm :=
  standard_sequence_from 0 elements
/-- 元素项均 admissible 时，标准有限函数图也是 admissible 对象项。 -/
theorem seq_admissible_m (start : Nat) {elements : List SetTerm} (hElements : ∀ element, element ∈ elements →
      Term.Admissible element SetSort.set) :
    Term.Admissible (standard_sequence_from start elements) SetSort.set := by
  induction elements generalizing start with
  | nil =>
      exact empty_set_term_admissible
  | cons head tail ih =>
      exact binary_union_term_admissible ({⟨numₘ(start), head⟩ₘ}ₘ) (standard_sequence_from (start + 1) tail) (singleton_term_admissible (⟨numₘ(start), head⟩ₘ)
          (ordered_pair_term_admissible (numₘ(start)) head (finite_numeral_term_admissible start) (hElements head (by simp))))
        (ih (start + 1) (fun element hElement =>
          hElements element (by simp [hElement])))
/-- closed 元素组成的标准有限序列仍然 closed。 -/
theorem seq_support_nil_m (start : Nat) {elements : List SetTerm} (hElements : ∀ element, element ∈ elements →
      Term.freeSupport element = []) :
    Term.freeSupport (standard_sequence_from start elements) = [] := by
  induction elements generalizing start with
  | nil =>
      rfl
  | cons head tail ih =>
      have hHead := hElements head (by simp)
      have hTail : ∀ element, element ∈ tail →
          Term.freeSupport element = [] := by
        intro element hElement
        exact hElements element (by simp [hElement])
      simp [standard_sequence_from, Term.freeSupport,
        Term.freeSupportList, finite_numeral_term_freeSupport,
        hHead, ih (start + 1) hTail]
end YesMetaZFC.Logic.FirstOrder.FormalSystem.GodelQuotation
