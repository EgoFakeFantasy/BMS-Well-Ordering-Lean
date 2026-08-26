import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FiniteSequenceSemantics.FamilyDomainElimination

/-!
# 有限序列族的宿主 token 分片

本模块把对象层消去所得长度列表解释为宿主 token 串的连续分片。定义按长度表递归
消费输入，因此分片扁平化、逐下标切片和长度证书都保持可计算。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace GodelQuotation

set_option autoImplicit false

universe u

/-- 按长度表从左到右连续切分输入；超出输入的尾段由 `take` 自然截断。 -/
def finite_family_slices {α : Type u} :
    List Nat → List α → List (List α)
  | .nil, _ => []
  | .cons length lengths, elements =>
      elements.take length ::
        finite_family_slices lengths
          (elements.drop length)

@[simp]
theorem finite_family_slices_length
    {α : Type u}
    (lengths : List Nat) (elements : List α) :
    (finite_family_slices lengths elements).length =
      lengths.length := by
  induction lengths generalizing elements with
  | nil =>
      rfl
  | cons length lengths ih =>
      simp [finite_family_slices, ih]

/-- 所有分片重新扁平化后，恰为输入的长度表总和前缀。 -/
theorem finite_family_slices_flatten
    {α : Type u}
    (lengths : List Nat) (elements : List α) :
    (finite_family_slices lengths elements).flatten =
      elements.take lengths.sum := by
  induction lengths generalizing elements with
  | nil =>
      simp [finite_family_slices]
  | cons length lengths ih =>
      simp only [finite_family_slices,
        List.flatten_cons, List.sum_cons, ih]
      exact (List.take_add (l := elements)
        (i := length) (j := lengths.sum)).symm

/-- 长度表总和覆盖完整输入时，所有分片重新扁平化为原输入。 -/
theorem finite_family_slices_flatten_eq_self
    {α : Type u}
    (lengths : List Nat) (elements : List α)
    (hLength : lengths.sum = elements.length) :
    (finite_family_slices lengths elements).flatten =
      elements := by
  rw [finite_family_slices_flatten, hLength,
    List.take_length]

/-- 第 `index` 个递归分片就是由全局前缀和定位的标准切片。 -/
theorem finite_family_slices_getElem?
    {α : Type u}
    (lengths : List Nat) (elements : List α)
    (index : Nat) (hIndex : index < lengths.length) :
    (finite_family_slices lengths elements)[index]? =
      some
        ((elements.drop
            (finite_family_prefix_length
              lengths index)).take
          (finite_family_piece_length
            lengths index)) := by
  induction lengths generalizing elements index with
  | nil =>
      simp at hIndex
  | cons length lengths ih =>
      cases index with
      | zero =>
          simp [finite_family_slices]
      | succ index =>
          have hTail :
              index < lengths.length := by
            simpa using hIndex
          rw [show
            (finite_family_slices
              (length :: lengths) elements)[index + 1]? =
                (finite_family_slices
                  lengths (elements.drop length))[index]? by
              rfl]
          rw [ih (elements := elements.drop length)
            index hTail]
          simp only [
            finite_family_prefix_length_cons_succ,
            finite_family_piece_length_cons_succ]
          rw [List.drop_drop]

/-- 完整覆盖输入时，每个有效标准分片都具有长度表指定的精确长度。 -/
theorem finite_family_standard_slice_length
    {α : Type u}
    (lengths : List Nat) (elements : List α)
    (index : Nat) (hIndex : index < lengths.length)
    (hLength : lengths.sum = elements.length) :
    ((elements.drop
        (finite_family_prefix_length
          lengths index)).take
      (finite_family_piece_length
        lengths index)).length =
      finite_family_piece_length lengths index := by
  have hBound :
      finite_family_prefix_length lengths index +
          finite_family_piece_length lengths index ≤
        elements.length := by
    rw [← hLength]
    exact finite_family_prefix_add_piece_le_sum
      lengths index hIndex
  simp only [List.length_take, List.length_drop]
  apply Nat.min_eq_left
  omega

/-- 由 `getElem?` 取出的递归分片具有长度表指定的精确长度。 -/
theorem finite_family_slice_length_of_getElem?
    {α : Type u}
    (lengths : List Nat) (elements piece : List α)
    (index : Nat) (hIndex : index < lengths.length)
    (hLength : lengths.sum = elements.length)
    (hPiece :
      (finite_family_slices
        lengths elements)[index]? =
          some piece) :
    piece.length =
      finite_family_piece_length lengths index := by
  have hCanonical :=
    finite_family_slices_getElem?
      lengths elements index hIndex
  rw [hPiece] at hCanonical
  have hEquality := Option.some.inj hCanonical.symm
  subst piece
  exact finite_family_standard_slice_length
    lengths elements index hIndex hLength

/-- 任一递归分片中的元素仍来自原输入。 -/
theorem finite_family_slice_mem_source
    {α : Type u}
    (lengths : List Nat) (elements piece : List α)
    (hPiece :
      piece ∈ finite_family_slices
        lengths elements)
    {element : α} (hElement : element ∈ piece) :
    element ∈ elements := by
  induction lengths generalizing elements with
  | nil =>
      simp [finite_family_slices] at hPiece
  | cons length lengths ih =>
      simp only [finite_family_slices,
        List.mem_cons] at hPiece
      rcases hPiece with rfl | hPiece
      · exact List.mem_of_mem_take hElement
      · exact List.mem_of_mem_drop <|
          ih (elements := elements.drop length)
            hPiece

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
