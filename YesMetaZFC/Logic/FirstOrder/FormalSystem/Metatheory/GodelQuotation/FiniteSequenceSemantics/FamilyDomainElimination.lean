import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.SequenceInversion

/-!
# 有限序列族的定义域长度消去

本模块把一列子序列的严格父域上界统一消去为外部自然数长度列表。每个长度分支
仍保留对应对象定义域等式，供 flatten 切片反演和 checked decoder 递归直接消费。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace GodelQuotation

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/--
从 `start` 开始的一列族元素定义域 numeral 等式上下文。

定义采用尾段在前的顺序，使递归消去时新加入的当前等式与已有局部上下文直接
拼接，不需要兼容层或上下文重排定理。
-/
def finite_family_domain_length_context
    (family : SetTerm) : Nat → List Nat →
      Context signature
  | _, [] => []
  | start, length :: lengths =>
      finite_family_domain_length_context
          family (start + 1) lengths ++
        [domₘ(family ·ₘ numₘ(start)) ≐ₘ
          numₘ(length)]

/-- 长度列表在越界位置取零的总函数视图。 -/
def finite_family_piece_length
    (lengths : List Nat) (index : Nat) : Nat :=
  lengths[index]?.getD 0

@[simp]
theorem finite_family_piece_length_cons_zero
    (length : Nat) (lengths : List Nat) :
    finite_family_piece_length
      (length :: lengths) 0 = length := by
  simp [finite_family_piece_length]

@[simp]
theorem finite_family_piece_length_cons_succ
    (length : Nat) (lengths : List Nat)
    (index : Nat) :
    finite_family_piece_length
      (length :: lengths) (index + 1) =
        finite_family_piece_length lengths index := by
  simp [finite_family_piece_length]

/-- 长度列表的递归前缀和。 -/
def finite_family_prefix_length
    (lengths : List Nat) : Nat → Nat
  | 0 => 0
  | index + 1 =>
      finite_family_prefix_length lengths index +
        finite_family_piece_length lengths index

@[simp]
theorem finite_family_prefix_length_zero
    (lengths : List Nat) :
    finite_family_prefix_length lengths 0 = 0 :=
  rfl

@[simp]
theorem finite_family_prefix_length_step
    (lengths : List Nat) (index : Nat) :
    finite_family_prefix_length lengths (index + 1) =
      finite_family_prefix_length lengths index +
        finite_family_piece_length lengths index :=
  rfl

@[simp]
theorem finite_family_prefix_length_cons_succ
    (length : Nat) (lengths : List Nat)
    (index : Nat) :
    finite_family_prefix_length
        (length :: lengths) (index + 1) =
      length +
        finite_family_prefix_length lengths index := by
  induction index with
  | zero =>
      simp [finite_family_prefix_length_step]
  | succ index ih =>
      calc
        finite_family_prefix_length
              (length :: lengths) ((index + 1) + 1) =
            finite_family_prefix_length
                (length :: lengths) (index + 1) +
              finite_family_piece_length
                (length :: lengths) (index + 1) := rfl
        _ =
            (length +
                finite_family_prefix_length
                  lengths index) +
              finite_family_piece_length
                lengths index := by
              rw [ih,
                finite_family_piece_length_cons_succ]
        _ =
            length +
              finite_family_prefix_length
                lengths (index + 1) := by
              rw [finite_family_prefix_length_step]
              omega

/-- 有效分片的前缀与本段长度之和不超过总长度。 -/
theorem finite_family_prefix_add_piece_le_sum
    (lengths : List Nat) (index : Nat)
    (hIndex : index < lengths.length) :
    finite_family_prefix_length lengths index +
        finite_family_piece_length lengths index ≤
      lengths.sum := by
  induction lengths generalizing index with
  | nil =>
      simp at hIndex
  | cons length lengths ih =>
      cases index with
      | zero =>
          simp
      | succ index =>
          have hTail :
              index < lengths.length := by
            simpa using hIndex
          have hBound := ih index hTail
          simp only [
            finite_family_prefix_length_cons_succ,
            finite_family_piece_length_cons_succ,
            List.sum_cons]
          omega

/-- 长度列表末端的前缀和就是全列表之和。 -/
theorem finite_family_prefix_length_at_end
    (lengths : List Nat) :
    finite_family_prefix_length
        lengths lengths.length =
      lengths.sum := by
  induction lengths with
  | nil =>
      rfl
  | cons length lengths ih =>
      rw [List.length_cons,
        finite_family_prefix_length_cons_succ,
        List.sum_cons, ih]

private theorem
    finite_family_domain_length_context_piece_mem
    (family : SetTerm) (start : Nat)
    (lengths : List Nat)
    (index : Nat) (hIndex : index < lengths.length) :
    domₘ(family ·ₘ numₘ(start + index)) ≐ₘ
        numₘ(finite_family_piece_length lengths index) ∈
      finite_family_domain_length_context
        family start lengths := by
  induction lengths generalizing start index with
  | nil =>
      simp at hIndex
  | cons length lengths ih =>
      cases index with
      | zero =>
          simp [finite_family_domain_length_context,
            finite_family_piece_length]
      | succ index =>
          have hTail :
              index < lengths.length := by
            simpa using hIndex
          have hMember :=
            ih (start := start + 1)
              (index := index) hTail
          have hArithmetic :
              (start + 1) + index =
                start + (index + 1) := by
            omega
          rw [hArithmetic] at hMember
          exact List.mem_append_left
            [domₘ(family ·ₘ numₘ(start)) ≐ₘ
              numₘ(length)] <| by
              simpa [finite_family_piece_length] using
                hMember

/--
长度列表分支上下文按下标直接给出对应族元素的对象定义域证书。
-/
theorem gq_finite_family_domain_length_context_piece
    {Γ : Context signature}
    (family : SetTerm) (start : Nat)
    (lengths : List Nat)
    (index : Nat) (hIndex : index < lengths.length)
    (hFamily :
      Term.CheckCertificate family SetSort.set := by
        prove_term_check) :
    finite_family_domain_length_context
          family start lengths ++ Γ
      ⊢ₘ[godel_quotation_theory]
        domₘ(family ·ₘ numₘ(start + index)) ≐ₘ
          numₘ(finite_family_piece_length
            lengths index) :=
  FirstOrder.Derives.assumption
    (List.mem_append_left Γ <|
      finite_family_domain_length_context_piece_mem
        family start lengths index hIndex)
    (by prove_formula_check)

/--
有限族全部子序列定义域的有界长度消去。

第 `offset` 个子序列只需证明其定义域严格属于同一个标准父码定义域。结论分支
一次接收长度为 `count` 的外部列表，以及列表中每个长度对应的对象等式上下文。
-/
theorem gq_finite_family_domain_lengths_elim
    {Γ : Context signature}
    (family parent : SetTerm)
    (tokens : List Nat)
    (start count : Nat)
    (conclusion : SetFormula)
    (hFamily : Term.CheckCertificate family SetSort.set := by
      prove_term_check)
    (hParent : Term.CheckCertificate parent SetSort.set := by
      prove_term_check)
    (hConclusion :
      Formula.CheckCertificate conclusion := by
        prove_nd_formula_check)
    (hMember :
      ∀ offset, offset < count →
        Γ ⊢ₘ[godel_quotation_theory]
          domₘ(family ·ₘ
              numₘ(start + offset)) ∈ₘ
            domₘ(parent))
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ parent)
    (hBranch :
      ∀ lengths, lengths.length = count →
        finite_family_domain_length_context
            family start lengths ++ Γ
          ⊢ₘ[godel_quotation_theory]
            conclusion) :
    Γ ⊢ₘ[godel_quotation_theory]
      conclusion := by
  induction count generalizing Γ start with
  | zero =>
      simpa [finite_family_domain_length_context] using
        hBranch [] rfl
  | succ count ih =>
      have hCurrentMember :
          Γ ⊢ₘ[godel_quotation_theory]
            domₘ(family ·ₘ numₘ(start)) ∈ₘ
              domₘ(parent) := by
        simpa using hMember 0 (by omega)
      apply
        gq_domain_length_elim_of_member_of_standard_equality
          (family ·ₘ numₘ(start))
          parent tokens conclusion
          hCurrentMember hEquality
          (hChild := by prove_term_check)
          (hParent := hParent)
          (hConclusion := hConclusion)
      intro length hLength
      let equality : SetFormula :=
        domₘ(family ·ₘ numₘ(start)) ≐ₘ
          numₘ(length)
      let Δ : Context signature := equality :: Γ
      have hTailMember :
          ∀ offset, offset < count →
            Δ ⊢ₘ[godel_quotation_theory]
              domₘ(family ·ₘ
                  numₘ((start + 1) + offset)) ∈ₘ
                domₘ(parent) := by
        intro offset hOffset
        apply FirstOrder.Derives.context_weaken
          (Γ := Γ) (Δ := Δ)
        · intro formula hFormula
          exact List.mem_cons_of_mem equality hFormula
        · simpa [Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using
            hMember (offset + 1) (by omega)
      have hEqualityΔ :
          Δ ⊢ₘ[godel_quotation_theory]
            standard_token_sequence tokens ≐ₘ
              parent :=
        FirstOrder.Derives.context_weaken
          (Γ := Γ) (Δ := Δ)
          (by
            intro formula hFormula
            exact List.mem_cons_of_mem
              equality hFormula)
          hEquality
      apply ih
        (Γ := Δ)
        (start := start + 1)
        hTailMember hEqualityΔ
      intro lengths hLengths
      have hCombinedLength :
          (length :: lengths).length =
            count + 1 := by
        simp [hLengths]
      simpa [Δ, equality,
        finite_family_domain_length_context,
        List.append_assoc] using
        hBranch (length :: lengths)
          hCombinedLength

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
