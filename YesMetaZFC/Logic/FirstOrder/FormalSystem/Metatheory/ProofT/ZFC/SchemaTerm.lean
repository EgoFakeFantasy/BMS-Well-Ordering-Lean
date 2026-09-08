import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.CodePattern
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.AxiomDecode

/-!
# 模式正文的束缚变量正负表示

直接表示实际 `ProjectDecode.term` 的成功与失败，输入可以是任意原始有限树。
同一个二元 Delta0 公式同时检查项构造、叶子索引和作用域；不预设输入已解析，
不固定参数数目，也不借用旧六构造子语法谓词。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaTerm
open Nonlogical.BasicSetTheory QuineEncoding NatPacket ProofCode
open IntrinsicQuotation CodePattern
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
set_option autoImplicit false

def pattern : Pattern := nodePattern (.literal 0) [nodePattern .first []]

def check (depth : Nat) (input : Tree) : Bool := (ProjectDecode.term depth input).isSome

theorem check_eq_true_iff (depth : Nat) (input : Tree) :
    check depth input = true ↔ ∃ index, index < depth ∧ input = .node 0 [leaf index] := by
  cases input with
  | node tag fields =>
    cases tag with
    | succ _ => simp [check, ProjectDecode.term]
    | zero =>
      cases fields with
      | nil => simp [check, ProjectDecode.term]
      | cons head tail =>
        cases tail with
        | cons _ _ => simp [check, ProjectDecode.term]
        | nil =>
          cases head with
          | node index fields =>
            cases fields with
            | cons _ _ => simp [check, ProjectDecode.term, scalar, leaf]
            | nil =>
              by_cases h : index < depth <;>
                simp [check, ProjectDecode.term, scalar, leaf, h]

theorem value_iff (input : Tree) (index : Nat) :
    treeValue input = pattern.eval index 0 ↔ input = .node 0 [leaf index] := by
  change treeValue input = treeValue (.node 0 [leaf index]) ↔ _
  exact ⟨fun h => treeValue_injective h, congrArg treeValue⟩

def condition {bound free : SetContext} (depth input : SetTerm bound free) :
    SetFormula bound free := CodePattern.unaryGraph pattern depth input

theorem condition_delta0 {bound free : SetContext} (depth input : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound (condition depth input) :=
  CodePattern.unaryGraph_delta0 _ _ _

theorem positive (depth : Nat) (input : Tree) (h : check depth input = true) :
    Derives intrinsic_zfc_theory []
      (condition (numₘ(depth)) (numₘ(treeValue input) : Code)) := by
  obtain ⟨index, hIndex, hShape⟩ := (check_eq_true_iff depth input).mp h
  exact CodePattern.unary_positive intrinsic_zfc_certificate_core
    intrinsic_zfc_arithmetic_support.contains_successor pattern depth _ index hIndex
    ((value_iff input index).mpr hShape)

theorem negative (depth : Nat) (input : Tree) (h : check depth input = false) :
    Derives intrinsic_zfc_theory []
      (¬ₘ condition (numₘ(depth)) (numₘ(treeValue input) : Code)) := by
  apply CodePattern.unary_negative intrinsic_zfc_certificate_core
  intro index hIndex hEq
  have hTrue := (check_eq_true_iff depth input).mpr
    ⟨index, hIndex, (value_iff input index).mp hEq⟩
  rw [h] at hTrue
  contradiction

theorem positive_at_tree (depth : Nat) (input : Tree) (h : check depth input = true) :
    Derives intrinsic_zfc_theory []
      (condition (numₘ(depth)) (IntrinsicQuotation.tree input)) :=
  CodePattern.unary_transport pattern (numₘ(depth))
    (Metatheory.Derives.equality_symm (tree_evaluate intrinsic_zfc_certificate_core input))
    (positive depth input h)

theorem negative_at_tree (depth : Nat) (input : Tree) (h : check depth input = false) :
    Derives intrinsic_zfc_theory []
      (¬ₘ condition (numₘ(depth)) (IntrinsicQuotation.tree input)) :=
  CodePattern.unary_transport_neg pattern (numₘ(depth))
    (Metatheory.Derives.equality_symm (tree_evaluate intrinsic_zfc_certificate_core input))
    (negative depth input h)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaTerm
