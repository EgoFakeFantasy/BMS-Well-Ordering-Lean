import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicQuotation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.PairingInversionDirect

/-!
# 新 quotation 的对象求值与相等判定

quotation 的单射不仅是宿主 AST 性质：有限算术核能够在对象理论内区分任意两个
不同的标准公式码。本层只消费已有 `CertificateCore`，不新增对象公理。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.IntrinsicQuotation
open Nonlogical.BasicSetTheory QuineEncoding NatPacket ProofCode
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
set_option autoImplicit false

mutual
def treeValue : Tree → Nat
  | .node tag children => godel_pair_value tag (forestValue children) + 1
def forestValue : List Tree → Nat
  | [] => godel_pair_value 0 0 + 1
  | head :: tail => godel_pair_value 1 (godel_pair_value (treeValue head) (forestValue tail)) + 1
end

mutual
private theorem treeValue_eq (left right : Tree) (h : treeValue left = treeValue right) : left = right := by
  cases left with
  | node a xs =>
    cases right with
    | node b ys =>
      have hPair := godel_pair_value_eq_iff.mp (Nat.add_right_cancel h)
      have hChildren := forestValue_eq xs ys hPair.2
      cases hPair.1
      cases hChildren
      rfl
termination_by sizeOf left

private theorem forestValue_eq (left right : List Tree) (h : forestValue left = forestValue right) : left = right := by
  cases left with
  | nil =>
    cases right with
    | nil => rfl
    | cons b ys =>
      have hPair := godel_pair_value_eq_iff.mp (Nat.add_right_cancel h)
      cases hPair.1
  | cons a xs =>
    cases right with
    | nil =>
      have hPair := godel_pair_value_eq_iff.mp (Nat.add_right_cancel h)
      cases hPair.1
    | cons b ys =>
      have hPair := godel_pair_value_eq_iff.mp (Nat.add_right_cancel h)
      have hFields := godel_pair_value_eq_iff.mp hPair.2
      have hHead := treeValue_eq a b hFields.1
      have hTail := forestValue_eq xs ys hFields.2
      cases hHead
      cases hTail
      rfl
termination_by sizeOf left
end

/-- 原始树数值码的单射；供尚未解析为类型化语法的识别器反演。 -/
theorem treeValue_injective : Function.Injective treeValue := fun _ _ h => treeValue_eq _ _ h

/-- 该数值只用于求值证明；对象 quotation 本身仍保留紧凑的结构项。 -/
def value {bound free : SetContext} (formula : SetFormula bound free) : Nat :=
  treeValue (SyntaxEncode.formula formula)

theorem value_injective {bound free : SetContext} : Function.Injective (@value bound free) := by
  intro left right h
  have hTree := treeValue_eq (SyntaxEncode.formula left) (SyntaxEncode.formula right) h
  have hDecoded := congrArg (SyntaxDecode.formula bound free) hTree
  simpa only [SyntaxEncode.formula_roundtrip, Option.some.injEq] using hDecoded

private theorem pair_evaluate {T : SetTheory} (C : CertificateCore T)
    (left right : Code) (a b : Nat)
    (hLeft : Derives T [] (left ≐ₘ numₘ(a)))
    (hRight : Derives T [] (right ≐ₘ numₘ(b))) :
    Derives T [] (godel_pairₘ(left, right) ≐ₘ numₘ(godel_pair_value a b)) :=
  Metatheory.Derives.equality_trans
    (IntrinsicPairing.pair_congr_of_equalities left (numₘ(a)) right (numₘ(b)) hLeft hRight)
    (C.pair_value a b)

private theorem node_evaluate {T : SetTheory} (C : CertificateCore T)
    (tag : Nat) (payload : Code) (n : Nat)
    (hPayload : Derives T [] (payload ≐ₘ numₘ(n))) :
    Derives T [] (Sₘ(godel_pairₘ(numₘ(tag), payload)) ≐ₘ numₘ(godel_pair_value tag n + 1)) :=
  successor_term_congr_of_equality _ _
    (pair_evaluate C _ _ tag n (Metatheory.Derives.equality_refl _) hPayload)

mutual
theorem tree_evaluate {T : SetTheory} (C : CertificateCore T) (input : Tree) :
    Derives T [] (tree input ≐ₘ numₘ(treeValue input)) := by
  cases input with
  | node tag children =>
      exact node_evaluate C tag _ _ (forest_evaluate C children)
termination_by sizeOf input

theorem forest_evaluate {T : SetTheory} (C : CertificateCore T) (input : List Tree) :
    Derives T [] (structural_list_code_term (forest input) ≐ₘ numₘ(forestValue input)) := by
  cases input with
  | nil => exact node_evaluate C 0 _ 0 (Metatheory.Derives.equality_refl _)
  | cons head tail =>
      exact node_evaluate C 1 _ _
        (pair_evaluate C _ _ _ _ (tree_evaluate C head) (forest_evaluate C tail))
termination_by sizeOf input
end

theorem quote_evaluate {T : SetTheory} (C : CertificateCore T)
    {bound free : SetContext} (formula : SetFormula bound free) :
    Derives T [] (quote formula ≐ₘ numₘ(value formula)) :=
  tree_evaluate C (SyntaxEncode.formula formula)

/-- 不同公式的 quotation 在对象理论中可证明不等。 -/
theorem quote_ne {T : SetTheory} (C : CertificateCore T)
    {bound free : SetContext} {left right : SetFormula bound free} (h : left ≠ right) :
    Derives T [] (¬ₘ (quote left ≐ₘ quote right)) := by
  have hValues : value left ≠ value right := fun hEq => h (value_injective hEq)
  apply FirstOrder.Derives.neg_intro
  have hCode : Derives T [quote left ≐ₘ quote right] (quote left ≐ₘ quote right) :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hLeft := FirstOrder.Derives.context_weaken_cons (assumption := quote left ≐ₘ quote right) (quote_evaluate C left)
  have hRight := FirstOrder.Derives.context_weaken_cons (assumption := quote left ≐ₘ quote right) (quote_evaluate C right)
  have hNumeric := Metatheory.Derives.equality_trans
    (Metatheory.Derives.equality_symm hLeft)
    (Metatheory.Derives.equality_trans hCode hRight)
  exact FirstOrder.Derives.neg_elim hNumeric
    (FirstOrder.Derives.context_weaken_cons (C.numeral_ne hValues))

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.IntrinsicQuotation
