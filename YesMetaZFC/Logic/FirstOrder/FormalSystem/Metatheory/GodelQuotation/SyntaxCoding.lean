import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemNumbering
import YesMetaZFC.Logic.FirstOrder.NatPairing
/-!
# 可编号单排序签名的构造性语法编码
Gödel quotation 已经要求函数符号与关系符号具有自然数单射编号，并要求签名只有
一个对象 sort。本模块复用同一编号数据，对原始 LN 项与公式给出可计算单射编码。
该编码只供 checked replay 比较语法对象，不携带 Henkin 调度、完备性或语义接口。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace GodelQuotation
namespace SyntaxCoding
open Nonlogical.BasicSetTheory
universe u v w
variable {σ : Signature.{u, v, w}} [QuotationNumbering σ]
/-! ## sort 与符号编号 -/
/-- 单排序签名中的 sort 统一编码为零。 -/
def sort_encode (_sort : σ.SortSymbol) : Nat :=
  0
/-- 单排序条件保证常值 sort 编码仍然单射。 -/
theorem sort_encode_injective :
    Function.Injective (sort_encode (σ := σ)) := by
  intro left right _
  exact (QuotationNumbering.sort_eq left).trans (QuotationNumbering.sort_eq right).symm
/-- 函数符号直接复用 quotation 编号。 -/
def function_symbol_encode (symbol : σ.FuncSymbol) : Nat :=
  QuotationNumbering.function_number symbol
/-- quotation 的函数符号编号保持单射。 -/
theorem function_symbol_encode_injective :
    Function.Injective (function_symbol_encode (σ := σ)) :=
  QuotationNumbering.function_number_injective
/-- 关系符号直接复用 quotation 编号。 -/
def relation_symbol_encode (symbol : σ.RelSymbol) : Nat :=
  QuotationNumbering.relation_number symbol
/-- quotation 的关系符号编号保持单射。 -/
theorem relation_symbol_encode_injective :
    Function.Injective (relation_symbol_encode (σ := σ)) :=
  QuotationNumbering.relation_number_injective
/-! ## LN 项编码 -/
mutual
  /-- 项大小只用于证明互递归反演终止。 -/
  def term_size : Term σ → Nat
    | .var _ => 1
    | .app _ arguments => term_list_size arguments + 1
  /-- 项列表大小与项大小同步递归。 -/
  def term_list_size : List (Term σ) → Nat
    | [] => 0
    | term :: rest => term_size term + term_list_size rest + 1
end
mutual
  /-- 原始 LN 项的带构造标签单射编码。 -/
  def term_encode : Term σ → Nat
    | .var (.bvar sort index) =>
        NatPairing.pair 0 (NatPairing.pair (sort_encode sort) index)
    | .var (.fvar sort id) =>
        NatPairing.pair 1 (NatPairing.pair (sort_encode sort) id)
    | .app function arguments =>
        NatPairing.pair 2 (NatPairing.pair (function_symbol_encode function) (term_list_encode arguments))
  /-- 项列表以零编码空表，以正配对编码首尾。 -/
  def term_list_encode : List (Term σ) → Nat
    | [] => 0
    | term :: rest =>
        NatPairing.pair (term_encode term) (term_list_encode rest) + 1
end
mutual
  theorem term_encode_eq
      {left right : Term σ} (hCode : term_encode left = term_encode right) :
      left = right := by
    cases left with
    | var leftVariable =>
        cases right with
        | var rightVariable =>
            cases leftVariable with
            | bvar sort index =>
                cases rightVariable with
                | bvar sort' index' =>
                    rcases NatPairing.pair_eq_pair_iff.mp hCode with
                      ⟨_, hPayload⟩
                    rcases NatPairing.pair_eq_pair_iff.mp hPayload with
                      ⟨hSort, hIndex⟩
                    rw [sort_encode_injective hSort, hIndex]
                | fvar =>
                    have hTag := (NatPairing.pair_eq_pair_iff.mp hCode).1
                    omega
            | fvar sort id =>
                cases rightVariable with
                | bvar =>
                    have hTag := (NatPairing.pair_eq_pair_iff.mp hCode).1
                    omega
                | fvar sort' id' =>
                    rcases NatPairing.pair_eq_pair_iff.mp hCode with
                      ⟨_, hPayload⟩
                    rcases NatPairing.pair_eq_pair_iff.mp hPayload with
                      ⟨hSort, hId⟩
                    rw [sort_encode_injective hSort, hId]
        | app =>
            cases leftVariable <;>
              simp [term_encode,
                NatPairing.pair_eq_pair_iff] at hCode
    | app function arguments =>
        cases right with
        | var rightVariable =>
            cases rightVariable <;>
              simp [term_encode,
                NatPairing.pair_eq_pair_iff] at hCode
        | app function' arguments' =>
            rcases NatPairing.pair_eq_pair_iff.mp hCode with
              ⟨_, hPayload⟩
            rcases NatPairing.pair_eq_pair_iff.mp hPayload with
              ⟨hFunction, hArguments⟩
            rw [function_symbol_encode_injective hFunction,
              term_list_encode_eq hArguments]
  theorem term_list_encode_eq
      {left right : List (Term σ)} (hCode : term_list_encode left = term_list_encode right) :
      left = right := by
    cases left with
    | nil =>
        cases right with
        | nil => rfl
        | cons head tail =>
            simp [term_list_encode] at hCode
    | cons head tail =>
        cases right with
        | nil =>
            simp [term_list_encode] at hCode
        | cons head' tail' =>
            simp only [term_list_encode] at hCode
            have hPair := Nat.add_right_cancel hCode
            rcases NatPairing.pair_eq_pair_iff.mp hPair with
              ⟨hHead, hTail⟩
            rw [term_encode_eq hHead,
              term_list_encode_eq hTail]
end
/-- 原始 LN 项编码保持单射。 -/
theorem term_encode_injective :
    Function.Injective (term_encode (σ := σ)) :=
  fun _ _ => term_encode_eq
/-- 原始 LN 项列表编码保持单射。 -/
theorem term_list_encode_injective :
    Function.Injective (term_list_encode (σ := σ)) :=
  fun _ _ => term_list_encode_eq
/-! ## LN 公式编码 -/
/-- 原始 LN 公式的带构造标签单射编码。 -/
def formula_encode : Formula σ → Nat
  | .falsum => NatPairing.pair 0 0
  | .truth => NatPairing.pair 1 0
  | .rel relation arguments =>
      NatPairing.pair 2 (NatPairing.pair (relation_symbol_encode relation) (term_list_encode arguments))
  | .equal left right =>
      NatPairing.pair 3 (NatPairing.pair (term_encode left) (term_encode right))
  | .neg body =>
      NatPairing.pair 4 (formula_encode body)
  | .conj left right =>
      NatPairing.pair 5 (NatPairing.pair (formula_encode left) (formula_encode right))
  | .disj left right =>
      NatPairing.pair 6 (NatPairing.pair (formula_encode left) (formula_encode right))
  | .imp left right =>
      NatPairing.pair 7 (NatPairing.pair (formula_encode left) (formula_encode right))
  | .iff left right =>
      NatPairing.pair 8 (NatPairing.pair (formula_encode left) (formula_encode right))
  | .forallE sort body =>
      NatPairing.pair 9 (NatPairing.pair (sort_encode sort) (formula_encode body))
  | .existsE sort body =>
      NatPairing.pair 10 (NatPairing.pair (sort_encode sort) (formula_encode body))
/-- 公式编码相等可按构造递归反演为公式相等。 -/
theorem formula_encode_injective :
    Function.Injective (formula_encode (σ := σ)) := by
  intro left
  induction left with
  | falsum =>
      intro right hCode
      cases right
      case falsum => rfl
      all_goals
        have hTag := (NatPairing.pair_eq_pair_iff.mp hCode).1
        omega
  | truth =>
      intro right hCode
      cases right
      case truth => rfl
      all_goals
        have hTag := (NatPairing.pair_eq_pair_iff.mp hCode).1
        omega
  | rel relation arguments =>
      intro right hCode
      cases right
      case rel relation' arguments' =>
        rcases NatPairing.pair_eq_pair_iff.mp hCode with
          ⟨_, hPayload⟩
        rcases NatPairing.pair_eq_pair_iff.mp hPayload with
          ⟨hRelation, hArguments⟩
        rw [relation_symbol_encode_injective hRelation,
          term_list_encode_injective hArguments]
      all_goals
        have hTag := (NatPairing.pair_eq_pair_iff.mp hCode).1
        omega
  | equal left right =>
      intro target hCode
      cases target
      case equal left' right' =>
        rcases NatPairing.pair_eq_pair_iff.mp hCode with
          ⟨_, hPayload⟩
        rcases NatPairing.pair_eq_pair_iff.mp hPayload with
          ⟨hLeft, hRight⟩
        rw [term_encode_injective hLeft,
          term_encode_injective hRight]
      all_goals
        have hTag := (NatPairing.pair_eq_pair_iff.mp hCode).1
        omega
  | neg body ih =>
      intro right hCode
      cases right
      case neg body' =>
        have hBody := (NatPairing.pair_eq_pair_iff.mp hCode).2
        rw [ih hBody]
      all_goals
        have hTag := (NatPairing.pair_eq_pair_iff.mp hCode).1
        omega
  | conj left right ihLeft ihRight =>
      intro target hCode
      cases target
      case conj left' right' =>
        rcases NatPairing.pair_eq_pair_iff.mp hCode with
          ⟨_, hPayload⟩
        rcases NatPairing.pair_eq_pair_iff.mp hPayload with
          ⟨hLeft, hRight⟩
        rw [ihLeft hLeft, ihRight hRight]
      all_goals
        have hTag := (NatPairing.pair_eq_pair_iff.mp hCode).1
        omega
  | disj left right ihLeft ihRight =>
      intro target hCode
      cases target
      case disj left' right' =>
        rcases NatPairing.pair_eq_pair_iff.mp hCode with
          ⟨_, hPayload⟩
        rcases NatPairing.pair_eq_pair_iff.mp hPayload with
          ⟨hLeft, hRight⟩
        rw [ihLeft hLeft, ihRight hRight]
      all_goals
        have hTag := (NatPairing.pair_eq_pair_iff.mp hCode).1
        omega
  | imp left right ihLeft ihRight =>
      intro target hCode
      cases target
      case imp left' right' =>
        rcases NatPairing.pair_eq_pair_iff.mp hCode with
          ⟨_, hPayload⟩
        rcases NatPairing.pair_eq_pair_iff.mp hPayload with
          ⟨hLeft, hRight⟩
        rw [ihLeft hLeft, ihRight hRight]
      all_goals
        have hTag := (NatPairing.pair_eq_pair_iff.mp hCode).1
        omega
  | iff left right ihLeft ihRight =>
      intro target hCode
      cases target
      case iff left' right' =>
        rcases NatPairing.pair_eq_pair_iff.mp hCode with
          ⟨_, hPayload⟩
        rcases NatPairing.pair_eq_pair_iff.mp hPayload with
          ⟨hLeft, hRight⟩
        rw [ihLeft hLeft, ihRight hRight]
      all_goals
        have hTag := (NatPairing.pair_eq_pair_iff.mp hCode).1
        omega
  | forallE sort body ih =>
      intro right hCode
      cases right
      case forallE sort' body' =>
        rcases NatPairing.pair_eq_pair_iff.mp hCode with
          ⟨_, hPayload⟩
        rcases NatPairing.pair_eq_pair_iff.mp hPayload with
          ⟨hSort, hBody⟩
        rw [sort_encode_injective hSort, ih hBody]
      all_goals
        have hTag := (NatPairing.pair_eq_pair_iff.mp hCode).1
        omega
  | existsE sort body ih =>
      intro right hCode
      cases right
      case existsE sort' body' =>
        rcases NatPairing.pair_eq_pair_iff.mp hCode with
          ⟨_, hPayload⟩
        rcases NatPairing.pair_eq_pair_iff.mp hPayload with
          ⟨hSort, hBody⟩
        rw [sort_encode_injective hSort, ih hBody]
      all_goals
        have hTag := (NatPairing.pair_eq_pair_iff.mp hCode).1
        omega
end SyntaxCoding
end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
