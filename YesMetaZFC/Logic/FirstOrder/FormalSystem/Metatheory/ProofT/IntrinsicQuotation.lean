import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SyntaxEncode

/-!
# 与当前内在 AST 同形的对象 quotation

语法树直接使用自然数编解码的标签与字段。对象项由现有后继、配数和结构列表构成，
不先做 Hilbert 化，也不把巨大自然数展开为一元 numeral。`unquote` 只读取对象项的
宿主语法；其往返定理证明 quotation 保留全部构造子，不替代对象理论内的表示证明。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.IntrinsicQuotation
open Nonlogical.BasicSetTheory QuineEncoding NatPacket
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def node {bound free : SetContext} (tag : Nat) (fields : List (SetTerm bound free)) :
    SetTerm bound free := Sₘ(godel_pairₘ(numₘ(tag), structural_list_code_term fields))

mutual
def tree : Tree → Code
  | .node tag children => node tag (forest children)
def forest : List Tree → List Code
  | [] => []
  | head :: tail => tree head :: forest tail
end

private def numeral? (input : SyntaxCoding.TermCode) : Option Nat :=
  match input with
  | .application symbol .nil => if symbol == FunctionSymbol.emptySet.ctorIdx then some 0 else none
  | .application symbol (.cons rest .nil) =>
      if symbol == FunctionSymbol.successor.ctorIdx then Nat.succ <$> numeral? rest else none
  | _ => none
termination_by sizeOf input

mutual
private def tree? (input : SyntaxCoding.TermCode) : Option Tree :=
  match input with
  | .application successor (.cons (.application pairing (.cons tag (.cons fields .nil))) .nil) =>
      if successor == FunctionSymbol.successor.ctorIdx && pairing == FunctionSymbol.godelPairing.ctorIdx then do
        return .node (← numeral? tag) (← forest? fields)
      else none
  | _ => none
termination_by sizeOf input
private def forest? (input : SyntaxCoding.TermCode) : Option (List Tree) :=
  match input with
  | .application successor (.cons (.application pairing (.cons tag (.cons fields .nil))) .nil) =>
      if successor == FunctionSymbol.successor.ctorIdx && pairing == FunctionSymbol.godelPairing.ctorIdx then
        match numeral? tag, fields with
        | some 0, .application empty .nil =>
            if empty == FunctionSymbol.emptySet.ctorIdx then some [] else none
        | some 1, .application pair (.cons head (.cons tail .nil)) =>
            if pair == FunctionSymbol.godelPairing.ctorIdx then do
              return (← tree? head) :: (← forest? tail)
            else none
        | _, _ => none
      else none
  | _ => none
termination_by sizeOf input
end

private theorem numeral_roundtrip (n : Nat) : numeral? (SyntaxCoding.term_code (numₘ(n) : Code)) = some n := by
  induction n with
  | zero => rw [numeral?.eq_def]; rfl
  | succ n ih =>
      rw [numeral?.eq_def]
      change Nat.succ <$> numeral? (SyntaxCoding.term_code (numₘ(n) : Code)) = some (n + 1)
      rw [ih]
      rfl

mutual
private theorem tree_roundtrip (input : Tree) : tree? (SyntaxCoding.term_code (tree input)) = some input := by
  cases input with
  | node tag children =>
      rw [tree?.eq_def]
      change (numeral? (SyntaxCoding.term_code (numₘ(tag) : Code))).bind (fun n =>
        (forest? (SyntaxCoding.term_code (structural_list_code_term (forest children)))).bind
          (fun ts => some (Tree.node n ts))) = some (Tree.node tag children)
      rw [numeral_roundtrip]
      change (forest? (SyntaxCoding.term_code (structural_list_code_term (forest children)))).bind
        (fun ts => some (Tree.node tag ts)) = some (Tree.node tag children)
      rw [forest_roundtrip]
      rfl
private theorem forest_roundtrip (input : List Tree) :
    forest? (SyntaxCoding.term_code (structural_list_code_term (forest input))) = some input := by
  cases input with
  | nil =>
      rw [forest?.eq_def]
      dsimp only [forest, structural_list_code_term, SyntaxCoding.term_code, SyntaxCoding.arguments_code]
      rw [numeral_roundtrip (structural_code_tag .listNil)]
      rfl
  | cons head tail =>
      rw [forest?.eq_def]
      dsimp only [forest, structural_list_code_term, SyntaxCoding.term_code, SyntaxCoding.arguments_code]
      rw [numeral_roundtrip (structural_code_tag .listCons)]
      change (tree? (SyntaxCoding.term_code (tree head))).bind (fun t =>
        (forest? (SyntaxCoding.term_code (structural_list_code_term (forest tail)))).bind
          (fun ts => some (t :: ts))) = some (head :: tail)
      rw [tree_roundtrip]
      change (forest? (SyntaxCoding.term_code (structural_list_code_term (forest tail)))).bind
        (fun ts => some (head :: ts)) = some (head :: tail)
      rw [forest_roundtrip]
      rfl
end

/-- 当前全部十一种公式构造子的直接对象码。 -/
def quote {bound free : SetContext} (formula : SetFormula bound free) : Code :=
  tree (SyntaxEncode.formula formula)

/-- 根据预期的类型化上下文恢复公式；不解释对象项的集合论语义。 -/
def unquote (bound free : SetContext) (code : Code) : Option (SetFormula bound free) := do
  SyntaxDecode.formula bound free (← tree? (SyntaxCoding.term_code code))

@[simp] theorem unquote_quote {bound free : SetContext} (formula : SetFormula bound free) :
    unquote bound free (quote formula) = some formula := by
  unfold unquote quote
  rw [tree_roundtrip]
  exact SyntaxEncode.formula_roundtrip formula

theorem quote_injective {bound free : SetContext} :
    Function.Injective (@quote bound free) := by
  intro left right h
  have hDecoded := congrArg (unquote bound free) h
  simpa only [unquote_quote, Option.some.injEq] using hDecoded

/-- 否定码是同一对象语言中的固定项构造，供 Rosser 谓词消费。 -/
def negation {bound free : SetContext} (code : SetTerm bound free) : SetTerm bound free :=
  node 4 [code]

@[simp] theorem quote_negation {bound free : SetContext} (formula : SetFormula bound free) :
    quote (.neg formula) = negation (quote formula) := rfl

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.IntrinsicQuotation
