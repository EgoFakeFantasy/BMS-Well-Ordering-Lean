import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SyntaxDecode
import YesMetaZFC.Logic.FirstOrder.Derivation

/-! # 全部二十七类基础逻辑公理的语法解码 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT
open Nonlogical.BasicSetTheory NatPacket
set_option autoImplicit false
namespace LogicalAxiomDecode

abbrev Result (free : SetContext) :=
  (formula : SetOpenFormula free) × HilbertBaseAxiom signature formula

def pack {free : SetContext} {formula : SetOpenFormula free}
    (certificate : HilbertBaseAxiom signature formula) : Result free := ⟨formula, certificate⟩

/-- 参数树精确匹配模式；量词模式分别验证 bound 与 free 作用域。 -/
def decode (free : SetContext) : Tree → Option (Result free)
  | .node 0 [a, b, c] => do
    return pack (.implication_distribution (← SyntaxDecode.formula [] free a) (← SyntaxDecode.formula [] free b) (← SyntaxDecode.formula [] free c))
  | .node 1 [a] => do
    return pack (.self_implication (← SyntaxDecode.formula [] free a))
  | .node 2 [a, b] => do
    return pack (.weakening (← SyntaxDecode.formula [] free a) (← SyntaxDecode.formula [] free b))
  | .node 3 [a, b] => do
    return pack (.contradiction (← SyntaxDecode.formula [] free a) (← SyntaxDecode.formula [] free b))
  | .node 4 [a] => do
    return pack (.classical (← SyntaxDecode.formula [] free a))
  | .node 5 [a, b] => do
    return pack (.explosion (← SyntaxDecode.formula [] free a) (← SyntaxDecode.formula [] free b))
  | .node 6 [a, b] => do
    return pack (.case_analysis (← SyntaxDecode.formula [] free a) (← SyntaxDecode.formula [] free b))
  | .node 7 [] => do
    return pack (.truth_intro)
  | .node 8 [a] => do
    return pack (.falsum_elimination (← SyntaxDecode.formula [] free a))
  | .node 9 [a] => do
    return pack (.negation_intro (← SyntaxDecode.formula [] free a))
  | .node 10 [a] => do
    return pack (.negation_elimination (← SyntaxDecode.formula [] free a))
  | .node 11 [a, b] => do
    return pack (.conjunction_intro (← SyntaxDecode.formula [] free a) (← SyntaxDecode.formula [] free b))
  | .node 12 [a, b] => do
    return pack (.conjunction_elim_left (← SyntaxDecode.formula [] free a) (← SyntaxDecode.formula [] free b))
  | .node 13 [a, b] => do
    return pack (.conjunction_elim_right (← SyntaxDecode.formula [] free a) (← SyntaxDecode.formula [] free b))
  | .node 14 [a, b] => do
    return pack (.disjunction_intro_left (← SyntaxDecode.formula [] free a) (← SyntaxDecode.formula [] free b))
  | .node 15 [a, b] => do
    return pack (.disjunction_intro_right (← SyntaxDecode.formula [] free a) (← SyntaxDecode.formula [] free b))
  | .node 16 [a, b, c] => do
    return pack (.disjunction_elimination (← SyntaxDecode.formula [] free a) (← SyntaxDecode.formula [] free b) (← SyntaxDecode.formula [] free c))
  | .node 17 [a, b] => do
    return pack (.biconditional_intro (← SyntaxDecode.formula [] free a) (← SyntaxDecode.formula [] free b))
  | .node 18 [a, b] => do
    return pack (.biconditional_elim_left (← SyntaxDecode.formula [] free a) (← SyntaxDecode.formula [] free b))
  | .node 19 [a, b] => do
    return pack (.biconditional_elim_right (← SyntaxDecode.formula [] free a) (← SyntaxDecode.formula [] free b))
  | .node 20 [body, term] => do
      return pack (.forall_specialization SetSort.set
        (← SyntaxDecode.formula [.set] free body) (← SyntaxDecode.term [] free term))
  | .node 21 [left, right] => do
      return pack (.forall_distribution SetSort.set
        (← SyntaxDecode.formula [] (.set :: free) left)
        (← SyntaxDecode.formula [] (.set :: free) right))
  | .node 22 [body] => do
      return pack (.vacuous_forall SetSort.set (← SyntaxDecode.formula [] free body))
  | .node 23 [body, term] => do
      return pack (.exists_introduction SetSort.set
        (← SyntaxDecode.formula [.set] free body) (← SyntaxDecode.term [] free term))
  | .node 24 [body, conclusion] => do
      return pack (.exists_elimination SetSort.set
        (← SyntaxDecode.formula [] (.set :: free) body)
        (← SyntaxDecode.formula [] free conclusion))
  | .node 25 [left, right, body] => do
      return pack (.equality_substitution SetSort.set
        (← SyntaxDecode.term [] free left) (← SyntaxDecode.term [] free right)
        (← SyntaxDecode.formula [.set] free body))
  | .node 26 [term] => do return pack (.equality_reflexivity (← SyntaxDecode.term [] free term))
  | _ => none
end LogicalAxiomDecode
end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT
