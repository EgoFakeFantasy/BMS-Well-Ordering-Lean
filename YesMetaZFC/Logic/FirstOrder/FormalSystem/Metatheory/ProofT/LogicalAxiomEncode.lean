import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.LogicalAxiomDecode
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SyntaxEncode

/-! # 二十七类逻辑公理的逆向编码与往返 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.LogicalAxiomEncode
open Nonlogical.BasicSetTheory NatPacket
set_option autoImplicit false

def encode {free : SetContext} {formula : SetOpenFormula free} :
    HilbertBaseAxiom signature formula → Tree
  | .implication_distribution a b c => .node 0 [SyntaxEncode.formula a, SyntaxEncode.formula b, SyntaxEncode.formula c]
  | .self_implication a => .node 1 [SyntaxEncode.formula a]
  | .weakening a b => .node 2 [SyntaxEncode.formula a, SyntaxEncode.formula b]
  | .contradiction a b => .node 3 [SyntaxEncode.formula a, SyntaxEncode.formula b]
  | .classical a => .node 4 [SyntaxEncode.formula a]
  | .explosion a b => .node 5 [SyntaxEncode.formula a, SyntaxEncode.formula b]
  | .case_analysis a b => .node 6 [SyntaxEncode.formula a, SyntaxEncode.formula b]
  | .truth_intro  => .node 7 []
  | .falsum_elimination a => .node 8 [SyntaxEncode.formula a]
  | .negation_intro a => .node 9 [SyntaxEncode.formula a]
  | .negation_elimination a => .node 10 [SyntaxEncode.formula a]
  | .conjunction_intro a b => .node 11 [SyntaxEncode.formula a, SyntaxEncode.formula b]
  | .conjunction_elim_left a b => .node 12 [SyntaxEncode.formula a, SyntaxEncode.formula b]
  | .conjunction_elim_right a b => .node 13 [SyntaxEncode.formula a, SyntaxEncode.formula b]
  | .disjunction_intro_left a b => .node 14 [SyntaxEncode.formula a, SyntaxEncode.formula b]
  | .disjunction_intro_right a b => .node 15 [SyntaxEncode.formula a, SyntaxEncode.formula b]
  | .disjunction_elimination a b c => .node 16 [SyntaxEncode.formula a, SyntaxEncode.formula b, SyntaxEncode.formula c]
  | .biconditional_intro a b => .node 17 [SyntaxEncode.formula a, SyntaxEncode.formula b]
  | .biconditional_elim_left a b => .node 18 [SyntaxEncode.formula a, SyntaxEncode.formula b]
  | .biconditional_elim_right a b => .node 19 [SyntaxEncode.formula a, SyntaxEncode.formula b]
  | .forall_specialization _ body term => .node 20 [SyntaxEncode.formula body, SyntaxEncode.term term]
  | .forall_distribution _ left right => .node 21 [SyntaxEncode.formula left, SyntaxEncode.formula right]
  | .vacuous_forall _ body => .node 22 [SyntaxEncode.formula body]
  | .exists_introduction _ body term => .node 23 [SyntaxEncode.formula body, SyntaxEncode.term term]
  | .exists_elimination _ body conclusion => .node 24 [SyntaxEncode.formula body, SyntaxEncode.formula conclusion]
  | .equality_substitution _ left right body => .node 25 [SyntaxEncode.term left, SyntaxEncode.term right, SyntaxEncode.formula body]
  | .equality_reflexivity term => .node 26 [SyntaxEncode.term term]

@[simp] theorem roundtrip {free : SetContext} {formula : SetOpenFormula free}
    (certificate : HilbertBaseAxiom signature formula) :
    LogicalAxiomDecode.decode free (encode certificate) = some ⟨formula, certificate⟩ := by
  cases certificate <;> (try cases ‹SetSort›) <;>
    simp only [encode, LogicalAxiomDecode.decode, SyntaxEncode.formula_roundtrip,
      SyntaxEncode.term_roundtrip, Option.pure_def, LogicalAxiomDecode.pack] <;> rfl
end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.LogicalAxiomEncode
