import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicAxiomCertificate
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicAxiomDecode

/-! # ZFC 固定公理与两类无界 schema 的数据解码 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open Nonlogical.BasicSetTheory NatPacket
open _root_.YesMetaZFC.SetTheory.Definitional
set_option autoImplicit false

namespace ProjectDecode
/-- schema 项只允许作用域内的束缚变量；自由变量不满足 schema 的闭性要求。 -/
def term (depth : Nat) : Tree → Option (Project.Term depth)
  | .node 0 [indexTree] => do
      let index ← scalar indexTree
      if h : index < depth then some (.bound ⟨index, h⟩) else none
  | _ => none

def formula (depth : Nat) (tree : Tree) : Option (Project.Formula 1 depth) :=
      match tree with
      | .node 0 [] => some .falsum
      | .node 1 [] => some .truth
      | .node 2 [left, right] => do return .mem (← term depth left) (← term depth right)
      | .node 3 [left, right] => do
          return Project.Formula.extensionalEq (← term depth left) (← term depth right)
      | .node 4 [body] => do return .neg (← formula depth body)
      | .node 5 [left, right] => do
          return .conj (← formula depth left) (← formula depth right)
      | .node 6 [left, right] => do
          return .disj (← formula depth left) (← formula depth right)
      | .node 7 [left, right] => do
          return .imp (← formula depth left) (← formula depth right)
      | .node 8 [left, right] => do
          return .iff (← formula depth left) (← formula depth right)
      | .node 9 [body] => do return .forallE (← formula (depth + 1) body)
      | .node 10 [body] => do return .existsE (← formula (depth + 1) body)
      | .node 11 [left, right] => do
          return Project.Formula.subset (← term depth left) (← term depth right)
      | _ => none
termination_by sizeOf tree

def unarySchema (parameterCount : Nat) (tree : Tree) : Option (Project.UnarySchema parameterCount) := do
  let body ← formula (parameterCount + 1) tree
  if h : body.FreeClosed then some ⟨body, h⟩ else none

def binarySchema (parameterCount : Nat) (tree : Tree) : Option (Project.BinarySchema parameterCount) := do
  let body ← formula (parameterCount + 2) tree
  if h : body.FreeClosed then some ⟨body, h⟩ else none
end ProjectDecode

/-- 标签 0–7 是固定公理，8 与 9 携带参数数目及 schema 体。 -/
def zfc_base_axiom_decode : Tree → Option ZFCAxiomCertificate
  | .node 0 [] => some .extensionality
  | .node 1 [] => some .emptySet
  | .node 2 [] => some .pairing
  | .node 3 [] => some .union
  | .node 4 [] => some .powerSet
  | .node 5 [] => some .infinity
  | .node 6 [] => some .foundation
  | .node 7 [] => some .choice
  | .node 8 [countTree, body] => do
      let count ← scalar countTree
      return .separation (← ProjectDecode.unarySchema count body)
  | .node 9 [countTree, body] => do
      let count ← scalar countTree
      return .collection (← ProjectDecode.binarySchema count body)
  | _ => none

/-- 完整支撑公理理论的可计算解码入口。 -/
def intrinsic_zfc_axiom_decode : AxiomDecoder intrinsic_zfc_axiom_presentation :=
  AxiomDecoder.union zfc_base_axiom_decode intrinsic_proof_axiom_decode
end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
