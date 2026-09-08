import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.LogicalAxiomDecode
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.AxiomDecode
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ProofCertificate

/-!
# 自然数到普通 Hilbert 证书的正向解码

六条规则全部保留。规则间的公式连接作结构相等判定，成功才运输依赖类型证书。
沿有限输入树直接递归，没有固定的公式级别、变量数或证明长度限制。
可靠性从成功构造的证书重放得到；本模块不假定逆向编码完备性或对象层表示。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT
open Nonlogical.BasicSetTheory NatPacket
set_option autoImplicit false
namespace NatDecode

abbrev Result {T : SetTheory} (axioms : AxiomPresentation T) (free : SetContext) :=
  (formula : SetOpenFormula free) × ProofCertificate axioms free formula

def pack {T : SetTheory} {axioms : AxiomPresentation T}
    {free : SetContext} {formula : SetOpenFormula free}
    (certificate : ProofCertificate axioms free formula) : Result axioms free := ⟨formula, certificate⟩

def castProof {T : SetTheory} {axioms : AxiomPresentation T} {free : SetContext}
    {left right : SetOpenFormula free} (h : left = right)
    (certificate : ProofCertificate axioms free left) : ProofCertificate axioms free right :=
  h ▸ certificate

/-- MP 只有在前提公式与蕴涵左端完全相等时通过。 -/
def modusPonens {T : SetTheory} {axioms : AxiomPresentation T} {free : SetContext}
    (premise implication : Result axioms free) : Option (Result axioms free) :=
  match implication with
  | ⟨.imp antecedent _, certificate⟩ =>
      match SyntaxDecode.formulaEq premise.1 antecedent with
      | isTrue h => some (pack (.modus_ponens (castProof h premise.2) certificate))
      | isFalse _ => none
  | _ => none

/-- 规则标签依次为逻辑公理、理论公理、MP、全称一般化、free strengthening、统一替换。 -/
def tree {T : SetTheory} {axioms : AxiomPresentation T} (decodeAxiom : AxiomDecoder axioms)
    (free : SetContext) (input : Tree) : Option (Result axioms free) :=
      match input with
      | .node 0 [axiomTree] => do
          let ⟨_, certificate⟩ ← LogicalAxiomDecode.decode free axiomTree
          return pack (.logical_axiom certificate)
      | .node 1 [axiomTree] => do
          return pack (ProofCertificate.theory_axiom (axioms := axioms) (← decodeAxiom axiomTree))
      | .node 2 [premise, implication] => do
          modusPonens (← tree decodeAxiom free premise)
            (← tree decodeAxiom free implication)
      | .node 3 [premise] => do
          let ⟨_, certificate⟩ ← tree decodeAxiom (.set :: free) premise
          return pack (.forall_generalization certificate)
      | .node 4 [conclusionTree, premise] => do
          let conclusion ← SyntaxDecode.formula [] free conclusionTree
          let decoded ← tree decodeAxiom (.set :: free) premise
          match SyntaxDecode.formulaEq decoded.1 (conclusion.weakenFree SetSort.set) with
          | isTrue h => return pack (.free_strengthening (castProof h decoded.2))
          | isFalse _ => none
      | .node 5 [sourceTree, argumentsTree, premise] => do
          let source ← SyntaxDecode.context sourceTree
          let arguments ← SyntaxDecode.arguments [] free source argumentsTree
          let ⟨_, certificate⟩ ← tree decodeAxiom source premise
          return pack (.free_substitution (SyntaxDecode.substitution arguments) certificate)
      | _ => none

termination_by sizeOf input

/-- 自然数正向解码：格式、语法、公理及每条推导规则都检查成功才返回闭证书。 -/
def decode {T : SetTheory} {axioms : AxiomPresentation T} (decodeAxiom : AxiomDecoder axioms)
    (code : Nat) : Option (ClosedProofCertificate axioms) := do
  let input ← NatPacket.decode code
  let ⟨conclusion, proof⟩ ← tree decodeAxiom [] input
  return ⟨conclusion, proof⟩

/-- 可计算的自然数证明检查器。 -/
def check {T : SetTheory} {axioms : AxiomPresentation T} (decodeAxiom : AxiomDecoder axioms)
    (code : Nat) (formula : SetSentence) : Bool :=
  match decode decodeAxiom code with
  | none => false
  | some certificate => certificate.check formula

/-- 成功解码的闭证书可重放为原理论中的普通推导。 -/
theorem decode_sound {T : SetTheory} {axioms : AxiomPresentation T}
    (decodeAxiom : AxiomDecoder axioms) {code : Nat} {certificate : ClosedProofCertificate axioms}
    (_hDecoded : decode decodeAxiom code = some certificate) :
    Derives T [] certificate.conclusion := ⟨certificate.proof.replay⟩

/-- 检查器的接受结果可靠，拒绝分支不需要任何对象理论假设。 -/
theorem check_sound {T : SetTheory} {axioms : AxiomPresentation T}
    (decodeAxiom : AxiomDecoder axioms) {code : Nat} {formula : SetSentence}
    (hChecked : check decodeAxiom code formula = true) : Derives T [] formula := by
  unfold check at hChecked
  split at hChecked
  · contradiction
  · exact ClosedProofCertificate.check_sound hChecked

/-- 公开接受结果的精确含义，避免把 `none` 误读成不可证性。 -/
theorem check_eq_true_iff {T : SetTheory} {axioms : AxiomPresentation T}
    (decodeAxiom : AxiomDecoder axioms) (code : Nat) (formula : SetSentence) :
    check decodeAxiom code formula = true ↔
      ∃ certificate, decode decodeAxiom code = some certificate ∧ certificate.conclusion = formula := by
  unfold check
  cases h : decode decodeAxiom code with
  | none => simp
  | some certificate => simp [ClosedProofCertificate.check_eq_true_iff]
end NatDecode
end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT
