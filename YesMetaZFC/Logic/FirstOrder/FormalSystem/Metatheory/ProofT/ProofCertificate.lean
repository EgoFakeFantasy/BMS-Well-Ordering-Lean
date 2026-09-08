import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.AxiomPresentation

/-!
# 使用显式公理证书的有限推导

本层保留既有 Hilbert 核的全部规则，包括 free strengthening 与统一 free 替换。
理论公理行只携带 `AxiomPresentation.Certificate`，其可靠性由重放时的
`sound` 定理提供。双向转换证明说明没有因为更换公理行格式而缩小可证句子集。
这些仍是结构证书；自然数编解码和对象层正负表示不由本模块假定。
-/

namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT

open Nonlogical.BasicSetTheory QuineEncoding.SyntaxCoding

set_option autoImplicit false

/-- 与普通推导规则同形、但使用显式公理数据的有限证书。 -/
inductive ProofCertificate {T : SetTheory} (axioms : AxiomPresentation T) :
    (free : SetContext) → SetOpenFormula free → Type where
  | logical_axiom {free : SetContext} {formula : SetOpenFormula free}
      (certificate : HilbertBaseAxiom signature formula) :
      ProofCertificate axioms free formula
  | theory_axiom {free : SetContext} (certificate : axioms.Certificate) :
      ProofCertificate axioms free (Formula.fromSentence (axioms.sentence certificate))
  | modus_ponens {free : SetContext} {antecedent consequent : SetOpenFormula free}
      (premise : ProofCertificate axioms free antecedent)
      (implication : ProofCertificate axioms free (.imp antecedent consequent)) :
      ProofCertificate axioms free consequent
  | forall_generalization {free : SetContext} {sort : SetSort}
      {formula : SetOpenFormula (sort :: free)}
      (premise : ProofCertificate axioms (sort :: free) formula) :
      ProofCertificate axioms free (formula.forallFreeTop sort)
  | free_strengthening {free : SetContext} {sort : SetSort}
      {formula : SetOpenFormula free}
      (premise : ProofCertificate axioms (sort :: free) (formula.weakenFree sort)) :
      ProofCertificate axioms free formula
  | free_substitution {sourceFree targetFree : SetContext}
      (substitution : VariableSubstitution signature sourceFree [] targetFree)
      {formula : SetOpenFormula sourceFree}
      (premise : ProofCertificate axioms sourceFree formula) :
      ProofCertificate axioms targetFree (formula.substituteFree substitution)

namespace ProofCertificate

/-- 重放证书，只在公理行调用公理表示的可靠性定理。 -/
def replay {T : SetTheory} {axioms : AxiomPresentation T}
    {free : SetContext} {formula : SetOpenFormula free} :
    ProofCertificate axioms free formula → HilbertDerivation T free formula
  | .logical_axiom certificate => .logical_axiom certificate
  | .theory_axiom certificate => .theory_axiom (axioms.sound certificate)
  | .modus_ponens premise implication => .modus_ponens premise.replay implication.replay
  | .forall_generalization premise => .forall_generalization premise.replay
  | .free_strengthening premise => .free_strengthening premise.replay
  | .free_substitution substitution premise => .free_substitution substitution premise.replay

/-- 每个普通推导都有同一结论的显式公理证书推导。 -/
theorem complete {T : SetTheory} (axioms : AxiomPresentation T)
    {free : SetContext} {formula : SetOpenFormula free}
    (proof : HilbertDerivation T free formula) :
    Nonempty (ProofCertificate axioms free formula) := by
  induction proof with
  | logical_axiom certificate => exact ⟨.logical_axiom certificate⟩
  | theory_axiom hTheory =>
      obtain ⟨certificate, hCertificate⟩ := axioms.complete hTheory
      cases hCertificate
      exact ⟨.theory_axiom certificate⟩
  | modus_ponens _ _ ihPremise ihImplication =>
      obtain ⟨premise⟩ := ihPremise
      obtain ⟨implication⟩ := ihImplication
      exact ⟨.modus_ponens premise implication⟩
  | forall_generalization _ ih =>
      obtain ⟨premise⟩ := ih
      exact ⟨.forall_generalization premise⟩
  | free_strengthening _ ih =>
      obtain ⟨premise⟩ := ih
      exact ⟨.free_strengthening premise⟩
  | free_substitution substitution _ ih =>
      obtain ⟨premise⟩ := ih
      exact ⟨.free_substitution substitution premise⟩

/-- 证书存在性与原始可证性完全相同，适用于任意 free 上下文。 -/
theorem nonempty_iff_provable {T : SetTheory} (axioms : AxiomPresentation T)
    {free : SetContext} (formula : SetOpenFormula free) :
    Nonempty (ProofCertificate axioms free formula) ↔ Provable T formula := by
  constructor
  · rintro ⟨certificate⟩
    exact ⟨certificate.replay⟩
  · rintro ⟨proof⟩
    exact complete axioms proof

end ProofCertificate

/-- 可独立传递的闭证明证书，同时保存其实际结论。 -/
structure ClosedProofCertificate {T : SetTheory} (axioms : AxiomPresentation T) where
  conclusion : SetSentence
  proof : ProofCertificate axioms [] conclusion

namespace ClosedProofCertificate

/-- 闭证书的结论检查；结构证书的规则合法性由内在索引保证。 -/
def check {T : SetTheory} {axioms : AxiomPresentation T}
    (certificate : ClosedProofCertificate axioms) (formula : SetSentence) : Bool :=
  decide (formula_code certificate.conclusion = formula_code formula)

@[simp] theorem check_eq_true_iff {T : SetTheory} {axioms : AxiomPresentation T}
    (certificate : ClosedProofCertificate axioms) (formula : SetSentence) :
    certificate.check formula = true ↔ certificate.conclusion = formula := by
  simp only [check, decide_eq_true_eq]
  exact ⟨fun hCode => formula_code_injective hCode,
    fun hFormula => congrArg formula_code hFormula⟩

theorem check_sound {T : SetTheory} {axioms : AxiomPresentation T}
    {certificate : ClosedProofCertificate axioms} {formula : SetSentence}
    (hChecked : certificate.check formula = true) : Derives T [] formula := by
  have hConclusion := (certificate.check_eq_true_iff formula).mp hChecked
  cases hConclusion
  exact ⟨certificate.proof.replay⟩

theorem check_complete {T : SetTheory} (axioms : AxiomPresentation T)
    {formula : SetSentence} (hFormula : Derives T [] formula) :
    ∃ certificate : ClosedProofCertificate axioms, certificate.check formula = true := by
  obtain ⟨proof⟩ := hFormula
  obtain ⟨certificate⟩ := ProofCertificate.complete axioms proof
  exact ⟨⟨formula, certificate⟩, by simp⟩

end ClosedProofCertificate
end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT
