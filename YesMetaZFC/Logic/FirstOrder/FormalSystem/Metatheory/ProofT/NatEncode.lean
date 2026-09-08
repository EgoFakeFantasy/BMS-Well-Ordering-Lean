import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.NatDecode
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.LogicalAxiomEncode
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.AxiomEncode
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.NatPacketRoundtrip

/-! # 有限证明证书的自然数逆向编码 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatEncode
open Nonlogical.BasicSetTheory NatPacket
set_option autoImplicit false

/-- 编码全部六条普通推导规则，不从可证性命题中作经典选择。 -/
def tree {T : SetTheory} {axioms : AxiomPresentation T} {decoder : AxiomDecoder axioms}
    (codec : AxiomCodec decoder) : {free : SetContext} → {formula : SetOpenFormula free} →
    ProofCertificate axioms free formula → Tree
  | _, _, .logical_axiom certificate => .node 0 [LogicalAxiomEncode.encode certificate]
  | _, _, .theory_axiom certificate => .node 1 [codec.encode certificate]
  | _, _, .modus_ponens premise implication => .node 2 [tree codec premise, tree codec implication]
  | _, _, .forall_generalization premise => .node 3 [tree codec premise]
  | _, formula, .free_strengthening premise => .node 4 [SyntaxEncode.formula formula, tree codec premise]
  | _, _, @ProofCertificate.free_substitution _ _ source _ subst _ premise =>
      .node 5 [SyntaxEncode.context source,
        SyntaxEncode.arguments (SyntaxEncode.substitutionArguments source subst), tree codec premise]

@[simp] theorem formulaEq_self {bound free : SetContext} (formula : SetFormula bound free) :
    SyntaxDecode.formulaEq formula formula = isTrue rfl := by
  cases h : SyntaxDecode.formulaEq formula formula with
  | isTrue hEq => rfl
  | isFalse hNe => exact False.elim (hNe rfl)

private theorem mp_roundtrip {T : SetTheory} {axioms : AxiomPresentation T} {free : SetContext}
    {a b : SetOpenFormula free} (p : ProofCertificate axioms free a)
    (q : ProofCertificate axioms free (.imp a b)) :
    NatDecode.modusPonens ⟨a, p⟩ ⟨.imp a b, q⟩ = some ⟨b, .modus_ponens p q⟩ := by
  unfold NatDecode.modusPonens
  split
  · rename_i implication antecedent consequent certificate h
    injection h with hFormula hCertificate
    injection hFormula with hAntecedent hConsequent
    subst antecedent consequent
    cases hCertificate
    rw [formulaEq_self]
    rfl
  · rename_i implication h
    exact False.elim (h a b q rfl)

/-- 树级往返保留整个证书，而不只是保留其结论。 -/
@[simp] theorem tree_roundtrip {T : SetTheory} {axioms : AxiomPresentation T}
    {decoder : AxiomDecoder axioms} (codec : AxiomCodec decoder)
    {free : SetContext} {formula : SetOpenFormula free} (certificate : ProofCertificate axioms free formula) :
    NatDecode.tree decoder free (tree codec certificate) = some ⟨formula, certificate⟩ := by
  induction certificate with
  | logical_axiom certificate =>
      rw [tree, NatDecode.tree.eq_def]
      change (LogicalAxiomDecode.decode _ (LogicalAxiomEncode.encode certificate)).bind
        (fun p => some (NatDecode.pack (ProofCertificate.logical_axiom (axioms := axioms) p.2))) = _
      rw [LogicalAxiomEncode.roundtrip]; rfl
  | theory_axiom certificate =>
      rw [tree, NatDecode.tree.eq_def]
      change (decoder (codec.encode certificate)).bind
        (fun c => some (NatDecode.pack (ProofCertificate.theory_axiom (axioms := axioms) c))) = _
      rw [codec.roundtrip]; rfl
  | modus_ponens premise implication ihPremise ihImplication =>
      rw [tree, NatDecode.tree.eq_def]
      change (NatDecode.tree decoder _ (tree codec premise)).bind
        (fun p => (NatDecode.tree decoder _ (tree codec implication)).bind (fun q => NatDecode.modusPonens p q)) = _
      rw [ihPremise]
      change (NatDecode.tree decoder _ (tree codec implication)).bind (fun q => NatDecode.modusPonens ⟨_, premise⟩ q) = _
      rw [ihImplication]
      exact mp_roundtrip premise implication
  | forall_generalization premise ih =>
      cases ‹SetSort›
      rw [tree, NatDecode.tree.eq_def]
      change (NatDecode.tree decoder _ (tree codec premise)).bind
        (fun p => some (NatDecode.pack (ProofCertificate.forall_generalization (axioms := axioms) p.2))) = _
      rw [ih]; rfl
  | @free_strengthening free sort formula premise ih =>
      cases sort
      rw [tree, NatDecode.tree.eq_def]
      change (SyntaxDecode.formula [] free (SyntaxEncode.formula formula)).bind
        (fun conclusion => (NatDecode.tree decoder _ (tree codec premise)).bind
          (fun decoded => match SyntaxDecode.formulaEq decoded.1 (conclusion.weakenFree SetSort.set) with
            | isTrue h => some (NatDecode.pack (.free_strengthening (NatDecode.castProof h decoded.2)))
            | isFalse _ => none)) = _
      rw [SyntaxEncode.formula_roundtrip]
      dsimp only [Option.bind_some]
      rw [ih]
      dsimp only [Option.bind_some]
      rw [formulaEq_self]
      rfl
  | @free_substitution source target subst formula premise ih =>
      rw [tree, NatDecode.tree.eq_def]
      change (SyntaxDecode.context (SyntaxEncode.context source)).bind
        (fun source' => (SyntaxDecode.arguments [] target source'
          (SyntaxEncode.arguments (SyntaxEncode.substitutionArguments source subst))).bind
          (fun args => (NatDecode.tree decoder source' (tree codec premise)).bind
            (fun p => some (NatDecode.pack (.free_substitution (SyntaxDecode.substitution args) p.2))))) = _
      rw [SyntaxEncode.context_roundtrip]
      dsimp only [Option.bind_some]
      rw [SyntaxEncode.arguments_roundtrip]
      dsimp only [Option.bind_some]
      rw [ih]
      dsimp only [Option.bind_some]
      rw [SyntaxEncode.substitution_roundtrip]
      rfl

def encode {T : SetTheory} {axioms : AxiomPresentation T} {decoder : AxiomDecoder axioms}
    (codec : AxiomCodec decoder) (certificate : ClosedProofCertificate axioms) : Nat :=
  NatPacket.encode (tree codec certificate.proof)

@[simp] theorem decode_encode {T : SetTheory} {axioms : AxiomPresentation T}
    {decoder : AxiomDecoder axioms} (codec : AxiomCodec decoder) (certificate : ClosedProofCertificate axioms) :
    NatDecode.decode decoder (encode codec certificate) = some certificate := by
  unfold encode NatDecode.decode
  rw [NatPacket.decode_encode]
  change (NatDecode.tree decoder [] (tree codec certificate.proof)).bind
    (fun p => some (ClosedProofCertificate.mk p.1 p.2)) = some certificate
  rw [tree_roundtrip]
  cases certificate
  rfl

@[simp] theorem check_encode {T : SetTheory} {axioms : AxiomPresentation T}
    {decoder : AxiomDecoder axioms} (codec : AxiomCodec decoder) (certificate : ClosedProofCertificate axioms) :
    NatDecode.check decoder (encode codec certificate) certificate.conclusion = true := by
  unfold NatDecode.check
  rw [decode_encode]
  exact (ClosedProofCertificate.check_eq_true_iff certificate certificate.conclusion).mpr rfl

/-- 每个原理论推导都给出可接受的自然数证明码。 -/
theorem check_complete {T : SetTheory} {axioms : AxiomPresentation T}
    {decoder : AxiomDecoder axioms} (codec : AxiomCodec decoder)
    {formula : SetSentence} (h : Derives T [] formula) :
    ∃ code, NatDecode.check decoder code formula = true := by
  obtain ⟨certificate, hChecked⟩ := ClosedProofCertificate.check_complete axioms h
  have hConclusion := (ClosedProofCertificate.check_eq_true_iff certificate formula).mp hChecked
  exact ⟨encode codec certificate, hConclusion ▸ check_encode codec certificate⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatEncode
