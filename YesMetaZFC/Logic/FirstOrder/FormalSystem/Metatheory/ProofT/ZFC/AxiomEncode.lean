import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.AxiomDecode
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicAxiomEncode

/-! # ZFC schema 的逆向编码及完整理论公理往返 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open Nonlogical.BasicSetTheory NatPacket
open _root_.YesMetaZFC.SetTheory
open _root_.YesMetaZFC.SetTheory.Definitional
set_option autoImplicit false
namespace ProjectEncode

def term {depth : Nat} : Project.Term depth → Tree
  | .bound entry => .node 0 [leaf entry.val]
  | .free id => .node 1 [leaf id]

@[simp] theorem term_roundtrip {depth : Nat} (input : Project.Term depth)
    (hClosed : input.freeSupport = []) : ProjectDecode.term depth (term input) = some input := by
  cases input with
  | bound entry => simp [term, ProjectDecode.term, scalar, leaf, entry.isLt]
  | free id => cases hClosed

theorem pairArguments_eta {depth : Nat} (args : TermVector 2 depth) :
    Project.Formula.pairArguments (args 0) (args 1) = args := by
  have h : (Project.Formula.pairArguments (args 0) (args 1)).terms = args.terms := by
    apply Array.ext
    · exact args.size_eq.symm
    · intro i hi hj
      have hIndex : i < 2 := by simpa [args.size_eq] using hj
      have hCases : i = 0 ∨ i = 1 := by omega
      rcases hCases with rfl | rfl <;> rfl
  have ext : ∀ (left right : TermVector 2 depth), left.terms = right.terms → left = right := by
    intro ⟨left, hLeft⟩ ⟨right, hRight⟩ hEq
    cases hEq
    rfl
  exact ext _ _ h

def formula {depth : Nat} : Project.Formula 1 depth → Tree
  | .falsum => leaf 0
  | .truth => leaf 1
  | .mem left right => .node 2 [term left, term right]
  | .atom .extensionalEq _ args => .node 3 [term (args 0), term (args 1)]
  | .atom .subset _ args => .node 11 [term (args 0), term (args 1)]
  | .neg body => .node 4 [formula body]
  | .conj left right => .node 5 [formula left, formula right]
  | .disj left right => .node 6 [formula left, formula right]
  | .imp left right => .node 7 [formula left, formula right]
  | .iff left right => .node 8 [formula left, formula right]
  | .forallE body => .node 9 [formula body]
  | .existsE body => .node 10 [formula body]

@[simp] theorem formula_roundtrip {depth : Nat} (input : Project.Formula 1 depth)
    (hClosed : input.FreeClosed) : ProjectDecode.formula depth (formula input) = some input := by
  induction input with
  | falsum => rw [formula, leaf, ProjectDecode.formula.eq_def]; rfl
  | truth => rw [formula, leaf, ProjectDecode.formula.eq_def]; rfl
  | mem left right =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      rw [formula, ProjectDecode.formula.eq_def]
      change (ProjectDecode.term _ (term left)).bind (fun l => (ProjectDecode.term _ (term right)).bind (fun r => some (Definitional.Formula.mem (σ := Project.coreSignature) (availableStage := 1) l r))) = _
      rw [term_roundtrip left hClosed.1]
      change (ProjectDecode.term _ (term right)).bind (fun r => some (Definitional.Formula.mem (σ := Project.coreSignature) (availableStage := 1) left r)) = _
      rw [term_roundtrip right hClosed.2]
      rfl
  | atom symbol hStage args =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      unfold TermVector.FreeClosed at hClosed
      cases symbol <;> rw [formula, ProjectDecode.formula.eq_def]
      all_goals
        change (ProjectDecode.term _ (term (args 0))).bind (fun l => (ProjectDecode.term _ (term (args 1))).bind (fun r => some _)) = _
        rw [term_roundtrip (args 0) (hClosed 0)]
        dsimp only [Option.bind_some]
        rw [term_roundtrip (args 1) (hClosed 1)]
        dsimp only [Option.bind_some, Option.pure_def, Project.Formula.extensionalEq, Project.Formula.subset]
        rw [pairArguments_eta]
  | neg body ih =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      rw [formula, ProjectDecode.formula.eq_def]
      change (ProjectDecode.formula _ (formula body)).bind (fun b => some (Definitional.Formula.neg (σ := Project.coreSignature) (availableStage := 1) b)) = _
      rw [ih hClosed]; rfl
  | conj left right ihLeft ihRight =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      rw [formula, ProjectDecode.formula.eq_def]
      change (ProjectDecode.formula _ (formula left)).bind (fun l => (ProjectDecode.formula _ (formula right)).bind (fun r => some (Definitional.Formula.conj (σ := Project.coreSignature) (availableStage := 1) l r))) = _
      rw [ihLeft hClosed.1]
      change (ProjectDecode.formula _ (formula right)).bind (fun r => some (Definitional.Formula.conj (σ := Project.coreSignature) (availableStage := 1) left r)) = _
      rw [ihRight hClosed.2]; rfl
  | disj left right ihLeft ihRight =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      rw [formula, ProjectDecode.formula.eq_def]
      change (ProjectDecode.formula _ (formula left)).bind (fun l => (ProjectDecode.formula _ (formula right)).bind (fun r => some (Definitional.Formula.disj (σ := Project.coreSignature) (availableStage := 1) l r))) = _
      rw [ihLeft hClosed.1]
      change (ProjectDecode.formula _ (formula right)).bind (fun r => some (Definitional.Formula.disj (σ := Project.coreSignature) (availableStage := 1) left r)) = _
      rw [ihRight hClosed.2]; rfl
  | imp left right ihLeft ihRight =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      rw [formula, ProjectDecode.formula.eq_def]
      change (ProjectDecode.formula _ (formula left)).bind (fun l => (ProjectDecode.formula _ (formula right)).bind (fun r => some (Definitional.Formula.imp (σ := Project.coreSignature) (availableStage := 1) l r))) = _
      rw [ihLeft hClosed.1]
      change (ProjectDecode.formula _ (formula right)).bind (fun r => some (Definitional.Formula.imp (σ := Project.coreSignature) (availableStage := 1) left r)) = _
      rw [ihRight hClosed.2]; rfl
  | iff left right ihLeft ihRight =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      rw [formula, ProjectDecode.formula.eq_def]
      change (ProjectDecode.formula _ (formula left)).bind (fun l => (ProjectDecode.formula _ (formula right)).bind (fun r => some (Definitional.Formula.iff (σ := Project.coreSignature) (availableStage := 1) l r))) = _
      rw [ihLeft hClosed.1]
      change (ProjectDecode.formula _ (formula right)).bind (fun r => some (Definitional.Formula.iff (σ := Project.coreSignature) (availableStage := 1) left r)) = _
      rw [ihRight hClosed.2]; rfl
  | forallE body ih =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      rw [formula, ProjectDecode.formula.eq_def]
      change (ProjectDecode.formula _ (formula body)).bind (fun b => some (Definitional.Formula.forallE (σ := Project.coreSignature) (availableStage := 1) b)) = _
      rw [ih hClosed]; rfl
  | existsE body ih =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      rw [formula, ProjectDecode.formula.eq_def]
      change (ProjectDecode.formula _ (formula body)).bind (fun b => some (Definitional.Formula.existsE (σ := Project.coreSignature) (availableStage := 1) b)) = _
      rw [ih hClosed]; rfl

@[simp] theorem unary_roundtrip {count : Nat} (schema : Project.UnarySchema count) :
    ProjectDecode.unarySchema count (formula schema.body) = some schema := by
  unfold ProjectDecode.unarySchema
  rw [formula_roundtrip schema.body schema.freeClosed]
  change (if h : schema.body.FreeClosed then some ⟨schema.body, h⟩ else none) = some schema
  rw [dif_pos schema.freeClosed]

@[simp] theorem binary_roundtrip {count : Nat} (schema : Project.BinarySchema count) :
    ProjectDecode.binarySchema count (formula schema.body) = some schema := by
  unfold ProjectDecode.binarySchema
  rw [formula_roundtrip schema.body schema.freeClosed]
  change (if h : schema.body.FreeClosed then some ⟨schema.body, h⟩ else none) = some schema
  rw [dif_pos schema.freeClosed]
end ProjectEncode

def zfc_base_axiom_encode : ZFCAxiomCertificate → Tree
  | .extensionality => leaf 0
  | .emptySet => leaf 1
  | .pairing => leaf 2
  | .union => leaf 3
  | .powerSet => leaf 4
  | .infinity => leaf 5
  | .foundation => leaf 6
  | .choice => leaf 7
  | @ZFCAxiomCertificate.separation count schema => .node 8 [leaf count, ProjectEncode.formula schema.body]
  | @ZFCAxiomCertificate.collection count schema => .node 9 [leaf count, ProjectEncode.formula schema.body]

@[simp] theorem zfc_base_axiom_roundtrip (certificate : ZFCAxiomCertificate) :
    zfc_base_axiom_decode (zfc_base_axiom_encode certificate) = some certificate := by
  cases certificate with
  | extensionality => rfl
  | emptySet => rfl
  | pairing => rfl
  | union => rfl
  | powerSet => rfl
  | infinity => rfl
  | foundation => rfl
  | choice => rfl
  | separation schema =>
      change (ProjectDecode.unarySchema _ (ProjectEncode.formula schema.body)).bind (fun s => some (ZFCAxiomCertificate.separation s)) = _
      rw [ProjectEncode.unary_roundtrip]
      rfl
  | collection schema =>
      change (ProjectDecode.binarySchema _ (ProjectEncode.formula schema.body)).bind (fun s => some (ZFCAxiomCertificate.collection s)) = _
      rw [ProjectEncode.binary_roundtrip]
      rfl

def zfc_base_axiom_codec :
    AxiomCodec (presentation := intrinsic_zfc_base_axiom_presentation) zfc_base_axiom_decode where
  encode := zfc_base_axiom_encode
  roundtrip := zfc_base_axiom_roundtrip

def intrinsic_zfc_axiom_codec : AxiomCodec intrinsic_zfc_axiom_decode :=
  AxiomCodec.union zfc_base_axiom_codec intrinsic_proof_axiom_codec
end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
