import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ProofTreeCode
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SyntaxCanonical

/-! # 局部证明节点的类型安全重放

子节点的可证性只能在其头部与所需上下文、公式完全相符后使用。
所有六类检查都直接重放原 Hilbert 核规则，不引入语义反射公理。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ProofTreeCode
open Nonlogical.BasicSetTheory IntrinsicQuotation
open _root_.YesMetaZFC.Automation.ObjectCodeProjection
set_option autoImplicit false

theorem readHeader_length {free : SetContext} {code : Nat} {formula : SetOpenFormula free}
    (h : readHeader free code = some formula) : field code 0 = free.length := by
  unfold readHeader at h
  split at h
  · assumption
  · cases h

theorem readHeader_value {free : SetContext} {code : Nat} {formula : SetOpenFormula free}
    (h : readHeader free code = some formula) : treeValue (SyntaxEncode.formula formula) = field code 1 := by
  unfold readHeader at h
  split at h
  · obtain ⟨input, hInput, hFormula⟩ := Option.bind_eq_some_iff.mp h
    rw [SyntaxDecode.formula_encode_of_decode [] free input formula hFormula]
    exact treeValue_of_decode hInput
  · cases h

def HeaderProvable (T : SetTheory) (code : Nat) : Prop :=
  ∃ formula : SetOpenFormula (List.replicate (field code 0) SetSort.set),
    readHeader _ code = some formula ∧ Provable T formula

theorem HeaderProvable.use {T : SetTheory} {code : Nat} (h : HeaderProvable T code)
    {free : SetContext} {formula : SetOpenFormula free} (hRead : readHeader free code = some formula) :
    Provable T formula := by
  have hLength := readHeader_length hRead
  unfold HeaderProvable at h
  rw [hLength, context_of_length] at h
  obtain ⟨actual, hActual, hProof⟩ := h
  have hEq : actual = formula := Option.some.inj (hActual.symm.trans hRead)
  exact hEq ▸ hProof

def childCodes (code : Nat) : List Nat :=
  match tag code with
  | 2 => [field code 2, field code 3]
  | 3 | 4 => [field code 2]
  | 5 => [field code 4]
  | _ => []

theorem localCheck_eq_true {T : SetTheory} {axioms : AxiomPresentation T} (decoder : AxiomDecoder axioms)
    (code : Nat) : localCheck decoder code = true ↔ localRun decoder code = some true := by
  unfold localCheck
  cases localRun decoder code <;> simp

/-- 任意数码节点的局部检查成功且所指子证明可靠，则该节点本身可靠。 -/
theorem localCheck_sound {T : SetTheory} {axioms : AxiomPresentation T} (decoder : AxiomDecoder axioms)
    (code : Nat) (h : localCheck decoder code = true)
    (children : ∀ child, child ∈ childCodes code → HeaderProvable T child) : HeaderProvable T code := by
  have hRun := (localCheck_eq_true decoder code).mp h
  unfold localRun at hRun
  dsimp only at hRun
  obtain ⟨conclusion, hConclusion, hStep⟩ := Option.bind_eq_some_iff.mp hRun
  refine ⟨conclusion, hConclusion, ?_⟩
  split at hStep
  · rename_i hTag
    obtain ⟨input, hInput, hRest⟩ := Option.bind_eq_some_iff.mp hStep
    obtain ⟨certificate, hCertificate, hResult⟩ := Option.bind_eq_some_iff.mp hRest
    have hEq : certificate.1 = conclusion := (formulaEqual_eq_true _ _).mp (Option.some.inj hResult)
    exact hEq ▸ Provable.logical_axiom certificate.2
  · rename_i hTag
    obtain ⟨input, hInput, hRest⟩ := Option.bind_eq_some_iff.mp hStep
    obtain ⟨certificate, hCertificate, hResult⟩ := Option.bind_eq_some_iff.mp hRest
    have hEq : Formula.fromSentence (axioms.sentence certificate) = conclusion :=
      (formulaEqual_eq_true _ _).mp (Option.some.inj hResult)
    exact hEq ▸ Provable.theory_axiom (axioms.sound certificate)
  · rename_i hTag
    obtain ⟨premise, hPremise, hRest⟩ := Option.bind_eq_some_iff.mp hStep
    obtain ⟨implication, hImplication, hResult⟩ := Option.bind_eq_some_iff.mp hRest
    cases implication <;> try cases hResult
    rename_i antecedent consequent
    obtain ⟨hLeft, hRight⟩ := Bool.and_eq_true_iff.mp (Option.some.inj hResult)
    have hLeft := (formulaEqual_eq_true _ _).mp hLeft
    have hRight := (formulaEqual_eq_true _ _).mp hRight
    have hP := (children (field code 2) (by simp [childCodes, hTag])).use hPremise
    have hQ := (children (field code 3) (by simp [childCodes, hTag])).use hImplication
    exact hRight ▸ Provable.modus_ponens (hLeft ▸ hP) hQ
  · rename_i hTag
    obtain ⟨premise, hPremise, hResult⟩ := Option.bind_eq_some_iff.mp hStep
    have hEq := (formulaEqual_eq_true _ _).mp (Option.some.inj hResult)
    have hP := (children (field code 2) (by simp [childCodes, hTag])).use hPremise
    exact hEq ▸ Provable.forall_generalization (σ := signature) (T := T)
      (free := List.replicate (field code 0) SetSort.set) (sort := SetSort.set) (formula := premise) hP
  · rename_i hTag
    obtain ⟨premise, hPremise, hResult⟩ := Option.bind_eq_some_iff.mp hStep
    have hEq := (formulaEqual_eq_true _ _).mp (Option.some.inj hResult)
    have hP := (children (field code 2) (by simp [childCodes, hTag])).use hPremise
    exact Provable.free_strengthening (sort := SetSort.set) (hEq ▸ hP)
  · rename_i hTag
    obtain ⟨trees, hTrees, hRest⟩ := Option.bind_eq_some_iff.mp hStep
    obtain ⟨args, hArgs, hRest⟩ := Option.bind_eq_some_iff.mp hRest
    obtain ⟨premise, hPremise, hResult⟩ := Option.bind_eq_some_iff.mp hRest
    have hEq := (formulaEqual_eq_true _ _).mp (Option.some.inj hResult)
    have hP := (children (field code 4) (by simp [childCodes, hTag])).use hPremise
    exact hEq ▸ Provable.free_substitution (SyntaxDecode.substitution args) hP
  · cases hStep

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ProofTreeCode
