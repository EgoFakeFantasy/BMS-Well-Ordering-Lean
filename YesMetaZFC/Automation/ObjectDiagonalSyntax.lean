import YesMetaZFC.Automation.ObjectNumeralSyntax
import YesMetaZFC.Automation.ObjectSyntaxTransformConcrete

/-! # 当前 quotation 的单变量数码自代入关系

先构造 numeral 项码，再用完整同时自由代入图执行单槽代入。这里给出固定
三元模板及任意候选输出的正负推导，最小见证层另行完成对象唯一性。
-/
namespace YesMetaZFC.Automation.ObjectDiagonal
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT IntrinsicQuotation QuineEncoding ObjectHorn
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000

abbrev UnaryFormula := SetOpenFormula [SetSort.set]
def code (body : UnaryFormula) : Nat := treeValue (SyntaxEncode.formula body)
def instantiate (body : UnaryFormula) (number : Nat) : SetSentence :=
  body.substituteFree (VariableSubstitution.cons (numₘ(number)) VariableSubstitution.empty)
def value (body : UnaryFormula) (number : Nat) : Nat := treeValue (SyntaxEncode.formula (instantiate body number))

/-- 已有支撑公理的具体能力包；没有加入任何额外理论公理。 -/
structure Support (T : SetTheory) where
  certificate : CertificateCore T
  core : Core T
  sequences : FiniteSequenceGraphSupport T
  power : ∀ {φ}, power_set_operator_theory φ → T φ
  infinity : ∀ {φ}, infinity_theory φ → T φ
  numeral_domain : ∀ number, Derives T [] (core.code_domain.condition (numₘ(number) : Code))

def numeral : FormulaTemplate.Ternary where
  body := ObjectNumeralSyntax.condition (.fvar .here) (.fvar (.there (.there .here)))
@[simp] theorem numeral_apply {bound free : SetContext} (input parameter output : SetTerm bound free) :
    numeral input parameter output = ObjectNumeralSyntax.condition input output := by
  simp [numeral, FormulaTemplate.apply_three, FormulaTemplate.instantiate,
    Term.substituteMapped, VariableSubstitution.cons]

def substitutionCondition {bound free : SetContext} (input parameter output : SetTerm bound free) : SetFormula bound free :=
  ObjectSyntaxTransform.condition (numₘ(3)) (numₘ(0)) (structural_list_code_term [parameter]) input output
@[simp] theorem substitutionCondition_substituteMapped {sb sf tb tf : SetContext}
    (input parameter output : SetTerm sb sf) (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf) :
    (substitutionCondition input parameter output).substituteMapped bs fs =
      substitutionCondition (input.substituteMapped bs fs) (parameter.substituteMapped bs fs) (output.substituteMapped bs fs) := by
  simp [substitutionCondition]

def substitution : FormulaTemplate.Ternary where
  body := substitutionCondition (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
@[simp] theorem substitution_apply {bound free : SetContext} (input parameter output : SetTerm bound free) :
    substitution input parameter output = substitutionCondition input parameter output := by
  simp [substitution, FormulaTemplate.apply_three, FormulaTemplate.instantiate,
    Term.substituteMapped, VariableSubstitution.cons]

private theorem singleton_row {T : SetTheory} (C : CertificateCore T) (input parameter output : Nat) :
    Derives T ([] : Context signature []) (IntrinsicQuotation.node 3 [numₘ(3), numₘ(0), numₘ(listValue [parameter]), numₘ(input), numₘ(output)] ≐ₘ
      IntrinsicQuotation.node 3 [numₘ(3), numₘ(0), structural_list_code_term [numₘ(parameter)] , numₘ(input), numₘ(output)]) :=
  node_congr 3 (.cons (Metatheory.Derives.equality_refl _)
    (.cons (Metatheory.Derives.equality_refl _)
      (.cons (FirstOrder.Derives.eq_symm (numeral_list_evaluate C [parameter]))
        (.cons (Metatheory.Derives.equality_refl _) (.cons (Metatheory.Derives.equality_refl _) .nil)))))

private theorem substitution_checked (body : UnaryFormula) (number output : Nat) :
    ObjectSyntaxTransform.checked 3 0 (listValue [ObjectNumeralSyntax.value number]) (code body) output = true ↔
      value body number = output := by
  simpa only [code, value, instantiate, ObjectNumeralSyntax.value_encode, SyntaxEncode.substitutionArguments,
    SyntaxEncode.argumentsList, VariableSubstitution.cons, List.map_cons, List.map_nil]
    using ObjectSyntaxTransform.checked_substituteFree body
      (VariableSubstitution.cons (numₘ(number) : Code) VariableSubstitution.empty) output

theorem numeral_positive {T : SetTheory} (S : Support T) (number : Nat) :
    Derives T [] (numeral (numₘ(number)) (numₘ(0)) (numₘ(ObjectNumeralSyntax.value number) : Code)) := by
  rw [numeral_apply]
  exact ObjectNumeralSyntax.positive S.certificate S.sequences S.power S.infinity number

theorem numeral_negative {T : SetTheory} (S : Support T) (number output : Nat) (h : ObjectNumeralSyntax.value number ≠ output) :
    Derives T [] (¬ₘ numeral (numₘ(number)) (numₘ(0)) (numₘ(output) : Code)) := by
  rw [numeral_apply]
  exact ObjectNumeralSyntax.negative S.certificate S.sequences.toArithmeticSupport number output h

theorem substitution_positive {T : SetTheory} (S : Support T) (body : UnaryFormula) (number : Nat) :
    Derives T [] (substitution (numₘ(code body)) (numₘ(ObjectNumeralSyntax.value number)) (numₘ(value body number) : Code)) := by
  rw [substitution_apply]
  change Derives T [] (ObjectHorn.condition ObjectSyntaxTransform.rules _)
  have h := ObjectSyntaxTransform.positive S.certificate S.sequences S.power S.infinity _ _ _ _ _
    ((substitution_checked body number _).mpr rfl)
  exact ObjectHorn.transport ObjectSyntaxTransform.rules
    (singleton_row S.certificate (code body) (ObjectNumeralSyntax.value number) (value body number)) h

theorem substitution_negative {T : SetTheory} (S : Support T) (body : UnaryFormula) (number output : Nat)
    (h : value body number ≠ output) :
    Derives T [] (¬ₘ substitution (numₘ(code body)) (numₘ(ObjectNumeralSyntax.value number)) (numₘ(output) : Code)) := by
  rw [substitution_apply]
  change Derives T [] (¬ₘ ObjectHorn.condition ObjectSyntaxTransform.rules _)
  have hCheck : ObjectSyntaxTransform.checked 3 0 (listValue [ObjectNumeralSyntax.value number]) (code body) output = false :=
    Bool.eq_false_iff.mpr (fun hTrue => h ((substitution_checked body number output).mp hTrue))
  have h := ObjectSyntaxTransform.negative S.certificate S.sequences.toArithmeticSupport _ _ _ _ _ hCheck
  exact ObjectHorn.transport_negative ObjectSyntaxTransform.rules
    (singleton_row S.certificate (code body) (ObjectNumeralSyntax.value number) output) h

end YesMetaZFC.Automation.ObjectDiagonal
