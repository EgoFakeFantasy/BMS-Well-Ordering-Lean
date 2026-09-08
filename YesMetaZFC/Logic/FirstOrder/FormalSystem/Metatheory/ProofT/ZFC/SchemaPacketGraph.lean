import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaPacketData

/-! # 模式传输包到内核 quotation 的固定二元对象公式 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaPacket
open Nonlogical.BasicSetTheory QuineEncoding NatPacket IntrinsicQuotation
open _root_.YesMetaZFC.Automation ObjectHorn ObjectArithmeticTerm
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def checks {bound free : SetContext} (tag : Nat) (kind : SchemaTemplate.Kind)
    (env : Fin 3 → SetTerm bound free) (packet output : SetTerm bound free) : List (SetFormula bound free) :=
  [ObjectPacket.condition packet (env 0), SchemaEnvelope.link tag (env 0) (env 1) (env 2),
    SchemaKernelJoin.condition kind (env 1) (env 2) output]

def matrix {bound free : SetContext} (tag : Nat) (kind : SchemaTemplate.Kind)
    (env : Fin 3 → SetTerm bound free) (packet output : SetTerm bound free) : SetFormula bound free :=
  allOf (checks tag kind env packet output)

theorem matrix_delta0 {bound free : SetContext} (tag : Nat) (kind : SchemaTemplate.Kind)
    (env : Fin 3 → SetTerm bound free) (packet output : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound (matrix tag kind env packet output) := by
  apply allOf_delta0
  intro φ hφ
  simp only [checks, List.mem_cons, List.not_mem_nil, or_false] at hφ
  rcases hφ with rfl | rfl | rfl
  · exact ObjectPacket.condition_delta0 _ _
  · exact .equal _ _
  · exact SchemaKernelJoin.condition_delta0 _ _ _ _

@[simp] theorem matrix_substituteMapped {sb sf tb tf : SetContext} (tag : Nat) (kind : SchemaTemplate.Kind)
    (env : Fin 3 → SetTerm sb sf) (packet output : SetTerm sb sf)
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf) :
    (matrix tag kind env packet output).substituteMapped bs fs =
      matrix tag kind (fun i => (env i).substituteMapped bs fs)
        (packet.substituteMapped bs fs) (output.substituteMapped bs fs) := by
  simp [matrix, checks, ObjectPacket.condition]

def boundedTemplate (tag : Nat) (kind : SchemaTemplate.Kind) : FormulaTemplate.Ternary where
  body := quantify 3 (.fvar .here)
    (matrix tag kind (fun i => .bvar (project_bound_variable i))
      (.fvar (.there .here)) (.fvar (.there (.there .here))))

def bounded {bound free : SetContext} (tag : Nat) (kind : SchemaTemplate.Kind)
    (limit packet output : SetTerm bound free) : SetFormula bound free :=
  boundedTemplate tag kind limit packet output

@[simp] theorem bounded_substituteMapped {sb sf tb tf : SetContext} (tag : Nat) (kind : SchemaTemplate.Kind)
    (limit packet output : SetTerm sb sf) (bs : VariableSubstitution signature sb tb tf)
    (fs : VariableSubstitution signature sf tb tf) :
    (bounded tag kind limit packet output).substituteMapped bs fs = bounded tag kind
      (limit.substituteMapped bs fs) (packet.substituteMapped bs fs) (output.substituteMapped bs fs) := by
  simp only [bounded, FormulaTemplate.apply_three, FormulaTemplate.instantiate_substituteMapped]
  congr 1
  funext sort v
  cases v with
  | here => rfl
  | there v => cases v with
    | here => rfl
    | there v => cases v with
      | here => rfl
      | there v => cases v

def limitTerm {bound free : SetContext} (packet : SetTerm bound free) : SetTerm bound free := Sₘ(tableBound packet)

def branch {bound free : SetContext} (tag : Nat) (kind : SchemaTemplate.Kind)
    (packet output : SetTerm bound free) : SetFormula bound free :=
  bounded tag kind (limitTerm packet) packet output

def condition {bound free : SetContext} (packet output : SetTerm bound free) : SetFormula bound free :=
  anyOf (entries.map (fun entry => branch entry.1 entry.2 packet output))

@[simp] theorem condition_substituteMapped {sb sf tb tf : SetContext} (packet output : SetTerm sb sf)
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf) :
    (condition packet output).substituteMapped bs fs =
      condition (packet.substituteMapped bs fs) (output.substituteMapped bs fs) := by
  simp [condition, branch, limitTerm, tableBound, Function.comp_def,
    Term.substituteMapped, Arguments.substituteMapped]

def template : FormulaTemplate.Binary where
  body := condition (.fvar .here) (.fvar (.there .here))

@[simp] theorem template_apply {bound free : SetContext} (packet output : SetTerm bound free) :
    template packet output = condition packet output := by
  simp [template, FormulaTemplate.apply_two, FormulaTemplate.instantiate,
    Term.substituteMapped, VariableSubstitution.cons]

theorem condition_delta0 {bound free : SetContext} (packet output : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound (condition packet output) := by
  apply anyOf_delta0
  intro φ hφ
  obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hφ
  exact FormulaTemplate.instantiate_delta0 _ (quantify_delta0 _ _ _ (matrix_delta0 _ _ _ _ _)) _

theorem template_delta0 : Formula.IsDelta0 set_levy_bound template.body := condition_delta0 _ _

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaPacket
