import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SupportTemplate
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteAxiomBasis

/-! # 参数支撑公理族由单一全称模板生成

参数证书中的自由上下文和项深度均任意。先打开模板闭包、执行类型化项代入，
再关闭实际自由上下文，因此无需把每次实例装配重新编译为对象计算图。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.SupportAssembly
open Nonlogical.BasicSetTheory SupportParameters
set_option autoImplicit false

def closedTemplate (kind : Kind) : SetSentence := Metatheory.Formula.forall_close (template kind)

def parameterTheory (kind : Kind) : SetTheory :=
  fun φ => ∃ parameters : SyntaxParameters.Parameters kind.arity, sentence kind parameters = φ

theorem template_member (kind : Kind) : parameterTheory kind (closedTemplate kind) :=
  ⟨⟨List.replicate kind.arity SetSort.set,
    SyntaxEncode.substitutionArguments _ VariableSubstitution.freeId⟩, rfl⟩

/-- 一个全称闭句即可生成该族全部项代入实例。 -/
theorem sentence_of_closedTemplate {T : SetTheory} (kind : Kind)
    (parameters : SyntaxParameters.Parameters kind.arity)
    (h : Derives T [] (closedTemplate kind)) : Derives T [] (sentence kind parameters) := by
  have hClosed : Derives T ([] : Context signature [])
      (Formula.fromSentence (Metatheory.Formula.forall_close (template kind))) := h
  have hOpen := Metatheory.Derives.forall_close_elim (Γ := []) (template kind)
    (SyntaxDecode.substitution parameters.args) hClosed
  have hInstance : Derives T ([] : Context signature parameters.free) (instantiate kind parameters) := hOpen
  rw [instantiate_eq] at hInstance
  exact Metatheory.Derives.forall_close_of_derives hInstance

def parameterBasis (kind : Kind) : FiniteAxiomBasis (parameterTheory kind) where
  axioms := [closedTemplate kind]
  sound φ h := (List.mem_singleton.mp h) ▸ template_member kind
  complete := by
    rintro φ ⟨parameters, rfl⟩
    exact sentence_of_closedTemplate kind parameters
      (FirstOrder.Derives.theory_axiom List.mem_cons_self)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.SupportAssembly
