import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaKernelSpec

/-! # 三类模式到当前内核 quotation 的紧凑项接口 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaKernelJoin
open Nonlogical.BasicSetTheory QuineEncoding NatPacket IntrinsicQuotation
open _root_.YesMetaZFC.SetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

theorem positive_at_tree (kind : SchemaTemplate.Kind) (n : Nat) (input output : Tree)
    (h : run kind n input = some output) :
    Derives intrinsic_zfc_theory [] (condition kind (numₘ(n)) (tree input) (tree output)) := by
  have hInput := FirstOrder.Derives.eq_subst
    (body := condition kind ((numₘ(n) : Code).weakenBound SetSort.set) (.bvar .here)
      ((numₘ(treeValue output) : Code).weakenBound SetSort.set))
    (FirstOrder.Derives.eq_symm (tree_evaluate intrinsic_zfc_certificate_core input))
    (by
      simpa [Formula.instantiateTop, Formula.substitute, Substitution.instantiateTop,
        Term.substituteMapped, VariableSubstitution.instantiateTop] using positive kind n input output h)
  have hInput : Derives intrinsic_zfc_theory []
      (condition kind (numₘ(n)) (tree input) (numₘ(treeValue output) : Code)) := by
    simpa [Formula.instantiateTop, Formula.substitute, Substitution.instantiateTop,
      Term.substituteMapped, VariableSubstitution.instantiateTop] using hInput
  have hOutput := FirstOrder.Derives.eq_subst
    (body := condition kind ((numₘ(n) : Code).weakenBound SetSort.set)
      ((tree input).weakenBound SetSort.set) (.bvar .here))
    (FirstOrder.Derives.eq_symm (tree_evaluate intrinsic_zfc_certificate_core output))
    (by
      simpa [Formula.instantiateTop, Formula.substitute, Substitution.instantiateTop,
        Term.substituteMapped, VariableSubstitution.instantiateTop] using hInput)
  simpa [Formula.instantiateTop, Formula.substitute, Substitution.instantiateTop,
    Term.substituteMapped, VariableSubstitution.instantiateTop] using hOutput

theorem separation_positive {n : Nat} (schema : Definitional.Project.UnarySchema n) :
    Derives intrinsic_zfc_theory [] (condition .separation (numₘ(n))
      (tree (ProjectEncode.formula schema.body)) (IntrinsicQuotation.quote (project_sentence (Axioms.Schema.separation schema)))) :=
  positive_at_tree .separation n _ _ (run_separation schema)

theorem collection_positive {n : Nat} (schema : Definitional.Project.BinarySchema n) :
    Derives intrinsic_zfc_theory [] (condition .collection (numₘ(n))
      (tree (ProjectEncode.formula schema.body)) (IntrinsicQuotation.quote (project_sentence (Axioms.Schema.collection schema)))) :=
  positive_at_tree .collection n _ _ (run_collection schema)

/-- 替换的独立模式接口，不改变 ZFC 原公理证书的构造子。 -/
theorem replacement_positive {n : Nat} (schema : Definitional.Project.BinarySchema n) :
    Derives intrinsic_zfc_theory [] (condition .replacement (numₘ(n))
      (tree (ProjectEncode.formula schema.body)) (IntrinsicQuotation.quote (project_sentence (Axioms.Schema.replacement schema)))) :=
  positive_at_tree .replacement n _ _ (run_replacement schema)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaKernelJoin
