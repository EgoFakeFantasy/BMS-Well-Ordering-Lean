import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaJoinDerives

/-! # 统一模式图连接紧凑树项和三类实际模式闭句 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaJoin
open Nonlogical.BasicSetTheory QuineEncoding NatPacket IntrinsicQuotation
open _root_.YesMetaZFC.Automation ObjectHorn
open _root_.YesMetaZFC.SetTheory
open _root_.YesMetaZFC.SetTheory.Definitional
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

private theorem input_instance (tag n output input : Code) :
    (condition (tag.weakenBound SetSort.set) (n.weakenBound SetSort.set) (.bvar .here)
      (output.weakenBound SetSort.set)).instantiateTop input = condition tag n input output := by
  simp [Formula.instantiateTop, Formula.substitute, Substitution.instantiateTop,
    Term.substituteMapped, VariableSubstitution.instantiateTop]

private theorem output_instance (tag n input output : Code) :
    (condition (tag.weakenBound SetSort.set) (n.weakenBound SetSort.set) (input.weakenBound SetSort.set)
      (.bvar .here)).instantiateTop output = condition tag n input output := by
  simp [Formula.instantiateTop, Formula.substitute, Substitution.instantiateTop,
    Term.substituteMapped, VariableSubstitution.instantiateTop]

theorem positive_at_tree (kind : SchemaTemplate.Kind) (n : Nat) (input output : Tree)
    (h : SchemaClosure.run kind n input = some output) :
    Derives intrinsic_zfc_theory [] (condition (numₘ(kind.tag)) (numₘ(n)) (tree input) (tree output)) := by
  have hNum := positive kind n input (treeValue output) (by rw [h]; rfl)
  have hInput := FirstOrder.Derives.eq_subst
    (body := condition ((numₘ(kind.tag) : Code).weakenBound SetSort.set)
      ((numₘ(n) : Code).weakenBound SetSort.set) (.bvar .here)
      ((numₘ(treeValue output) : Code).weakenBound SetSort.set))
    (Metatheory.Derives.equality_symm (tree_evaluate intrinsic_zfc_certificate_core input))
    (by rw [input_instance]; exact hNum)
  rw [input_instance] at hInput
  have hOutput := FirstOrder.Derives.eq_subst
    (body := condition ((numₘ(kind.tag) : Code).weakenBound SetSort.set)
      ((numₘ(n) : Code).weakenBound SetSort.set) ((tree input).weakenBound SetSort.set) (.bvar .here))
    (Metatheory.Derives.equality_symm (tree_evaluate intrinsic_zfc_certificate_core output))
    (by rw [output_instance]; exact hInput)
  rwa [output_instance] at hOutput

theorem negative_at_tree (kind : SchemaTemplate.Kind) (n : Nat) (input output : Tree)
    (h : SchemaClosure.run kind n input ≠ some output) :
    Derives intrinsic_zfc_theory [] (¬ₘ condition (numₘ(kind.tag)) (numₘ(n)) (tree input) (tree output)) := by
  have hNum := negative kind n input (treeValue output) (by
    intro hNum
    obtain ⟨actual, hRun, hValue⟩ := Option.map_eq_some_iff.mp hNum
    exact h (treeValue_injective hValue ▸ hRun))
  have hInput := FirstOrder.Derives.eq_subst
    (body := ¬ₘ condition ((numₘ(kind.tag) : Code).weakenBound SetSort.set)
      ((numₘ(n) : Code).weakenBound SetSort.set) (.bvar .here)
      ((numₘ(treeValue output) : Code).weakenBound SetSort.set))
    (Metatheory.Derives.equality_symm (tree_evaluate intrinsic_zfc_certificate_core input))
    (by rw [Formula.instantiateTop_neg, input_instance]; exact hNum)
  rw [Formula.instantiateTop_neg, input_instance] at hInput
  have hOutput := FirstOrder.Derives.eq_subst
    (body := ¬ₘ condition ((numₘ(kind.tag) : Code).weakenBound SetSort.set)
      ((numₘ(n) : Code).weakenBound SetSort.set) ((tree input).weakenBound SetSort.set) (.bvar .here))
    (Metatheory.Derives.equality_symm (tree_evaluate intrinsic_zfc_certificate_core output))
    (by rw [Formula.instantiateTop_neg, output_instance]; exact hInput)
  rwa [Formula.instantiateTop_neg, output_instance] at hOutput

theorem separation_positive {n : Nat} (schema : Project.UnarySchema n) :
    Derives intrinsic_zfc_theory [] (condition (numₘ(0)) (numₘ(n))
      (tree (ProjectEncode.formula schema.body)) (tree (ProjectEncode.formula (Axioms.Schema.separation schema).formula))) :=
  positive_at_tree .separation n _ _ (SchemaClosure.run_separation schema)

theorem collection_positive {n : Nat} (schema : Project.BinarySchema n) :
    Derives intrinsic_zfc_theory [] (condition (numₘ(1)) (numₘ(n))
      (tree (ProjectEncode.formula schema.body)) (tree (ProjectEncode.formula (Axioms.Schema.collection schema).formula))) :=
  positive_at_tree .collection n _ _ (SchemaClosure.run_collection schema)

theorem replacement_positive {n : Nat} (schema : Project.BinarySchema n) :
    Derives intrinsic_zfc_theory [] (condition (numₘ(2)) (numₘ(n))
      (tree (ProjectEncode.formula schema.body)) (tree (ProjectEncode.formula (Axioms.Schema.replacement schema).formula))) :=
  positive_at_tree .replacement n _ _ (SchemaClosure.run_replacement schema)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaJoin
