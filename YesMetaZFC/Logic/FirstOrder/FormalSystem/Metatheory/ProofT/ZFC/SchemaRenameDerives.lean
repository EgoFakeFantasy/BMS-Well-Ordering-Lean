import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaRenameFormulaReject

/-! # 支撑公理理论上有限表重命名的统一正负表示 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaObjectGraph.Rename
open Nonlogical.BasicSetTheory QuineEncoding NatPacket IntrinsicQuotation
open _root_.YesMetaZFC.Automation ObjectHorn
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

theorem positive (target : Nat) (table : List Nat) (input output : Tree)
    (h : SchemaRename.run target table input = some output) :
    Derives intrinsic_zfc_theory [] (condition (numₘ(target)) (numₘ(listValue table))
      (numₘ(treeValue input)) (numₘ(treeValue output) : Code)) := by
  obtain ⟨rows, hRoot, hRows⟩ := run_accept target table input output h
  have hGraph := ObjectHorn.positive intrinsic_zfc_certificate_core
    intrinsic_zfc_arithmetic_support.toFiniteSequenceGraphSupport
    (fun h => intrinsic_zfc_arithmetic_support.contains_function_predicate
      (relation_plane_theory_subset_function_predicate_theory
        (power_set_operator_theory_subset_relation_plane_theory h)))
    intrinsic_zfc_arithmetic_support.contains_infinity rules (runRow target table input output) rows hRoot hRows
  exact ObjectHorn.transport rules (FirstOrder.Derives.eq_symm
    (node_evaluate intrinsic_zfc_certificate_core 5 [target, listValue table, treeValue input, treeValue output])) hGraph

/-- 包括解析失败、整表越界，以及解析成功但给出另一个输出的所有情况。 -/
theorem negative (target : Nat) (table : List Nat) (input output : Tree)
    (h : SchemaRename.run target table input ≠ some output) :
    Derives intrinsic_zfc_theory [] (¬ₘ condition (numₘ(target)) (numₘ(listValue table))
      (numₘ(treeValue input)) (numₘ(treeValue output) : Code)) := by
  have hGraph := ObjectHorn.negative intrinsic_zfc_certificate_core
    intrinsic_zfc_arithmetic_support.toArithmeticSupport (run_reject target table input output h)
  exact ObjectHorn.transport_negative rules (FirstOrder.Derives.eq_symm
    (node_evaluate intrinsic_zfc_certificate_core 5 [target, listValue table, treeValue input, treeValue output])) hGraph

/-- 六个实际模式位置均消费同一公式；不再留下重命名器的对象表示合同。 -/
theorem site_positive (site : SchemaRename.Site) (parameterCount : Nat)
    (body : _root_.YesMetaZFC.SetTheory.Definitional.Project.Formula 1 (site.sourceDepth parameterCount))
    (hClosed : body.FreeClosed) :
    Derives intrinsic_zfc_theory [] (condition (numₘ(site.targetDepth parameterCount))
      (numₘ(listValue (site.table parameterCount))) (numₘ(treeValue (ProjectEncode.formula body)))
      (numₘ(treeValue (ProjectEncode.formula (body.rename (site.mapping parameterCount)))) : Code)) :=
  positive _ _ _ _ (site.run_encode parameterCount body hClosed)

theorem site_negative (site : SchemaRename.Site) (parameterCount : Nat) (input output : Tree)
    (h : SchemaRename.run (site.targetDepth parameterCount) (site.table parameterCount) input ≠ some output) :
    Derives intrinsic_zfc_theory [] (¬ₘ condition (numₘ(site.targetDepth parameterCount))
      (numₘ(listValue (site.table parameterCount))) (numₘ(treeValue input)) (numₘ(treeValue output) : Code)) :=
  negative _ _ _ _ h

private theorem tree_arguments (target : Nat) (table : List Nat) (input output : Tree) :
    Derives intrinsic_zfc_theory []
      (IntrinsicQuotation.node 5 [numₘ(target), numₘ(listValue table), numₘ(treeValue input), numₘ(treeValue output)] ≐ₘ
        IntrinsicQuotation.node 5 [numₘ(target), structural_list_code_term (table.map (fun n => (numₘ(n) : Code))),
          IntrinsicQuotation.tree input, IntrinsicQuotation.tree output]) :=
  node_congr 5 (.cons (Metatheory.Derives.equality_refl _)
    (.cons (FirstOrder.Derives.eq_symm (numeral_list_evaluate intrinsic_zfc_certificate_core table))
      (.cons (FirstOrder.Derives.eq_symm (tree_evaluate intrinsic_zfc_certificate_core input))
        (.cons (FirstOrder.Derives.eq_symm (tree_evaluate intrinsic_zfc_certificate_core output)) .nil))))

theorem positive_at_tree (target : Nat) (table : List Nat) (input output : Tree)
    (h : SchemaRename.run target table input = some output) :
    Derives intrinsic_zfc_theory [] (condition (numₘ(target))
      (structural_list_code_term (table.map (fun n => numₘ(n))))
      (IntrinsicQuotation.tree input) (IntrinsicQuotation.tree output)) :=
  ObjectHorn.transport rules (tree_arguments target table input output) (positive target table input output h)

theorem negative_at_tree (target : Nat) (table : List Nat) (input output : Tree)
    (h : SchemaRename.run target table input ≠ some output) :
    Derives intrinsic_zfc_theory [] (¬ₘ condition (numₘ(target))
      (structural_list_code_term (table.map (fun n => numₘ(n))))
      (IntrinsicQuotation.tree input) (IntrinsicQuotation.tree output)) :=
  ObjectHorn.transport_negative rules (tree_arguments target table input output) (negative target table input output h)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaObjectGraph.Rename
