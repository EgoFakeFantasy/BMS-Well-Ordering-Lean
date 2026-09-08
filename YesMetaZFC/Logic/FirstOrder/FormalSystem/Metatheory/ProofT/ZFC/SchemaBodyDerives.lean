import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaBodyObjectReject

/-! # 支撑公理理论上正文识别的统一正负表示 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaObjectGraph.Body
open Nonlogical.BasicSetTheory QuineEncoding NatPacket IntrinsicQuotation
open _root_.YesMetaZFC.Automation ObjectHorn
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

theorem positive (depth : Nat) (input : Tree) (h : SchemaBody.check depth input = true) :
    Derives intrinsic_zfc_theory [] (condition (numₘ(depth)) (numₘ(treeValue input) : Code)) := by
  obtain ⟨rows, hRoot, hRows⟩ := check_accept depth input h
  have hGraph := ObjectHorn.positive intrinsic_zfc_certificate_core
    intrinsic_zfc_arithmetic_support.toFiniteSequenceGraphSupport
    (fun h => intrinsic_zfc_arithmetic_support.contains_function_predicate
      (relation_plane_theory_subset_function_predicate_theory
        (power_set_operator_theory_subset_relation_plane_theory h)))
    intrinsic_zfc_arithmetic_support.contains_infinity rules (row 1 depth input) rows hRoot hRows
  exact ObjectHorn.transport rules
    (FirstOrder.Derives.eq_symm (node_evaluate intrinsic_zfc_certificate_core 1 [depth, treeValue input])) hGraph

theorem negative (depth : Nat) (input : Tree) (h : SchemaBody.check depth input = false) :
    Derives intrinsic_zfc_theory [] (¬ₘ condition (numₘ(depth)) (numₘ(treeValue input) : Code)) := by
  have hGraph := ObjectHorn.negative intrinsic_zfc_certificate_core
    intrinsic_zfc_arithmetic_support.toArithmeticSupport (check_reject depth input h)
  exact ObjectHorn.transport_negative rules
    (FirstOrder.Derives.eq_symm (node_evaluate intrinsic_zfc_certificate_core 1 [depth, treeValue input])) hGraph

theorem positive_at_tree (depth : Nat) (input : Tree) (h : SchemaBody.check depth input = true) :
    Derives intrinsic_zfc_theory [] (condition (numₘ(depth)) (IntrinsicQuotation.tree input)) :=
  ObjectHorn.transport rules (node_congr 1 (.cons (Metatheory.Derives.equality_refl _)
    (.cons (FirstOrder.Derives.eq_symm (tree_evaluate intrinsic_zfc_certificate_core input)) .nil)))
    (positive depth input h)

theorem negative_at_tree (depth : Nat) (input : Tree) (h : SchemaBody.check depth input = false) :
    Derives intrinsic_zfc_theory [] (¬ₘ condition (numₘ(depth)) (IntrinsicQuotation.tree input)) :=
  ObjectHorn.transport_negative rules (node_congr 1 (.cons (Metatheory.Derives.equality_refl _)
    (.cons (FirstOrder.Derives.eq_symm (tree_evaluate intrinsic_zfc_certificate_core input)) .nil)))
    (negative depth input h)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaObjectGraph.Body
