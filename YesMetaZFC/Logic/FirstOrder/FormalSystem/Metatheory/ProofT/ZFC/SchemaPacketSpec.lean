import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaPacketDerives
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaKernelSpec

/-! # 端到端对象图与原 ZFC 公理证书解码器的一致性

这里只筛选既有解码器中的两个模式构造子；固定公理和支撑公理仍由各自的检查层负责。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaPacket
open Nonlogical.BasicSetTheory QuineEncoding NatPacket IntrinsicQuotation
open _root_.YesMetaZFC.SetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def schemaConclusion : ZFCAxiomCertificate → Option Tree
  | .separation schema => some (SyntaxEncode.formula (project_sentence (Axioms.Schema.separation schema)))
  | .collection schema => some (SyntaxEncode.formula (project_sentence (Axioms.Schema.collection schema)))
  | _ => none

/-- 独立规格使用原公理解码器、原模式构造与当前内核 AST 编码。 -/
def actual (packet : Nat) : Option Tree := do
  let input ← NatPacket.decode packet
  let certificate ← zfc_base_axiom_decode input
  schemaConclusion certificate

theorem run_eq_actual (packet : Nat) : run packet = actual packet := by
  cases hPacket : NatPacket.decode packet with
  | none => simp [run, runBranch, actual, hPacket]
  | some input =>
    fun_cases zfc_base_axiom_decode input
    case case1 | case2 | case3 | case4 | case5 | case6 | case7 | case8 =>
      simp [run, runBranch, actual, hPacket, SchemaEnvelope.decode, zfc_base_axiom_decode, schemaConclusion]
    case case9 countTree body =>
      cases countTree with
      | node count fields =>
        cases fields with
        | nil =>
          simp [run, runBranch, actual, hPacket, SchemaEnvelope.decode,
            zfc_base_axiom_decode, scalar, SchemaKernelJoin.separation_decode, schemaConclusion]
          cases ProjectDecode.unarySchema count body <;> rfl
        | cons head tail =>
          simp [run, runBranch, actual, hPacket, SchemaEnvelope.decode, zfc_base_axiom_decode, scalar]
    case case10 countTree body =>
      cases countTree with
      | node count fields =>
        cases fields with
        | nil =>
          simp [run, runBranch, actual, hPacket, SchemaEnvelope.decode,
            zfc_base_axiom_decode, scalar, SchemaKernelJoin.collection_decode, schemaConclusion]
          cases ProjectDecode.binarySchema count body <;> rfl
        | cons head tail =>
          simp [run, runBranch, actual, hPacket, SchemaEnvelope.decode, zfc_base_axiom_decode, scalar]
    case case11 =>
      have hNone : zfc_base_axiom_decode input = none := by
        unfold zfc_base_axiom_decode
        split <;> simp_all
      have h8 : SchemaEnvelope.decode 8 input = none := by
        unfold SchemaEnvelope.decode
        split <;> simp_all
      have h9 : SchemaEnvelope.decode 9 input = none := by
        unfold SchemaEnvelope.decode
        split <;> simp_all
      simp [run, runBranch, actual, hPacket, hNone, h8, h9]

/-- 真正实际解码器的成功，直接给出固定二元对象图的普通推导。 -/
theorem actual_positive (packet : Nat) (output : Tree) (h : actual packet = some output) :
    Derives intrinsic_zfc_theory [] (condition (numₘ(packet)) (IntrinsicQuotation.tree output)) :=
  positive_at_tree packet output (by rw [run_eq_actual]; exact h)

theorem actual_positive_number (packet output : Nat) (h : (actual packet).map treeValue = some output) :
    Derives intrinsic_zfc_theory [] (condition (numₘ(packet)) (numₘ(output) : Code)) := by
  obtain ⟨result, hResult, rfl⟩ := Option.map_eq_some_iff.mp h
  exact positive packet result (by rw [run_eq_actual]; exact hResult)

theorem actual_negative (packet output : Nat) (h : (actual packet).map treeValue ≠ some output) :
    Derives intrinsic_zfc_theory [] (¬ₘ condition (numₘ(packet)) (numₘ(output) : Code)) :=
  negative packet output (by rw [run_eq_actual]; exact h)

theorem separation_positive {n : Nat} (schema : Definitional.Project.UnarySchema n) :
    Derives intrinsic_zfc_theory [] (condition
      (numₘ(NatPacket.encode (zfc_base_axiom_encode (.separation schema))))
      (IntrinsicQuotation.quote (project_sentence (Axioms.Schema.separation schema)))) := by
  apply positive_at_tree
  apply run_of_branch (8, .separation) (by simp [entries])
  apply (branch_spec 8 .separation _ _).mpr
  exact ⟨n, ProjectEncode.formula schema.body, NatPacket.decode_encode _, SchemaKernelJoin.run_separation schema⟩

theorem collection_positive {n : Nat} (schema : Definitional.Project.BinarySchema n) :
    Derives intrinsic_zfc_theory [] (condition
      (numₘ(NatPacket.encode (zfc_base_axiom_encode (.collection schema))))
      (IntrinsicQuotation.quote (project_sentence (Axioms.Schema.collection schema)))) := by
  apply positive_at_tree
  apply run_of_branch (9, .collection) (by simp [entries])
  apply (branch_spec 9 .collection _ _).mpr
  exact ⟨n, ProjectEncode.formula schema.body, NatPacket.decode_encode _, SchemaKernelJoin.run_collection schema⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaPacket
