import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaPacketGraph

/-! # 三个任意对象中间码的正向填充与负向消去 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaPacket
open Nonlogical.BasicSetTheory QuineEncoding NatPacket IntrinsicQuotation
open _root_.YesMetaZFC.Automation ObjectHorn ObjectArithmeticTerm
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

theorem matrix_positive (tag : Nat) (kind : SchemaTemplate.Kind) (count : Nat) (body output : Tree)
    (h : SchemaKernelJoin.run kind count body = some output) :
    Derives intrinsic_zfc_theory [] (matrix tag kind (fun i => numₘ(witnesses tag count body i))
      (numₘ(NatPacket.encode (.node tag [leaf count, body]))) (numₘ(treeValue output) : Code)) := by
  apply allOf_intro
  intro φ hφ
  simp only [checks, List.mem_cons, List.not_mem_nil, or_false] at hφ
  rcases hφ with rfl | rfl | rfl
  · exact ObjectPacket.positive intrinsic_zfc_certificate_core
      intrinsic_zfc_arithmetic_support.toFiniteSequenceGraphSupport
      (fun h => intrinsic_zfc_arithmetic_support.contains_function_predicate
        (relation_plane_theory_subset_function_predicate_theory
          (power_set_operator_theory_subset_relation_plane_theory h)))
      intrinsic_zfc_arithmetic_support.contains_infinity _ _ (NatPacket.decode_encode _)
  · exact SchemaEnvelope.link_positive _ _ _ _
      ((SchemaEnvelope.value_iff tag _ count (treeValue body)).mpr ⟨body, rfl, rfl⟩)
  · exact SchemaKernelJoin.positive kind count body output h

theorem matrix_negative (tag : Nat) (kind : SchemaTemplate.Kind) (packet output : Nat)
    (hBad : (runBranch tag kind packet).map treeValue ≠ some output) (values : Fin 3 → Nat) :
    Derives intrinsic_zfc_theory [] (¬ₘ matrix tag kind (fun i => numₘ(values i))
      (numₘ(packet)) (numₘ(output) : Code)) := by
  classical
  by_cases hRaw : (NatPacket.decode packet).map treeValue = some (values 0)
  · obtain ⟨input, hPacket, hCode⟩ := Option.map_eq_some_iff.mp hRaw
    by_cases hEnvelope : treeValue input = (SchemaEnvelope.pattern tag).eval (values 1) (values 2)
    · obtain ⟨body, hShape, hBody⟩ := (SchemaEnvelope.value_iff tag input (values 1) (values 2)).mp hEnvelope
      apply allOf_negative_of_member (formulas := checks tag kind (fun i => numₘ(values i)) (numₘ(packet)) (numₘ(output) : Code))
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      change Derives intrinsic_zfc_theory [] (¬ₘ SchemaKernelJoin.condition kind
        (numₘ(values 1)) (numₘ(values 2)) (numₘ(output) : Code))
      rw [← hBody]
      apply SchemaKernelJoin.negative
      rw [hShape] at hPacket
      simpa [runBranch, hPacket, SchemaEnvelope.decode, leaf] using hBad
    · apply allOf_negative_of_member (formulas := checks tag kind (fun i => numₘ(values i)) (numₘ(packet)) (numₘ(output) : Code))
        (List.mem_cons_of_mem _ List.mem_cons_self)
      apply SchemaEnvelope.link_negative
      rwa [← hCode]
  · exact allOf_negative_of_member (formulas := checks tag kind (fun i => numₘ(values i)) (numₘ(packet)) (numₘ(output) : Code))
      List.mem_cons_self (ObjectPacket.negative_number intrinsic_zfc_certificate_core
        intrinsic_zfc_arithmetic_support.toArithmeticSupport packet (values 0) hRaw)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaPacket
