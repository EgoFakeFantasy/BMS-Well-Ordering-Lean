import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaPacketMatrix

/-! # 固定二元模式传输公式的端到端正负 Derives -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaPacket
open Nonlogical.BasicSetTheory QuineEncoding NatPacket IntrinsicQuotation
open _root_.YesMetaZFC.Automation ObjectHorn ObjectArithmeticTerm
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

theorem limit_evaluate (packet : Nat) :
    Derives intrinsic_zfc_theory [] ((limitTerm (numₘ(packet)) : Code) ≐ₘ numₘ(tableBoundValue packet + 1)) :=
  successor_term_congr_of_equality _ _ (tableBound_evaluate intrinsic_zfc_arithmetic_support packet)

theorem bounded_positive (tag : Nat) (kind : SchemaTemplate.Kind) (count : Nat) (body output : Tree)
    (h : SchemaKernelJoin.run kind count body = some output) :
    Derives intrinsic_zfc_theory [] (bounded tag kind
      (numₘ(tableBoundValue (NatPacket.encode (.node tag [leaf count, body])) + 1))
      (numₘ(NatPacket.encode (.node tag [leaf count, body]))) (numₘ(treeValue output) : Code)) := by
  unfold bounded boundedTemplate FormulaTemplate.apply_three FormulaTemplate.instantiate
  apply quantify_positive (values := witnesses tag count body)
  · intro i
    simpa [Term.substituteMapped, VariableSubstitution.cons] using
      numeral_mem_of_lt intrinsic_zfc_arithmetic_support.contains_successor (witnesses_bound tag count body i)
  · simpa [Term.substituteMapped, VariableSubstitution.cons] using matrix_positive tag kind count body output h

theorem bounded_negative (tag : Nat) (kind : SchemaTemplate.Kind) (limit packet output : Nat)
    (h : (runBranch tag kind packet).map treeValue ≠ some output) :
    Derives intrinsic_zfc_theory [] (¬ₘ bounded tag kind (numₘ(limit)) (numₘ(packet)) (numₘ(output) : Code)) := by
  unfold bounded boundedTemplate FormulaTemplate.apply_three FormulaTemplate.instantiate
  apply quantify_negative intrinsic_zfc_certificate_core.toFiniteCore (limit := limit)
  · rfl
  · intro values _
    simpa [Term.substituteMapped, VariableSubstitution.cons] using matrix_negative tag kind packet output h values

@[simp] theorem bounded_instantiateTop (tag : Nat) (kind : SchemaTemplate.Kind) (point packet output : Code) :
    (bounded tag kind (.bvar .here) (packet.weakenBound SetSort.set) (output.weakenBound SetSort.set)).instantiateTop point =
      bounded tag kind point packet output := by
  simp [Formula.instantiateTop, Formula.substitute, Substitution.instantiateTop,
    Term.substituteMapped, VariableSubstitution.instantiateTop]

theorem bounded_transport (tag : Nat) (kind : SchemaTemplate.Kind) (packet output : Code) {left right : Code}
    (hEq : Derives intrinsic_zfc_theory [] (left ≐ₘ right))
    (h : Derives intrinsic_zfc_theory [] (bounded tag kind left packet output)) :
    Derives intrinsic_zfc_theory [] (bounded tag kind right packet output) := by
  have h := FirstOrder.Derives.eq_subst
    (body := bounded tag kind (.bvar .here) (packet.weakenBound SetSort.set) (output.weakenBound SetSort.set)) hEq
    (by rw [bounded_instantiateTop]; exact h)
  rwa [bounded_instantiateTop] at h

theorem bounded_transport_negative (tag : Nat) (kind : SchemaTemplate.Kind) (packet output : Code) {left right : Code}
    (hEq : Derives intrinsic_zfc_theory [] (left ≐ₘ right))
    (h : Derives intrinsic_zfc_theory [] (¬ₘ bounded tag kind left packet output)) :
    Derives intrinsic_zfc_theory [] (¬ₘ bounded tag kind right packet output) := by
  have h := FirstOrder.Derives.eq_subst
    (body := ¬ₘ bounded tag kind (.bvar .here) (packet.weakenBound SetSort.set) (output.weakenBound SetSort.set)) hEq
    (by rw [Formula.instantiateTop_neg, bounded_instantiateTop]; exact h)
  rwa [Formula.instantiateTop_neg, bounded_instantiateTop] at h

theorem branch_positive (tag : Nat) (kind : SchemaTemplate.Kind) (packet : Nat) (output : Tree)
    (h : runBranch tag kind packet = some output) :
    Derives intrinsic_zfc_theory [] (branch tag kind (numₘ(packet)) (numₘ(treeValue output) : Code)) := by
  obtain ⟨count, body, hPacket, hOutput⟩ := (branch_spec tag kind packet output).mp h
  have hCode := NatPacket.encode_of_decode hPacket
  rw [← hCode]
  exact bounded_transport tag kind _ _ (Metatheory.Derives.equality_symm (limit_evaluate _))
    (bounded_positive tag kind count body output hOutput)

theorem branch_negative (tag : Nat) (kind : SchemaTemplate.Kind) (packet output : Nat)
    (h : (runBranch tag kind packet).map treeValue ≠ some output) :
    Derives intrinsic_zfc_theory [] (¬ₘ branch tag kind (numₘ(packet)) (numₘ(output) : Code)) :=
  bounded_transport_negative tag kind _ _ (Metatheory.Derives.equality_symm (limit_evaluate packet))
    (bounded_negative tag kind (tableBoundValue packet + 1) packet output h)

theorem positive (packet : Nat) (output : Tree) (h : run packet = some output) :
    Derives intrinsic_zfc_theory [] (condition (numₘ(packet)) (numₘ(treeValue output) : Code)) := by
  obtain ⟨entry, hEntry, hBranch⟩ := (run_spec packet output).mp h
  exact anyOf_intro (List.mem_map.mpr ⟨entry, hEntry, rfl⟩)
    (branch_positive entry.1 entry.2 packet output hBranch)

/-- 对所有包自然数与候选自然数成立；畸形包、模式外壳、正文和错误结论均走同一出口。 -/
theorem negative (packet output : Nat) (h : (run packet).map treeValue ≠ some output) :
    Derives intrinsic_zfc_theory [] (¬ₘ condition (numₘ(packet)) (numₘ(output) : Code)) := by
  apply anyOf_negative
  intro φ hφ
  obtain ⟨entry, hEntry, rfl⟩ := List.mem_map.mp hφ
  apply branch_negative
  intro hBranch
  obtain ⟨result, hResult, rfl⟩ := Option.map_eq_some_iff.mp hBranch
  exact h (by rw [run_of_branch entry hEntry packet result hResult]; rfl)

/-- 最终输出槽可直接使用紧凑的内核 quotation 项。 -/
theorem positive_at_tree (packet : Nat) (output : Tree) (h : run packet = some output) :
    Derives intrinsic_zfc_theory [] (condition (numₘ(packet)) (IntrinsicQuotation.tree output)) := by
  have h := FirstOrder.Derives.eq_subst
    (body := condition ((numₘ(packet) : Code).weakenBound SetSort.set) (.bvar .here))
    (FirstOrder.Derives.eq_symm (tree_evaluate intrinsic_zfc_certificate_core output))
    (by
      simpa [Formula.instantiateTop, Formula.substitute, Substitution.instantiateTop,
        Term.substituteMapped, VariableSubstitution.instantiateTop] using positive packet output h)
  simpa [Formula.instantiateTop, Formula.substitute, Substitution.instantiateTop,
    Term.substituteMapped, VariableSubstitution.instantiateTop] using h

theorem negative_at_tree (packet : Nat) (output : Tree) (h : run packet ≠ some output) :
    Derives intrinsic_zfc_theory [] (¬ₘ condition (numₘ(packet)) (IntrinsicQuotation.tree output)) := by
  have hNeg := negative packet (treeValue output) (by
    intro hMap
    obtain ⟨result, hResult, hCode⟩ := Option.map_eq_some_iff.mp hMap
    exact h (treeValue_injective hCode ▸ hResult))
  have h := FirstOrder.Derives.eq_subst
    (body := ¬ₘ condition ((numₘ(packet) : Code).weakenBound SetSort.set) (.bvar .here))
    (FirstOrder.Derives.eq_symm (tree_evaluate intrinsic_zfc_certificate_core output))
    (by
      simpa [Formula.instantiateTop, Formula.substitute, Formula.substituteMapped, Substitution.instantiateTop,
        Term.substituteMapped, VariableSubstitution.instantiateTop] using hNeg)
  simpa [Formula.instantiateTop, Formula.substitute, Formula.substituteMapped, Substitution.instantiateTop,
    Term.substituteMapped, VariableSubstitution.instantiateTop] using h

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaPacket
