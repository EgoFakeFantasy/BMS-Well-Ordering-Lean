import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.BaseAxiomPacketData

/-! # 八条固定公理与两个无界模式的统一二元对象公式 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.BaseAxiomPacket
open Nonlogical.BasicSetTheory QuineEncoding NatPacket IntrinsicQuotation
open _root_.YesMetaZFC.Automation ObjectHorn
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def condition {bound free : SetContext} (packet output : SetTerm bound free) : SetFormula bound free :=
  anyOf [ObjectFiniteTable.condition fixedEntries packet output, SchemaPacket.condition packet output]

@[simp] theorem condition_substituteMapped {sb sf tb tf : SetContext} (packet output : SetTerm sb sf)
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf) :
    (condition packet output).substituteMapped bs fs =
      condition (packet.substituteMapped bs fs) (output.substituteMapped bs fs) := by
  simp [condition]

def template : FormulaTemplate.Binary where
  body := condition (.fvar .here) (.fvar (.there .here))

@[simp] theorem template_apply {bound free : SetContext} (packet output : SetTerm bound free) :
    template packet output = condition packet output := by
  simp [template, FormulaTemplate.apply_two, FormulaTemplate.instantiate,
    Term.substituteMapped, VariableSubstitution.cons]

theorem condition_delta0 {bound free : SetContext} (packet output : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound (condition packet output) :=
  .disj (ObjectFiniteTable.condition_delta0 _ _ _) (.disj (SchemaPacket.condition_delta0 _ _) .falsum)

theorem template_delta0 : Formula.IsDelta0 set_levy_bound template.body := condition_delta0 _ _

theorem fixed_positive (certificate : ZFCAxiomCertificate) (h : certificate ∈ fixedCertificates) :
    Derives intrinsic_zfc_theory [] (condition
      (numₘ(NatPacket.encode (zfc_base_axiom_encode certificate)))
      (IntrinsicQuotation.quote (project_sentence certificate.sentence))) :=
  anyOf_intro List.mem_cons_self (ObjectFiniteTable.positive_at_tree fixedEntries (fixedEntry certificate)
    (List.mem_map.mpr ⟨certificate, h, rfl⟩))

/-- 所有实际证书共用同一个公式；模式参数数目不受界限限制。 -/
theorem certificate_positive (certificate : ZFCAxiomCertificate) :
    Derives intrinsic_zfc_theory [] (condition
      (numₘ(NatPacket.encode (zfc_base_axiom_encode certificate)))
      (IntrinsicQuotation.quote (project_sentence certificate.sentence))) := by
  cases certificate
  case separation n schema =>
    exact anyOf_intro (List.mem_cons_of_mem _ List.mem_cons_self) (SchemaPacket.separation_positive schema)
  case collection n schema =>
    exact anyOf_intro (List.mem_cons_of_mem _ List.mem_cons_self) (SchemaPacket.collection_positive schema)
  all_goals
    exact fixed_positive _ (by simp [fixedCertificates])

theorem positive_at_tree (packet : Nat) (output : Tree) (h : run packet = some output) :
    Derives intrinsic_zfc_theory [] (condition (numₘ(packet)) (IntrinsicQuotation.tree output)) := by
  obtain ⟨certificate, rfl, rfl⟩ := (run_eq_some_iff packet output).mp h
  exact certificate_positive certificate

/-- 任意失败包与错误候选数码，都得到同一个二元公式的普通否定推导。 -/
theorem negative (packet output : Nat) (h : (run packet).map treeValue ≠ some output) :
    Derives intrinsic_zfc_theory [] (¬ₘ condition (numₘ(packet)) (numₘ(output) : Code)) := by
  apply anyOf_negative
  intro φ hφ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
  rcases hφ with rfl | rfl
  · apply ObjectFiniteTable.negative intrinsic_zfc_certificate_core
    intro entry hEntry hPacket hOutput
    obtain ⟨certificate, _, rfl⟩ := List.mem_map.mp hEntry
    apply h
    rw [hPacket]
    change Option.map treeValue (run (NatPacket.encode (zfc_base_axiom_encode certificate))) = some output
    rw [run_encode]
    exact congrArg some hOutput
  · apply SchemaPacket.negative
    intro hSchema
    obtain ⟨result, hResult, rfl⟩ := Option.map_eq_some_iff.mp hSchema
    exact h (by rw [schema_success packet result hResult]; rfl)

theorem positive (packet : Nat) (output : Tree) (h : run packet = some output) :
    Derives intrinsic_zfc_theory [] (condition (numₘ(packet)) (numₘ(treeValue output) : Code)) := by
  have h := FirstOrder.Derives.eq_subst
    (body := condition ((numₘ(packet) : Code).weakenBound SetSort.set) (.bvar .here))
    (tree_evaluate intrinsic_zfc_certificate_core output)
    (by
      simpa [Formula.instantiateTop, Formula.substitute, Substitution.instantiateTop,
        Term.substituteMapped, VariableSubstitution.instantiateTop] using positive_at_tree packet output h)
  simpa [Formula.instantiateTop, Formula.substitute, Substitution.instantiateTop,
    Term.substituteMapped, VariableSubstitution.instantiateTop] using h

theorem positive_number (packet output : Nat) (h : (run packet).map treeValue = some output) :
    Derives intrinsic_zfc_theory [] (condition (numₘ(packet)) (numₘ(output) : Code)) := by
  obtain ⟨result, hResult, rfl⟩ := Option.map_eq_some_iff.mp h
  exact positive packet result hResult

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

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.BaseAxiomPacket
