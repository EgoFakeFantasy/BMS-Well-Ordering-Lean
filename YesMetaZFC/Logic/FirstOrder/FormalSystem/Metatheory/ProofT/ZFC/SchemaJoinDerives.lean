import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaJoinMatrix

/-! # 统一模式对象公式的无合同正负 Derives -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaJoin
open Nonlogical.BasicSetTheory QuineEncoding NatPacket IntrinsicQuotation
open _root_.YesMetaZFC.Automation ObjectHorn ObjectArithmeticTerm
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

theorem limit_evaluate (n output : Nat) :
    Derives intrinsic_zfc_theory [] ((limitTerm (numₘ(n)) (numₘ(output)) : Code) ≐ₘ numₘ(limitValue n output)) :=
  successor_term_congr_of_equality _ _ (Metatheory.Derives.equality_trans
    (IntrinsicPairing.pair_congr_of_equalities _ _ _ _
      (tableBound_evaluate intrinsic_zfc_arithmetic_support n) (Metatheory.Derives.equality_refl _))
    (intrinsic_zfc_certificate_core.pair_value _ _))

theorem bounded_positive (kind : SchemaTemplate.Kind) (n : Nat) (input : Tree) (bodies : Fin 3 → Tree)
    (h : CorrectInputs kind n input bodies) :
    Derives intrinsic_zfc_theory [] (bounded kind
      (numₘ(limitValue n (treeValue (SchemaClosure.close n (SchemaTemplate.build kind bodies)))))
      (numₘ(n)) (numₘ(treeValue input)) (numₘ(treeValue (SchemaClosure.close n (SchemaTemplate.build kind bodies))) : Code)) := by
  unfold bounded FormulaTemplate.instantiate boundedTemplate
  apply quantify_positive (values := witnesses kind n bodies)
  · intro i
    simpa [arguments, Term.substituteMapped, VariableSubstitution.cons] using
      numeral_mem_of_lt intrinsic_zfc_arithmetic_support.contains_successor (witnesses_bound kind n input bodies h i)
  · simpa [arguments, Term.substituteMapped, VariableSubstitution.cons] using matrix_positive kind n input bodies h

theorem bounded_negative (kind : SchemaTemplate.Kind) (limit n : Nat) (input : Tree) (output : Nat)
    (h : (SchemaClosure.run kind n input).map treeValue ≠ some output) :
    Derives intrinsic_zfc_theory [] (¬ₘ bounded kind (numₘ(limit)) (numₘ(n)) (numₘ(treeValue input)) (numₘ(output) : Code)) := by
  unfold bounded FormulaTemplate.instantiate boundedTemplate
  apply quantify_negative intrinsic_zfc_certificate_core.toFiniteCore (limit := limit)
  · rfl
  · intro values _
    simpa [arguments, Term.substituteMapped, VariableSubstitution.cons] using matrix_negative kind n input output h values

@[simp] theorem bounded_instantiateTop (kind : SchemaTemplate.Kind) (point n input output : Code) :
    (bounded kind (.bvar .here) (n.weakenBound SetSort.set) (input.weakenBound SetSort.set)
      (output.weakenBound SetSort.set)).instantiateTop point = bounded kind point n input output := by
  simp [Formula.instantiateTop, Formula.substitute, Substitution.instantiateTop,
    Term.substituteMapped, VariableSubstitution.instantiateTop]

theorem bounded_transport (kind : SchemaTemplate.Kind) (n input output : Code) {left right : Code}
    (hEq : Derives intrinsic_zfc_theory [] (left ≐ₘ right))
    (h : Derives intrinsic_zfc_theory [] (bounded kind left n input output)) :
    Derives intrinsic_zfc_theory [] (bounded kind right n input output) := by
  have h := FirstOrder.Derives.eq_subst
    (body := bounded kind (.bvar .here) (n.weakenBound SetSort.set)
      (input.weakenBound SetSort.set) (output.weakenBound SetSort.set)) hEq
    (by rw [bounded_instantiateTop]; exact h)
  rwa [bounded_instantiateTop] at h

theorem bounded_transport_negative (kind : SchemaTemplate.Kind) (n input output : Code) {left right : Code}
    (hEq : Derives intrinsic_zfc_theory [] (left ≐ₘ right))
    (h : Derives intrinsic_zfc_theory [] (¬ₘ bounded kind left n input output)) :
    Derives intrinsic_zfc_theory [] (¬ₘ bounded kind right n input output) := by
  have h := FirstOrder.Derives.eq_subst
    (body := ¬ₘ bounded kind (.bvar .here) (n.weakenBound SetSort.set)
      (input.weakenBound SetSort.set) (output.weakenBound SetSort.set)) hEq
    (by rw [Formula.instantiateTop_neg, bounded_instantiateTop]; exact h)
  rwa [Formula.instantiateTop_neg, bounded_instantiateTop] at h

theorem branch_positive (kind : SchemaTemplate.Kind) (n : Nat) (input : Tree) (output : Nat)
    (h : (SchemaClosure.run kind n input).map treeValue = some output) :
    Derives intrinsic_zfc_theory [] (branch kind (numₘ(n)) (numₘ(treeValue input)) (numₘ(output) : Code)) := by
  obtain ⟨closed, hRun, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨bodies, hBodies, rfl⟩ := inputs_of_run kind n input closed hRun
  exact bounded_transport kind _ _ _ (Metatheory.Derives.equality_symm (limit_evaluate _ _))
    (bounded_positive kind n input bodies hBodies)

theorem branch_negative (kind : SchemaTemplate.Kind) (n : Nat) (input : Tree) (output : Nat)
    (h : (SchemaClosure.run kind n input).map treeValue ≠ some output) :
    Derives intrinsic_zfc_theory [] (¬ₘ branch kind (numₘ(n)) (numₘ(treeValue input)) (numₘ(output) : Code)) :=
  bounded_transport_negative kind _ _ _ (Metatheory.Derives.equality_symm (limit_evaluate _ _))
    (bounded_negative kind (limitValue n output) n input output h)

theorem positive (kind : SchemaTemplate.Kind) (n : Nat) (input : Tree) (output : Nat)
    (h : (SchemaClosure.run kind n input).map treeValue = some output) :
    Derives intrinsic_zfc_theory [] (condition (numₘ(kind.tag)) (numₘ(n)) (numₘ(treeValue input)) (numₘ(output) : Code)) := by
  apply anyOf_intro (List.mem_map.mpr ⟨kind, by cases kind <;> simp [kinds] , rfl⟩)
  exact FirstOrder.Derives.conj_intro (Metatheory.Derives.equality_refl _) (branch_positive kind n input output h)

/-- 原始输入可为任意树，输出为任意自然数；七个对象见证均被消去。 -/
theorem negative (kind : SchemaTemplate.Kind) (n : Nat) (input : Tree) (output : Nat)
    (h : (SchemaClosure.run kind n input).map treeValue ≠ some output) :
    Derives intrinsic_zfc_theory [] (¬ₘ condition (numₘ(kind.tag)) (numₘ(n)) (numₘ(treeValue input)) (numₘ(output) : Code)) := by
  apply anyOf_negative
  intro φ hφ
  obtain ⟨candidate, _, rfl⟩ := List.mem_map.mp hφ
  apply FirstOrder.Derives.neg_intro
  have hBoth := FirstOrder.Derives.assumption (T := intrinsic_zfc_theory)
    (Γ := [(numₘ(kind.tag) ≐ₘ numₘ(candidate.tag)) ∧ₘ branch candidate (numₘ(n)) (numₘ(treeValue input)) (numₘ(output) : Code)])
    List.mem_cons_self
  by_cases hTag : kind.tag = candidate.tag
  · have hSame : candidate = kind := by cases candidate <;> cases kind <;> simp_all [SchemaTemplate.Kind.tag]
    subst candidate
    exact FirstOrder.Derives.neg_elim (FirstOrder.Derives.conj_elim_right hBoth)
      (FirstOrder.Derives.context_weaken_cons (branch_negative kind n input output h))
  · exact FirstOrder.Derives.neg_elim (FirstOrder.Derives.conj_elim_left hBoth)
      (FirstOrder.Derives.context_weaken_cons (intrinsic_zfc_certificate_core.numeral_ne hTag))

theorem unknown_tag_negative (tag : Nat) (n input output : Code)
    (h0 : tag ≠ 0) (h1 : tag ≠ 1) (h2 : tag ≠ 2) :
    Derives intrinsic_zfc_theory [] (¬ₘ condition (numₘ(tag)) n input output) := by
  apply anyOf_negative
  intro φ hφ
  obtain ⟨kind, _, rfl⟩ := List.mem_map.mp hφ
  apply FirstOrder.Derives.neg_intro
  have hBoth := FirstOrder.Derives.assumption (T := intrinsic_zfc_theory)
    (Γ := [(numₘ(tag) ≐ₘ numₘ(kind.tag)) ∧ₘ branch kind n input output]) List.mem_cons_self
  exact FirstOrder.Derives.neg_elim (FirstOrder.Derives.conj_elim_left hBoth)
    (FirstOrder.Derives.context_weaken_cons (intrinsic_zfc_certificate_core.numeral_ne
      (by cases kind; exact h0; exact h1; exact h2)))

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaJoin
