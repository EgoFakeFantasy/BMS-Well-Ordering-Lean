import BMSConstructibleBridge.SecondOrderCanonicalMemberDefGraph
import BMSConstructibleBridge.SecondOrderMemberDef
import BMSConstructibleBridge.SecondOrderMemberDefault

/-! # 唯一 Def 输出图与商对象定义的连接

同一完整图证书给出原内部根域和精确合法切片集合；非空母根时恢复已验证
Def 关系。这里没有以宿主良基性替代模型内部根域。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalMemberDefSemantics

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem root_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    {a : num_l ℳ} {V E D Q R T F G P W : set_l ℳ}
    (h : SecondOrderCanonicalMemberDefGraph.spec_l A.real A.root a V E D Q R T F G P W) :
    SecondOrderDomain.wf_l W (zero_l ℳ) := by
  apply SecondOrderGraftDomain.root_l hℳ G P W h.graft
  intro c hc
  obtain ⟨i, rfl, _⟩ := (h.selection c).mp hc
  exact SecondOrderSubsetLayer.wf_l hℳ A F G (SecondOrderCanonicalSubsetLayer.layer_l hℳ h.layer) i

def code_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    {a : num_l ℳ} {V E D Q R T F G P W : set_l ℳ}
    (h : SecondOrderCanonicalMemberDefGraph.spec_l A.real A.root a V E D Q R T F G P W) :
    SecondOrderGraph.code_l ℳ := ⟨W, zero_l ℳ, root_l hℳ A h⟩

theorem collection_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    {a : num_l ℳ} {V E D Q R T F G P W : set_l ℳ}
    (h : SecondOrderCanonicalMemberDefGraph.spec_l A.real A.root a V E D Q R T F G P W)
    (B : SecondOrderGraph.code_l ℳ) : SecondOrderGraph.mem_l B (code_l hℳ A h) ↔
      ∃ i, SecondOrderLegalFormulaIndex.spec_l V E i ∧ ∀ C, SecondOrderGraph.mem_l C B ↔
        ∃ n, relation_l A.real n A.root ∧ relation_l F i n ∧
          SecondOrderBisimulation.eq_l C.real A.real C.root n := by
  let hLayer := SecondOrderCanonicalSubsetLayer.layer_l hℳ h.layer
  have hDomain c (hc : mem_l c P) : SecondOrderDomain.wf_l G c := by
    obtain ⟨i, rfl, _⟩ := (h.selection c).mp hc
    exact SecondOrderSubsetLayer.wf_l hℳ A F G hLayer i
  have hRead := SecondOrderGraftSemantics.mem_l hℳ G P W h.graft hDomain B
  change SecondOrderGraph.mem_l B (SecondOrderGraftSemantics.code_l hℳ G P W h.graft hDomain) ↔ _
  rw [hRead]
  constructor
  · rintro ⟨c, hc, hB⟩
    obtain ⟨i, rfl, hi⟩ := (h.selection c).mp hc
    change SecondOrderGraph.eq_l B (SecondOrderSubsetLayer.code_l hℳ A F G hLayer i) at hB
    exact ⟨i, hi, fun C => (SecondOrderGraph.mem_congr_l hℳ (SecondOrderGraph.refl_l hℳ C) hB).trans
      (SecondOrderSubsetLayer.mem_l hℳ A F G hLayer i C)⟩
  · rintro ⟨i, hi, hB⟩
    refine ⟨_, (h.selection _).mpr ⟨i, rfl, hi⟩, ?_⟩
    exact (SecondOrderGraph.ext_l hℳ B (SecondOrderSubsetLayer.code_l hℳ A F G hLayer i)).mpr
      (fun C => (hB C).trans (SecondOrderSubsetLayer.mem_l hℳ A F G hLayer i C).symm)

theorem presentation_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    {a : num_l ℳ} (ha : relation_l A.real a A.root) {V E D Q R T F G P W : set_l ℳ}
    (h : SecondOrderCanonicalMemberDefGraph.spec_l A.real A.root a V E D Q R T F G P W) :
    SecondOrderLegalMemberCollection.presentation_l hℳ A a ha V E D Q R T F (code_l hℳ A h) := by
  refine ⟨h.packet.formula_codes, h.packet.powers, h.packet.domain, ?_, h.packet.membership,
    h.packet.evaluation, h.packet.family, collection_l hℳ A h⟩
  intro n m
  refine (h.packet.equality n m).trans ?_
  constructor
  · intro hEq
    apply Subtype.ext
    exact (SecondOrderQuotient.eq_iff_l hℳ _ _).mpr hEq
  · intro hEq
    exact (SecondOrderQuotient.eq_iff_l hℳ _ _).mp (congrArg Subtype.val hEq)

theorem nonempty_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    {a : num_l ℳ} (ha : relation_l A.real a A.root) {V E D Q R T F G P W : set_l ℳ}
    (h : SecondOrderCanonicalMemberDefGraph.spec_l A.real A.root a V E D Q R T F G P W) :
    SecondOrderMemberDef.nonempty_l hℳ (SecondOrderQuotient.mk_l hℳ A)
      (SecondOrderQuotient.mk_l hℳ (code_l hℳ A h)) :=
  ⟨A, a, ha, V, E, D, Q, R, T, F, code_l hℳ A h, rfl, presentation_l hℳ A ha h, rfl⟩

theorem legal_exists_l (hℳ : Theory.Models ℳ theory_m) {V E : set_l ℳ}
    (hV : SecondOrderInternalFormulaSyntax.spec_l V) (hE : SecondOrderBinaryPowers.spec_l E) :
    ∃ i, SecondOrderLegalFormulaIndex.spec_l V E i := by
  have hValid : SecondOrderAssignmentSyntax.valid_l E (zero_l ℳ) (zero_l ℳ) := by
    simpa only [SecondOrderAssignmentSyntax.valid_l, SecondOrderSequenceSyntax.read_eq_l hE,
      SecondOrderAssignment.spec_l, SecondOrderNumberHistory.entry_l] using SecondOrderAssignment.empty_l hℳ hE
  exact ⟨_, zero_l ℳ, zero_l ℳ, zero_l ℳ, rfl, hValid,
    SecondOrderInternalFormulaCompilation.falsum_l hV _⟩

theorem empty_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    (hEmpty : ∀ n, ¬relation_l A.real n A.root)
    {a : num_l ℳ} {V E D Q R T F G P W : set_l ℳ}
    (h : SecondOrderCanonicalMemberDefGraph.spec_l A.real A.root a V E D Q R T F G P W) :
    SecondOrderPairObjects.pair_l hℳ (SecondOrderQuotient.mk_l hℳ A) (SecondOrderQuotient.mk_l hℳ A)
      (SecondOrderQuotient.mk_l hℳ (code_l hℳ A h)) := by
  have hA (C : SecondOrderGraph.code_l ℳ) : ¬SecondOrderGraph.mem_l C A := by
    rintro ⟨n, hn, _⟩
    exact hEmpty n hn
  obtain ⟨i, hi⟩ := legal_exists_l hℳ h.packet.formula_codes h.packet.powers
  intro b
  obtain ⟨B, rfl⟩ := SecondOrderQuotient.surj_l hℳ b
  change SecondOrderGraph.mem_l B (code_l hℳ A h) ↔
    SecondOrderQuotient.mk_l hℳ B = SecondOrderQuotient.mk_l hℳ A ∨
      SecondOrderQuotient.mk_l hℳ B = SecondOrderQuotient.mk_l hℳ A
  constructor
  · intro hB
    obtain ⟨j, _, hB⟩ := (collection_l hℳ A h B).mp hB
    have hEq : SecondOrderGraph.eq_l B A := (SecondOrderGraph.ext_l hℳ B A).mpr (fun C =>
      iff_of_false (fun hC => by obtain ⟨n, hn, _⟩ := (hB C).mp hC; exact hEmpty n hn) (hA C))
    exact Or.inl ((SecondOrderQuotient.eq_iff_l hℳ B A).mpr hEq)
  · intro hEq
    have hBA := (SecondOrderQuotient.eq_iff_l hℳ B A).mp (hEq.elim id id)
    apply (collection_l hℳ A h B).mpr
    refine ⟨i, hi, fun C => iff_of_false ?_ ?_⟩
    · intro hC
      exact hA C ((SecondOrderGraph.mem_congr_l hℳ (SecondOrderGraph.refl_l hℳ C) hBA).mp hC)
    · rintro ⟨n, hn, _⟩
      exact hEmpty n hn

theorem represents_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    {a : num_l ℳ} (ha : SecondOrderMemberDefault.spec_l A.real A.root a)
    {V E D Q R T F G P W : set_l ℳ}
    (h : SecondOrderCanonicalMemberDefGraph.spec_l A.real A.root a V E D Q R T F G P W) :
    SecondOrderMemberDef.spec_l hℳ (SecondOrderQuotient.mk_l hℳ A)
      (SecondOrderQuotient.mk_l hℳ (code_l hℳ A h)) := by
  rcases ha with ⟨ha, _⟩ | ⟨hEmpty, _⟩
  · exact Or.inr (nonempty_l hℳ A ha h)
  · refine Or.inl ⟨?_, empty_l hℳ A hEmpty h⟩
    intro z hz
    obtain ⟨Z, rfl⟩ := SecondOrderQuotient.surj_l hℳ z
    obtain ⟨n, hn, _⟩ := hz
    exact hEmpty n hn

#print axioms root_l
#print axioms nonempty_l
#print axioms represents_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalMemberDefSemantics
