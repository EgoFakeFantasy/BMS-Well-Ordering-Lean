import BMSConstructibleBridge.PowerlessTruthWitness
import BMSConstructibleBridge.PowerlessTruthSign
import BMSConstructibleBridge.PowerlessBoundedCode

/-!
# 读取集合分支记录的有界量词规则

真分支读取一个界内见证；假分支允许槽位不合法，或为每个界内元素
读取一个真实更新图的假记录。界槽没有取值时，全称条件正确地为真。
不要求界或记录集合有限；局部规则只消费严格较小公式码的归纳假设。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthBounded

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def positive_l (ω D p b f i j : carrier_l ℳ) : Prop :=
  PowerlessAmbientAssignments.slot_l ω f i ∧
    ∃ z, value_l f j z ∧ ∃ a, member_l ℳ a z ∧ PowerlessTruthWitness.witness_l ω D p b f i a

def negative_l (ω D p b f i j : carrier_l ℳ) : Prop :=
  PowerlessAmbientAssignments.finite_l ω f ∧
    (¬ PowerlessAmbientAssignments.slot_l ω f i ∨
      ∀ z, value_l f j z → ∀ a, member_l ℳ a z → PowerlessTruthWitness.witness_l ω D p b f i a)

def positive_m {Γ Δ : SortContext ℒ} (ω D p b f i j : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let q (s : Term ℒ Γ Δ .set) := s.weakenBound SetTheory.SetSort.set
  let v (s : Term ℒ Γ Δ .set) := (q s).weakenBound SetTheory.SetSort.set
  .conj (PowerlessAmbientAssignments.slot_m ω f i)
    (.existsE .set (.conj (SecondOrderObjectSyntax.value_m (q f) (q j) (.bvar .here))
      (.existsE .set (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there .here)))
        (PowerlessTruthWitness.witness_m (v ω) (v D) (v p) (v b) (v f) (v i) (.bvar .here))))))

def negative_m {Γ Δ : SortContext ℒ} (ω D p b f i j : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let q (s : Term ℒ Γ Δ .set) := s.weakenBound SetTheory.SetSort.set
  let v (s : Term ℒ Γ Δ .set) := (q s).weakenBound SetTheory.SetSort.set
  .conj (PowerlessAmbientAssignments.finite_m ω f)
    (.disj (.neg (PowerlessAmbientAssignments.slot_m ω f i))
      (.forallE .set (.imp (SecondOrderObjectSyntax.value_m (q f) (q j) (.bvar .here))
        (.forallE .set (.imp (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there .here)))
          (PowerlessTruthWitness.witness_m (v ω) (v D) (v p) (v b) (v f) (v i) (.bvar .here)))))))

def rule_m {Γ Δ : SortContext ℒ} (ω e t D p b f i j : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (.conj (.equal p e) (positive_m ω D e b f i j))
    (.conj (.equal p t) (negative_m ω D t b f i j))

theorem positive_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω D p b f i j : Term ℒ Γ Δ .set) :
    (positive_m ω D p b f i j).satisfies η ↔
      positive_l (ω.eval η) (D.eval η) (p.eval η) (b.eval η) (f.eval η) (i.eval η) (j.eval η) := by
  simp only [positive_m, positive_l, Formula.satisfies, PowerlessAmbientAssignments.slot_formula_l,
    value_formula_l, PowerlessTruthWitness.witness_formula_l, SecondOrderObjectSyntax.member_m,
    Arguments.eval, Term.eval_weakenBound]
  rfl

theorem negative_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω D p b f i j : Term ℒ Γ Δ .set) :
    (negative_m ω D p b f i j).satisfies η ↔
      negative_l (ω.eval η) (D.eval η) (p.eval η) (b.eval η) (f.eval η) (i.eval η) (j.eval η) := by
  simp only [negative_m, negative_l, Formula.satisfies, PowerlessAmbientAssignments.finite_formula_l,
    PowerlessAmbientAssignments.slot_formula_l, value_formula_l, PowerlessTruthWitness.witness_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

variable {U δ R H c : carrier_l ℳ} {hU₀ : ∃ x, member_l ℳ x U}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val)
  (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
  (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
  (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val δ U)
  (hδ : PowerlessStagePair.limit_l δ)
  (hR : PowerlessEvaluationOperator.assignments_l ω.val U R)
  (hH : PowerlessEvaluationRecursion.evaluation_l ω.val e.val T.val U t₁.val t₂.val t₃.val R H)

include hℳ hω ht hT hU hδ hR hH

theorem positive_source_l {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (w D s b f i j : Term ℒ Γ Δ .set)
    (hw : (w.eval η).val = ω.val) (hs : (s.eval η).val = e.val)
    (hD : ∀ d, member_l ℳ d c → ∀ p g, PowerlessTruthRecord.entry_l (D.eval η).val p d g →
      PowerlessTruthSign.sign_l e.val t₁.val H p d g)
    (hc : PowerlessBoundedCode.code_l ω.val e.val T.val t₂.val t₃.val
      (i.eval η).val (j.eval η).val (b.eval η).val c)
    (h : (positive_m w D s b f i j).satisfies η) :
    PowerlessEvaluationClause.query_l H c (f.eval η).val := by
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  have h₀ := (positive_formula_l η w D s b f i j).mp h
  have hw₀ : w.eval η = ω := Subtype.ext hw
  rw [hw₀] at h₀
  obtain ⟨hi, z, hz, a, ha, hg⟩ := h₀
  obtain ⟨n, hn, hf, hi⟩ := (PowerlessStageAmbientAssignments.slot_l hℳ hω ht hT hU hδ).mp hi
  have hz₀ := (PowerlessSourceGraphAbsolute.value_l hUT).mp hz
  obtain ⟨g, ⟨m, _, hg⟩, hu, hq⟩ := (PowerlessTruthWitness.stage_l hℳ hω ht hT hU hδ
    (D.eval η) (s.eval η) (b.eval η) (f.eval η) (i.eval η) a).mp hg
  have hnm := PowerlessAssignmentDomain.domain_l hℳ hf hg hi hu
  subst m
  rw [hs] at hq
  have hb := (PowerlessTruthSign.positive_l (PowerlessEvaluationTags.distinct_l hℳ ht).1).mp
    (hD _ (PowerlessBoundedCode.bounds_l hℳ hω ht.1 hT hc).2.2 _ _ hq)
  exact (PowerlessBoundedCode.equation_l hℳ hω ht hT hH hR hc (f.eval η).val
    ((hR (f.eval η).val).mpr ⟨n, hn, hf⟩)).mpr
      ⟨n, hn, hf, hi, z.val, hz₀, a.val, ha, g.val, hg, hu, hb⟩

theorem negative_source_l {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (w D s b f i j : Term ℒ Γ Δ .set)
    (hw : (w.eval η).val = ω.val) (hs : (s.eval η).val = t₁.val)
    (hD : ∀ d, member_l ℳ d c → ∀ p g, PowerlessTruthRecord.entry_l (D.eval η).val p d g →
      PowerlessTruthSign.sign_l e.val t₁.val H p d g)
    (hc : PowerlessBoundedCode.code_l ω.val e.val T.val t₂.val t₃.val
      (i.eval η).val (j.eval η).val (b.eval η).val c)
    (h : (negative_m w D s b f i j).satisfies η) :
    ¬ PowerlessEvaluationClause.query_l H c (f.eval η).val := by
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  have h₀ := (negative_formula_l η w D s b f i j).mp h
  have hw₀ : w.eval η = ω := Subtype.ext hw
  rw [hw₀] at h₀
  obtain ⟨hf, h⟩ := h₀
  have hf₀ := (PowerlessStageAmbientAssignments.finite_l hℳ hω ht hT hU hδ).mp hf
  intro hq
  obtain ⟨n, hn, hf, hi, z, hz, a, ha, g, hg, hu, hq⟩ :=
    (PowerlessBoundedCode.equation_l hℳ hω ht hT hH hR hc (f.eval η).val
      ((hR (f.eval η).val).mpr hf₀)).mp hq
  rcases h with hi₀ | h
  · exact hi₀ ((PowerlessStageAmbientAssignments.slot_l hℳ hω ht hT hU hδ).mpr ⟨n, hn, hf, hi⟩)
  · have hzU := (PowerlessValueAbsolute.coordinates_l hUT (f.eval η).property hz).2
    let z₀ : type_l U := ⟨z, hzU⟩
    let a₀ : type_l U := ⟨a, hUT z a hzU ha⟩
    have h₁ := h z₀ ((PowerlessSourceGraphAbsolute.value_l hUT).mpr hz) a₀ ha
    obtain ⟨g₀, ⟨m, _, hg₀⟩, hu₀, hq₀⟩ := (PowerlessTruthWitness.stage_l hℳ hω ht hT hU hδ
      (D.eval η) (s.eval η) (b.eval η) (f.eval η) (i.eval η) a₀).mp h₁
    have hnm := PowerlessAssignmentDomain.domain_l hℳ hf hg₀ hi hu₀
    subst m
    have hgg := PowerlessAssignmentUpdate.unique_l hℳ hg₀ hg hu₀ hu
    rw [hs] at hq₀
    have hb := (PowerlessTruthSign.negative_l (PowerlessEvaluationTags.distinct_l hℳ ht).1).mp
      (hD _ (PowerlessBoundedCode.bounds_l hℳ hω ht.1 hT hc).2.2 _ _ hq₀)
    exact hb (hgg.symm ▸ hq)

theorem source_l {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (w z s D p b f i j : Term ℒ Γ Δ .set)
    (hw : (w.eval η).val = ω.val) (hz : (z.eval η).val = e.val) (hs : (s.eval η).val = t₁.val)
    (hD : ∀ d, member_l ℳ d c → ∀ q g, PowerlessTruthRecord.entry_l (D.eval η).val q d g →
      PowerlessTruthSign.sign_l e.val t₁.val H q d g)
    (hc : PowerlessBoundedCode.code_l ω.val e.val T.val t₂.val t₃.val
      (i.eval η).val (j.eval η).val (b.eval η).val c)
    (h : (rule_m w z s D p b f i j).satisfies η) :
    PowerlessTruthSign.sign_l e.val t₁.val H (p.eval η).val c (f.eval η).val := by
  change (p.eval η = z.eval η ∧ (positive_m w D z b f i j).satisfies η) ∨
    (p.eval η = s.eval η ∧ (negative_m w D s b f i j).satisfies η) at h
  rcases h with ⟨hp, h⟩ | ⟨hp, h⟩
  · exact Or.inl ⟨(congrArg Subtype.val hp).trans hz,
      positive_source_l hℳ hω ht hT hU hδ hR hH η w D z b f i j hw hz hD hc h⟩
  · exact Or.inr ⟨(congrArg Subtype.val hp).trans hs,
      negative_source_l hℳ hω ht hT hU hδ hR hH η w D s b f i j hw hs hD hc h⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthBounded
