import BMSConstructibleBridge.PowerlessTruthSign
import BMSConstructibleBridge.PowerlessTruthRecordAbsolute
import BMSConstructibleBridge.PowerlessStageAmbientAssignments

/-!
# 当前层中有符号记录的与非规则

源公式只读取候选记录集和实际赋值，不读取完整域或完整求值器。
这里只证明局部规则消费可靠子记录；记录集整体的局部证书尚须另验。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthNand

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure
open PowerlessTruthRecord (entry_l entry_m entry_formula_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def branch_l (e t D p a b f : carrier_l ℳ) : Prop :=
  (p = e ∧ (entry_l D t a f ∨ entry_l D t b f)) ∨
    (p = t ∧ entry_l D e a f ∧ entry_l D e b f)

def rule_m {Γ Δ : SortContext ℒ} (ω e t D p a b f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessAmbientAssignments.finite_m ω f)
    (.disj (.conj (.equal p e) (.disj (entry_m D t a f) (entry_m D t b f)))
      (.conj (.equal p t) (.conj (entry_m D e a f) (entry_m D e b f))))

theorem rule_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e t D p a b f : Term ℒ Γ Δ .set) :
    (rule_m ω e t D p a b f).satisfies η ↔
      PowerlessAmbientAssignments.finite_l (ω.eval η) (f.eval η) ∧
        branch_l (e.eval η) (t.eval η) (D.eval η) (p.eval η) (a.eval η) (b.eval η) (f.eval η) := by
  simp only [rule_m, branch_l, Formula.satisfies, PowerlessAmbientAssignments.finite_formula_l, entry_formula_l]

theorem source_l {U δ R H c : carrier_l ℳ} {hU₀ : ∃ x, member_l ℳ x U}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val)
    (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
    (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
    (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val δ U)
    (hδ : PowerlessStagePair.limit_l δ)
    (hR : PowerlessEvaluationOperator.assignments_l ω.val U R)
    (hH : PowerlessEvaluationRecursion.evaluation_l ω.val e.val T.val U t₁.val t₂.val t₃.val R H)
    {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (w z s D p a b f : Term ℒ Γ Δ .set)
    (hw : (w.eval η).val = ω.val) (hz : (z.eval η).val = e.val) (hs : (s.eval η).val = t₁.val)
    (hD : ∀ d, member_l ℳ d c → ∀ q g,
      entry_l (D.eval η).val q d g → PowerlessTruthSign.sign_l e.val t₁.val H q d g)
    (hc : PowerlessFormulaConstructor.constructor_l ω.val e.val T.val t₂.val (a.eval η).val (b.eval η).val c)
    (h : (rule_m w z s D p a b f).satisfies η) :
    PowerlessTruthSign.sign_l e.val t₁.val H (p.eval η).val c (f.eval η).val := by
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  have h₀ := (rule_formula_l η w z s D p a b f).mp h
  have hw₀ : w.eval η = ω := Subtype.ext hw
  rw [hw₀] at h₀
  have hf := (PowerlessStageAmbientAssignments.finite_l hℳ hω ht hT hU hδ).mp h₀.1
  have hfR := (hR (f.eval η).val).mpr hf
  have hB := h₀.2
  simp only [branch_l, PowerlessTruthRecordAbsolute.entry_l hUT, hz, hs] at hB
  have hq : PowerlessEvaluationClause.query_l H c (f.eval η).val ↔
      ¬ (PowerlessEvaluationClause.query_l H (a.eval η).val (f.eval η).val ∧
        PowerlessEvaluationClause.query_l H (b.eval η).val (f.eval η).val) :=
    (PowerlessEvaluationEquations.nand_l hℳ hω ht hT hH hc (f.eval η).val).trans (and_iff_right hfR)
  apply (PowerlessTruthSign.nand_l (PowerlessEvaluationTags.distinct_l hℳ ht).1 hq).mpr
  have hab := PowerlessFormulaConstructor.bounds_l hℳ hω ht.1 hT hc
  rcases hB with ⟨hp, ha | hb⟩ | ⟨hp, ha, hb⟩
  · exact Or.inl ⟨(congrArg Subtype.val hp).trans hz, Or.inl (hD _ hab.1 _ _ ha)⟩
  · exact Or.inl ⟨(congrArg Subtype.val hp).trans hz, Or.inr (hD _ hab.2 _ _ hb)⟩
  · exact Or.inr ⟨(congrArg Subtype.val hp).trans hs, hD _ hab.1 _ _ ha, hD _ hab.2 _ _ hb⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthNand
