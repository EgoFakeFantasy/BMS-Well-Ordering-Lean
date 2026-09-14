import BMSConstructibleBridge.PowerlessStageAmbientAssignments
import BMSConstructibleBridge.PowerlessTruthRecordAbsolute

/-!
# 带记录的真实更新见证

源公式同时要求有限函数图、原单变量更新及指定真值记录。
当前层解释保留更新图属于该层，不将图值条件误当作图本身的定义。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthWitness

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def witness_l (ω D p b f i a : carrier_l ℳ) : Prop :=
  ∃ g, PowerlessAmbientAssignments.finite_l ω g ∧
    PowerlessAssignmentUpdate.update_l f i a g ∧ PowerlessTruthRecord.entry_l D p b g

def witness_m {Γ Δ : SortContext ℒ} (ω D p b f i a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let q (s : Term ℒ Γ Δ .set) := s.weakenBound SetTheory.SetSort.set
  .existsE .set (.conj (PowerlessAmbientAssignments.finite_m (q ω) (.bvar .here))
    (.conj (PowerlessAssignmentUpdate.update_m (q f) (q i) (q a) (.bvar .here))
      (PowerlessTruthRecord.entry_m (q D) (q p) (q b) (.bvar .here))))

theorem witness_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ)
    (ω D p b f i a : Term ℒ Γ Δ .set) :
    (witness_m ω D p b f i a).satisfies η ↔
      witness_l (ω.eval η) (D.eval η) (p.eval η) (b.eval η) (f.eval η) (i.eval η) (a.eval η) := by
  simp only [witness_m, witness_l, Formula.satisfies, PowerlessAmbientAssignments.finite_formula_l,
    PowerlessAssignmentUpdate.update_formula_l, PowerlessTruthRecord.entry_formula_l, Term.eval_weakenBound]
  rfl

theorem stage_l {U δ : carrier_l ℳ} {hU₀ : ∃ x, member_l ℳ x U}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val)
    (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
    (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
    (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val δ U)
    (hδ : PowerlessStagePair.limit_l δ) (D p b f i a : type_l U) :
    witness_l (ℳ := structure_l U hU₀) ω D p b f i a ↔
      ∃ g : type_l U, (∃ n, member_l ℳ n ω.val ∧ map_l g.val n U) ∧
        PowerlessAssignmentUpdate.update_l f.val i.val a.val g.val ∧
          PowerlessTruthRecord.entry_l D.val p.val b.val g.val := by
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  exact exists_congr fun g => and_congr
    (PowerlessStageAmbientAssignments.finite_l hℳ hω ht hT hU hδ)
    (and_congr (PowerlessValueAbsolute.update_l hUT) (PowerlessTruthRecordAbsolute.entry_l hUT))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthWitness
