import BMSConstructibleBridge.PowerlessFormulaCodeAbsolute
import BMSConstructibleBridge.PowerlessValueAbsolute
import BMSConstructibleBridge.PowerlessStageFiniteGraphs

/-!
# 原局部求值公式在传递子域中的绝对性

存在量词的更新图由有限图闭包取回；构造子的两个字段由原自然数 guard
取回。与非分支使用查询的双向等价，不以单向保持代替否定的绝对性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationClauseAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem exists_l {B : carrier_l ℳ} {hB : ∃ x, member_l ℳ x B}
    (hBT : PowerlessNaturalOrder.transitive_l B) {ω A H f i b : type_l B}
    (hG : ∀ n, member_l ℳ n ω.val → ∀ g, map_l g n A.val → member_l ℳ g B) :
    PowerlessEvaluationClause.exists_l (ℳ := structure_l B hB) ω A H f i b ↔
      PowerlessEvaluationClause.exists_l ω.val A.val H.val f.val i.val b.val := by
  constructor
  · rintro ⟨n, hn, hf, hi, a, ha, g, hg, hu, hq⟩
    exact ⟨n.val, hn, (PowerlessSourceGraphAbsolute.map_l hBT).mp hf, hi, a.val, ha, g.val,
      (PowerlessSourceGraphAbsolute.map_l hBT).mp hg,
      (PowerlessValueAbsolute.update_l hBT).mp hu, (PowerlessValueAbsolute.query_l hBT).mp hq⟩
  · rintro ⟨n, hn, hf, hi, a, ha, g, hg, hu, hq⟩
    have hnB := hBT ω.val n ω.property hn
    have haB := hBT A.val a A.property ha
    exact ⟨⟨n, hnB⟩, hn, (PowerlessSourceGraphAbsolute.map_l hBT).mpr hf, hi, ⟨a, haB⟩, ha,
      ⟨g, hG n hn g hg⟩, (PowerlessSourceGraphAbsolute.map_l hBT).mpr hg,
      (PowerlessValueAbsolute.update_l hBT).mpr hu, (PowerlessValueAbsolute.query_l hBT).mpr hq⟩

theorem clause_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {B : carrier_l ℳ} {hB : ∃ x, member_l ℳ x B} (hBT : PowerlessNaturalOrder.transitive_l B)
    {ω e T A t₁ t₂ t₃ H n f : type_l B} (hω : omega_l ω.val) (he : PowerlessNatural.zero_l e.val)
    (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
    (hI : ∀ x, member_l ℳ x ω.val → ∀ F,
      PowerlessAddition.iteration_l ω.val e.val x F → member_l ℳ F B)
    (hG : ∀ k, member_l ℳ k ω.val → ∀ g, map_l g k A.val → member_l ℳ g B) :
    PowerlessEvaluationClause.clause_l (ℳ := structure_l B hB) ω e T A t₁ t₂ t₃ H n f ↔
      PowerlessEvaluationClause.clause_l ω.val e.val T.val A.val t₁.val t₂.val t₃.val H.val n.val f.val := by
  have h₀ (t : type_l B) (P : type_l B → type_l B → Prop) (Q : carrier_l ℳ → carrier_l ℳ → Prop)
      (hPQ : ∀ a b, P a b ↔ Q a.val b.val) :
      (∃ a b, PowerlessFormulaConstructor.constructor_l (ℳ := structure_l B hB) ω e T t a b n ∧ P a b) ↔
        ∃ a b, PowerlessFormulaConstructor.constructor_l ω.val e.val T.val t.val a b n.val ∧ Q a b := by
    constructor
    · rintro ⟨a, b, hc, h⟩
      exact ⟨a.val, b.val, (PowerlessFormulaCodeAbsolute.constructor_l hℳ hBT hω he hT hI).mp hc,
        (hPQ a b).mp h⟩
    · rintro ⟨a, b, hc, h⟩
      have haB := hBT ω.val a ω.property hc.1
      have hbB := hBT ω.val b ω.property hc.2.1
      exact ⟨⟨a, haB⟩, ⟨b, hbB⟩,
        (PowerlessFormulaCodeAbsolute.constructor_l hℳ hBT hω he hT hI).mpr hc,
        (hPQ ⟨a, haB⟩ ⟨b, hbB⟩).mpr h⟩
  unfold PowerlessEvaluationClause.clause_l
  apply or_congr
  · apply h₀ e
    intro i j
    exact PowerlessValueAbsolute.member_l hBT
  · apply or_congr
    · apply h₀ t₁
      intro i j
      exact PowerlessValueAbsolute.equal_l hBT
    · apply or_congr
      · apply h₀ t₂
        intro a b
        exact not_congr (and_congr (PowerlessValueAbsolute.query_l hBT) (PowerlessValueAbsolute.query_l hBT))
      · apply h₀ t₃
        intro i b
        exact exists_l hBT hG

theorem source_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {B : carrier_l ℳ} {hB : ∃ x, member_l ℳ x B} (hBT : PowerlessNaturalOrder.transitive_l B)
    {Γ Δ : SortContext ℒ} (η : Env (structure_l B hB) Γ Δ)
    (ω e T A t₁ t₂ t₃ H n f : Term ℒ Γ Δ .set)
    (hω : omega_l (ω.eval η).val) (he : PowerlessNatural.zero_l (e.eval η).val)
    (hT : PowerlessTriangular.triangular_l (ω.eval η).val (e.eval η).val (T.eval η).val)
    (hI : ∀ x, member_l ℳ x (ω.eval η).val → ∀ F,
      PowerlessAddition.iteration_l (ω.eval η).val (e.eval η).val x F → member_l ℳ F B)
    (hG : ∀ k, member_l ℳ k (ω.eval η).val → ∀ g, map_l g k (A.eval η).val → member_l ℳ g B) :
    Formula.satisfies η (PowerlessEvaluationClause.clause_m ω e T A t₁ t₂ t₃ H n f) ↔
      PowerlessEvaluationClause.clause_l (ω.eval η).val (e.eval η).val (T.eval η).val (A.eval η).val
        (t₁.eval η).val (t₂.eval η).val (t₃.eval η).val (H.eval η).val (n.eval η).val (f.eval η).val :=
  (PowerlessEvaluationClause.clause_formula_l η ω e T A t₁ t₂ t₃ H n f).trans (clause_l hℳ hBT hω he hT hI hG)

theorem stage_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ β B : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hB : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ β B)
    (hωβ : member_l ℳ ω β) (hβ : PowerlessStagePair.limit_l β) :
    ∃ hB₀ : ∃ x, member_l ℳ x B, ∃ w z U s₁ s₂ s₃ : type_l B,
      w.val = ω ∧ z.val = e ∧ U.val = T ∧ s₁.val = t₁ ∧ s₂.val = t₂ ∧ s₃.val = t₃ ∧
      ∀ A H n f : type_l B,
        PowerlessEvaluationClause.clause_l (ℳ := structure_l B hB₀) w z U A s₁ s₂ s₃ H n f ↔
          PowerlessEvaluationClause.clause_l ω e T A.val t₁ t₂ t₃ H.val n.val f.val := by
  obtain ⟨hw, hz, hU, h₁, h₂, h₃⟩ := PowerlessStageTriangular.parameters_l hℳ hω ht hT hB hωβ hβ
  have hBT := PowerlessStageStructure.transitive_l hℳ hω ht hT hB
  have hG := PowerlessStageFiniteGraphs.finite_l hℳ hω ht hT hB hβ
    (fun x hx => PowerlessOrdinal.transitive_l hβ.1 ω x hωβ hx)
  refine ⟨⟨ω, hw⟩, ⟨ω, hw⟩, ⟨e, hz⟩, ⟨T, hU⟩, ⟨t₁, h₁⟩, ⟨t₂, h₂⟩, ⟨t₃, h₃⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro A H n f
  apply clause_l hℳ hBT hω ht.1 hT
  · exact fun x hx F hF => PowerlessStageAdditionIteration.limit_l hℳ hω ht hT hB hωβ hβ hx hF
  · intro k hk g hg
    apply hG k hk g
    exact PowerlessFunction.range_l hℳ hg
      (fun x y hxy => hBT A.val y A.property (PowerlessFunction.value_mem_l hℳ hg hxy).2)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationClauseAbsolute
