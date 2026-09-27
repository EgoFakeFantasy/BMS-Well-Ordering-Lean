import BMSConstructibleBridge.PowerlessDiagramConstraint
import BMSConstructibleBridge.PowerlessSupportedReflection

/-!
# 同一标签图同时满足有限族约束的反射

全部矩阵共享同两个存在见证 g、B，不把各条约束分别存在化。
列表只枚举外部固定种类的约束，图的定义域 q 仍是任意内部集合。
反射给出实际小层函数图；具体 BMS 边、序及顶端条件须由各矩阵的语义引理解释。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessDiagramFamily

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

def realize_m {Γ Δ : SortContext ℒ} (Φ : List (Formula ℒ (.set :: .set :: Γ) Δ))
    (q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set (.existsE .set (.conj
    (SecondOrderObjectSyntax.map_m (.bvar (.there .here))
      ((q.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set) (.bvar .here))
    (Formula.conjunctionList Φ)))

theorem realize_formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (Φ : List (Formula ℒ (.set :: .set :: Γ) Δ))
    (q : Term ℒ Γ Δ .set) (η : Env ℳ Γ Δ) :
    (realize_m Φ q).satisfies η ↔
      ∃ g B, map_l g (q.eval η) B ∧ ∀ φ ∈ Φ, φ.satisfies ((η.pushBound g).pushBound B) := by
  simp only [realize_m, Formula.satisfies, map_formula_l, Term.eval_weakenBound,
    Formula.satisfies_conjunctionList_iff]
  rfl

/-- 对原矩阵族实际选择反射端点；任何上层共同见证都反射成一个小层共同函数图。 -/
theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    {Γ Δ : SortContext ℒ} (k : Nat) (Φ : List (Formula ℒ (.set :: .set :: Γ) Δ))
    (q : Term ℒ Γ Δ .set) (γ : carrier_l ℳ) (hγ : PowerlessOrdinal.ordinal_l γ) :
    ∃ n α β A B S R F G, ∃ hA₀ : ∃ x, member_l ℳ x A, ∃ hB₀ : ∃ x, member_l ℳ x B,
    ∃ hAB : subset_l A B,
      PowerlessNumeral.numeral_l e (PowerlessSupportedReflection.budget_m k [realize_m Φ q]) n ∧
      member_l ℳ γ α ∧
      PowerlessStageEvaluation.system_l ω e T t₁ t₂ t₃ α A S F ∧
      PowerlessStageEvaluation.system_l ω e T t₁ t₂ t₃ β B R G ∧
      Theory.Models (structure_l A hA₀) (Theory.ofList (PowerlessStabilitySupport.basis_m k)) ∧
      Theory.Models (structure_l B hB₀) (Theory.ofList (PowerlessStabilitySupport.basis_m k)) ∧
      PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ n α β ∧
      ∀ η : Env (structure_l A hA₀) Γ Δ,
        (realize_m Φ q).satisfies (PowerlessSourceInclusion.env_l (hU := hB₀) hAB η) →
        ∃ g D : type_l A, map_l g.val (q.eval η).val D.val ∧
          ∀ φ ∈ Φ, φ.satisfies ((η.pushBound g).pushBound D) := by
  obtain ⟨n, α, β, A, B, S, R, F, G, hA₀, hB₀, hAB, hn, hγα, hA, hB, h𝒜, hℬ, h, hΦ⟩ :=
    PowerlessSupportedReflection.exists_l hℳ hω ht hT k [realize_m Φ q] γ hγ
  refine ⟨n, α, β, A, B, S, R, F, G, hA₀, hB₀, hAB, hn, hγα, hA, hB, h𝒜, hℬ, h, ?_⟩
  intro η hη
  have h₀ := (hΦ (realize_m Φ q) (List.mem_singleton_self _) η).mp hη
  obtain ⟨g, D, hg, hD⟩ := (realize_formula_l Φ q η).mp h₀
  exact ⟨g, D, (PowerlessSourceGraphAbsolute.map_l
    (PowerlessStageStructure.transitive_l hℳ hω ht hT hA.1)).mp hg, hD⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessDiagramFamily
