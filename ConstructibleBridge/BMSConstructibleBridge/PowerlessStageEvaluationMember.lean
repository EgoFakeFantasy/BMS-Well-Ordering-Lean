import BMSConstructibleBridge.PowerlessEvaluationEntrySource

/-!
# 由域内有限前缀定义整个求值图

F 的所有值在 B 内，故每个内部有限前缀都由有限图闭包进入 B。
成员公式只使用 ω、编码、A、S 参数，不使用 F；源覆盖得到 F∈D(B)。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageEvaluationMember

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem operator_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ β B D A S F : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hB : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ β B)
    (hωβ : member_l ℳ ω β) (hβ : PowerlessStagePair.limit_l β)
    (hA : member_l ℳ A B) (hS : member_l ℳ S B)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F) (hF₀ : map_l F ω B)
    (hD : PowerlessEvaluationOperator.operator_l ω e T t₁ t₂ t₃ B D) : member_l ℳ F D := by
  obtain ⟨hωB, heB, hTB, h₁, h₂, h₃⟩ := PowerlessStageTriangular.parameters_l hℳ hω ht hT hB hωβ hβ
  have hωβ₀ : subset_l ω β := fun x hx => PowerlessOrdinal.transitive_l hβ.1 ω x hωβ hx
  have hN := PowerlessStageParameters.naturals_l hℳ hω ht hT hB hωβ₀
  have hG := PowerlessStageFiniteGraphs.finite_l hℳ hω ht hT hB hβ hωβ₀
  let hB₀ : ∃ x, member_l ℳ x B := ⟨ω, hωB⟩
  let η : Env (structure_l B hB₀) [.set, .set, .set, .set, .set, .set, .set, .set] [] :=
    ((((((((Env.empty (σ := ℒ) (M := structure_l B hB₀)).pushBound
      (sort := SetTheory.SetSort.set) ⟨S, hS⟩).pushBound ⟨t₃, h₃⟩).pushBound ⟨t₂, h₂⟩).pushBound
      ⟨t₁, h₁⟩).pushBound ⟨A, hA⟩).pushBound ⟨T, hTB⟩).pushBound ⟨e, heB⟩).pushBound ⟨ω, hωB⟩
  let φ : Formula ℒ [.set, .set, .set, .set, .set, .set, .set, .set, .set] [] :=
    PowerlessEvaluationEntry.entry_m
      (.bvar (.there .here))
      (.bvar (.there (.there .here)))
      (.bvar (.there (.there (.there .here))))
      (.bvar (.there (.there (.there (.there .here)))))
      (.bvar (.there (.there (.there (.there (.there .here))))))
      (.bvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.bvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
      (.bvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.bvar .here)
  apply PowerlessOperatorClosure.specified_l hℳ hω ht hT hD φ η
  intro p
  have h (hp : member_l ℳ p B) : φ.satisfies (η.pushBound ⟨p, hp⟩) ↔
      ∃ m G n Y : type_l B, member_l ℳ m.val ω ∧
        PowerlessEvaluationPrefix.prefix_l ω e T A t₁ t₂ t₃ S G.val m.val ∧
        value_l G.val n.val Y.val ∧ ordered_l n.val Y.val p :=
    PowerlessEvaluationEntrySource.stage_l hℳ hω ht hT hB hωβ hβ
      _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
  constructor
  · intro hp
    obtain ⟨n, Y, hn, hY, hp₀⟩ := hF₀.1 p hp
    have hpB := PowerlessStageGraphClosure.ordered_l hℳ hω ht hT hB hβ (hN n hn) hY hp₀
    obtain ⟨m, hm⟩ := PowerlessNatural.successor_exists_l hℳ n
    have hm₀ := PowerlessNatural.successor_mem_l hℳ hω hn hm
    obtain ⟨G, hG₀, h₀⟩ := PowerlessEvaluationPrefixRestriction.exists_l hℳ hF
      (PowerlessOrdinal.mem_l (PowerlessOmegaOrdinal.ordinal_l hℳ hω) hm₀)
      (PowerlessNaturalOrder.subset_l hℳ hω m hm₀)
    have hGB : member_l ℳ G B := by
      obtain ⟨C, hC, _⟩ := hG₀
      apply hG m hm₀ G (PowerlessFunction.range_l hℳ hC ?_)
      intro k Z hZ
      exact (PowerlessFunction.value_mem_l hℳ hF₀ ((h₀ k Z).mp hZ).2).2
    refine ⟨hpB, (h hpB).mpr ⟨⟨m, hN m hm₀⟩, ⟨G, hGB⟩, ⟨n, hN n hn⟩, ⟨Y, hY⟩, hm₀, hG₀, ?_, hp₀⟩⟩
    exact (h₀ n Y).mpr ⟨(hm n).mpr (Or.inr rfl), p, hp, hp₀⟩
  · rintro ⟨hp, h₀⟩
    obtain ⟨m, G, n, Y, hm, hG₀, hY, hp₀⟩ := (h hp).mp h₀
    exact (PowerlessEvaluationEntry.member_l hℳ hω hF p).mp
      ⟨m.val, G.val, n.val, Y.val, hm, hG₀, hY, hp₀⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageEvaluationMember
