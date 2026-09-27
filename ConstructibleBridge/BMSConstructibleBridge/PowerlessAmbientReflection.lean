import BMSConstructibleBridge.PowerlessSupportedReflection
import BMSConstructibleBridge.PowerlessAmbientStability

/-!
# 低层标签对实际反射端点的稳定性一致

有限公式族的反射同时处理所有小层标签与所有指定外部层号。
这不是高处标签的重标号存在性；这里只证明共同小层标签的顶端稳定迹一致。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessAmbientReflection

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure PowerlessSourcePadding

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

abbrev context_m : SortContext ℒ := [.set, .set, .set, .set, .set, .set, .set]

def formula_m (k : Nat) : Formula ℒ [.set, .set] context_m :=
  PowerlessAmbientStability.stable_m k omega_m zero_m triangle_m tag₁_m tag₂_m tag₃_m
    (.bvar (.there .here)) (.bvar .here)

def environment_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e T t₁ t₂ t₃ n x : carrier_l ℳ) : Env ℳ [.set, .set] context_m :=
  ((env_l Env.empty ω e T t₁ t₂ t₃ e).pushBound n).pushBound x

theorem source_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {U δ R H : carrier_l ℳ} {hU₀ : ∃ x, member_l ℳ x U}
    {ω e T t₁ t₂ t₃ n x : type_l U} (hω : omega_l ω.val)
    (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
    (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
    (hU : PowerlessStageEvaluation.system_l ω.val e.val T.val t₁.val t₂.val t₃.val δ U R H)
    (hδ : PowerlessStagePair.limit_l δ) (hωδ : member_l ℳ ω.val δ)
    {k : Nat} (h𝒰 : Theory.Models (structure_l U hU₀) (Theory.ofList (PowerlessStabilitySupport.basis_m k)))
    (j : Nat) (hj : j ≤ k) (hn : PowerlessNumeral.numeral_l e.val j n.val) :
    (formula_m j).satisfies (environment_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ n x) ↔
      PowerlessStageStability.stable_l ω.val e.val T.val t₁.val t₂.val t₃.val n.val x.val δ :=
  PowerlessAmbientStability.source_l hℳ hω ht hT hU.1 hδ hωδ
    (PowerlessStabilitySupport.hierarchy_l h𝒰) (PowerlessStabilitySupport.introduction_l h𝒰)
    hU.2.1 hU.2.2 j (fun i hi => PowerlessStabilitySupport.oracle_l (j := i) h𝒰 (Nat.lt_of_lt_of_le hi hj))
    (environment_l ω e T t₁ t₂ t₃ n x) omega_m zero_m triangle_m tag₁_m tag₂_m tag₃_m
    (.bvar (.there .here)) (.bvar .here) rfl rfl rfl rfl rfl rfl hn

theorem inclusion_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {A B : carrier_l ℳ} {hA₀ : ∃ x, member_l ℳ x A} {hB₀ : ∃ x, member_l ℳ x B}
    (hAB : subset_l A B) (ω e T t₁ t₂ t₃ n x : type_l A) :
    PowerlessSourceInclusion.env_l (hU := hB₀) hAB
      (environment_l (ℳ := structure_l A hA₀) ω e T t₁ t₂ t₃ n x) =
      environment_l (ℳ := structure_l B hB₀)
        (PowerlessSourceInclusion.inclusion_l hAB ω) (PowerlessSourceInclusion.inclusion_l hAB e)
        (PowerlessSourceInclusion.inclusion_l hAB T) (PowerlessSourceInclusion.inclusion_l hAB t₁)
        (PowerlessSourceInclusion.inclusion_l hAB t₂) (PowerlessSourceInclusion.inclusion_l hAB t₃)
        (PowerlessSourceInclusion.inclusion_l hAB n) (PowerlessSourceInclusion.inclusion_l hAB x) := by
  apply Env.ext
  · intro s v
    match s, v with
    | .set, .here => rfl
    | .set, .there .here => rfl
  · intro s v
    match s, v with
    | .set, .here => rfl
    | .set, .there .here => rfl
    | .set, .there (.there .here) => rfl
    | .set, .there (.there (.there .here)) => rfl
    | .set, .there (.there (.there (.there .here))) => rfl
    | .set, .there (.there (.there (.there (.there .here)))) => rfl
    | .set, .there (.there (.there (.there (.there (.there .here))))) => rfl

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (k : Nat) (γ : carrier_l ℳ) (hγ : PowerlessOrdinal.ordinal_l γ) :
    ∃ n α β A B S R F G,
      PowerlessNumeral.numeral_l e
        (PowerlessSupportedReflection.budget_m k ((List.range (k + 1)).map formula_m)) n ∧
      member_l ℳ γ α ∧
      PowerlessStageEvaluation.system_l ω e T t₁ t₂ t₃ α A S F ∧
      PowerlessStageEvaluation.system_l ω e T t₁ t₂ t₃ β B R G ∧
      PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ n α β ∧
      ∀ j, j ≤ k → ∀ m, PowerlessNumeral.numeral_l e j m → ∀ x, member_l ℳ x A →
        (PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ m x β ↔
          PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ m x α) := by
  obtain ⟨n, α, β, A, B, S, R, F, G, hA₀, hB₀, hAB, hn, hγα, hA, hB, h𝒜, hℬ, h, hΦ⟩ :=
    PowerlessSupportedReflection.exists_l hℳ hω ht hT k ((List.range (k + 1)).map formula_m) γ hγ
  refine ⟨n, α, β, A, B, S, R, F, G, hn, hγα, hA, hB, h, ?_⟩
  intro j hj m hm x hx
  have hp := h.2.1
  have hωβ := PowerlessOrdinal.transitive_l hp.2.2.2.1 α ω hp.2.1 hp.1
  obtain ⟨hw, hz, hV, hs₁, hs₂, hs₃⟩ :=
    PowerlessStageTriangular.parameters_l hℳ hω ht hT hA.1 hp.1 hp.2.2.1
  have hmA := PowerlessStageParameters.naturals_l hℳ hω ht hT hA.1
    (fun a ha => PowerlessOrdinal.transitive_l hp.2.2.1.1 ω a hp.1 ha) m
    (PowerlessNumeral.natural_l hℳ hω ht.1 hm)
  let w : type_l A := ⟨ω, hw⟩
  let z : type_l A := ⟨e, hz⟩
  let V : type_l A := ⟨T, hV⟩
  let s₁ : type_l A := ⟨t₁, hs₁⟩
  let s₂ : type_l A := ⟨t₂, hs₂⟩
  let s₃ : type_l A := ⟨t₃, hs₃⟩
  let v : type_l A := ⟨m, hmA⟩
  let a : type_l A := ⟨x, hx⟩
  let η := environment_l (ℳ := structure_l A hA₀) w z V s₁ s₂ s₃ v a
  have h₀ := source_l (ω := w) (e := z) (T := V) (t₁ := s₁) (t₂ := s₂) (t₃ := s₃)
    (n := v) (x := a) hℳ hω ht hT hA hp.2.2.1 hp.1 h𝒜 j hj hm
  have h₁ := source_l (ω := PowerlessSourceInclusion.inclusion_l hAB w)
    (e := PowerlessSourceInclusion.inclusion_l hAB z) (T := PowerlessSourceInclusion.inclusion_l hAB V)
    (t₁ := PowerlessSourceInclusion.inclusion_l hAB s₁) (t₂ := PowerlessSourceInclusion.inclusion_l hAB s₂)
    (t₃ := PowerlessSourceInclusion.inclusion_l hAB s₃) (n := PowerlessSourceInclusion.inclusion_l hAB v)
    (x := PowerlessSourceInclusion.inclusion_l hAB a) hℳ hω ht hT hB hp.2.2.2 hωβ hℬ j hj hm
  have h₂ := hΦ (formula_m j) (List.mem_map.mpr ⟨j, List.mem_range.mpr (Nat.lt_succ_of_le hj), rfl⟩) η
  rw [inclusion_l] at h₂
  exact h₁.symm.trans (h₂.trans h₀)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessAmbientReflection
