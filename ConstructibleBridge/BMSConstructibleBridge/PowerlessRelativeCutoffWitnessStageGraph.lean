import BMSConstructibleBridge.PowerlessRelativeHistoryWitnessStage
import BMSConstructibleBridge.PowerlessRelativeCutoffClassHistory
import BMSConstructibleBridge.PowerlessRelativeClassRawFunction
import BMSConstructibleBridge.PowerlessRelativeClassFunctionRange
import BMSConstructibleBridge.PowerlessRelativeClassOntoCountability

/-! # 实际截断见证的 Class 最小阶段图

对象语言为纯隶属 ℒ，背景为原 Z₂。真实 Class 前史在证明内生成；
有界固定矩阵的逐自然数最小阶段经 Class 的 Δ₀ 构图得到同一实际函数。
参数只需是真实 Class 对象；任意原矩阵对 W 相对化后可接入此有界模式。
本模块先建设实际图及精确读数，不把 Class 图升级为 W 成员，也不以
可数值域冒充其序数并集的可数性。完整 Collection 与原对象出口另行接入。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffWitnessStageGraph

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private def input_m {Γ Ε Δ : SortContext ℒ} (x : Term ℒ Γ Ε .set)
    (τ : Variable Δ .set → Term ℒ Γ Ε .set) :
    Variable (.set :: Δ) .set → Term ℒ Γ Ε .set
  | .here => x
  | .there v => τ v

def graph_m {Γ Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (F W x a : Term ℒ Γ Ε .set) (τ : Variable Δ .set → Term ℒ Γ Ε .set) : Formula ℒ Γ Ε :=
  PowerlessRelativeHistoryWitnessStage.rank_m φ F W a (input_m x τ)

theorem delta_l {Γ Ε Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) (F W x a : Term ℒ Γ Ε .set)
    (τ : Variable Δ .set → Term ℒ Γ Ε .set) :
    Formula.IsDelta0 membershipLevyBound (graph_m φ F W x a τ) :=
  PowerlessRelativeHistoryWitnessStage.rank_delta_l hφ F W a (input_m x τ)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ

theorem graph_formula_l {Γ Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 Γ Ε) (F W x a : Term ℒ Γ Ε .set)
    (τ : Variable Δ .set → Term ℒ Γ Ε .set) :
    (graph_m φ F W x a τ).satisfies η ↔
      PowerlessRelativeHistoryWitnessStage.rank_l φ
        ((PowerlessRelativeHistoryWitnessStage.env_l η τ).pushFree (x.eval η))
        (F.eval η) (W.eval η) (a.eval η) := by
  have hEnv : PowerlessRelativeHistoryWitnessStage.env_l η (input_m x τ) =
      (PowerlessRelativeHistoryWitnessStage.env_l η τ).pushFree (x.eval η) := by
    apply Env.ext
    · intro s v; nomatch v
    · intro s v; cases s; cases v <;> rfl
  simpa only [graph_m, hEnv] using
    PowerlessRelativeHistoryWitnessStage.rank_formula_l φ η F W a (input_m x τ)

/-- 使用指定的真实前史，图中每个输出仍是原矩阵的最小阶段。 -/
theorem history_l (K : source_coding_l hℳ) {B ω Ω W : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B ω Ω)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W)
    (F : type_l hℳ B) (hF : PowerlessRelativeHierarchySemantics.history_l hℳ B Ω F.val W)
    {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) (η : Env 𝒱 [] Δ)
    (hParams : ∀ s (v : Variable Δ s), PowerlessRelativeClassCorrespondence.member_l hℳ B (η.freeVal v))
    (hSome : ∀ x, mem_l hℳ x ω → ∃ y, mem_l hℳ y W ∧ φ.satisfies ((η.pushFree x).pushFree y)) :
    ∃ G : type_l hℳ B, map_l (ℳ := 𝒱) G.val ω Ω ∧ ∀ x a,
      value_l (ℳ := 𝒱) G.val x a ↔ mem_l hℳ x ω ∧ mem_l hℳ a Ω ∧
        PowerlessRelativeWitnessLeastStage.rank_l φ (η.pushFree x) B a := by
  let η' : Env (structure_l hℳ B hBase) [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with | .set => ⟨η.freeVal v, hParams .set v⟩ }
  let O : type_l hℳ B := ⟨ω, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ hω)⟩
  let A : type_l hℳ B := ⟨Ω, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase hΩ.1⟩
  let C : type_l hℳ B := ⟨W, PowerlessRelativeLevelClosure.class_l hℳ hBase hW⟩
  let ξ : Env (structure_l hℳ B hBase) [] (.set :: .set :: Δ) :=
    (η'.pushFree C).pushFree F
  let τ : Variable Δ .set → Term ℒ [] (.set :: .set :: .set :: .set :: Δ) .set :=
    fun v => .fvar (.there (.there (.there (.there v))))
  let ψ : Formula ℒ [] (.set :: .set :: .set :: .set :: Δ) :=
    graph_m φ (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar .here) (.fvar (.there .here)) τ
  have hψ : Formula.IsDelta0 membershipLevyBound ψ := delta_l hφ _ _ _ _ τ
  have hRead (x a : Raw) :
      ψ.satisfies (((PowerlessRelativeClassRelativization.env_l ξ).pushFree a).pushFree x) ↔
        PowerlessRelativeHistoryWitnessStage.rank_l φ (η.pushFree x) F.val W a := by
    have hEnv : PowerlessRelativeHistoryWitnessStage.env_l
        (((PowerlessRelativeClassRelativization.env_l ξ).pushFree a).pushFree x) τ = η := by
      apply Env.ext
      · intro s v; nomatch v
      · intro s v; cases s; rfl
    have h := graph_formula_l φ
      (((PowerlessRelativeClassRelativization.env_l ξ).pushFree a).pushFree x)
      (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar .here) (.fvar (.there .here)) τ
    change ψ.satisfies (((PowerlessRelativeClassRelativization.env_l ξ).pushFree a).pushFree x) ↔
      PowerlessRelativeHistoryWitnessStage.rank_l φ
        ((PowerlessRelativeHistoryWitnessStage.env_l
          (((PowerlessRelativeClassRelativization.env_l ξ).pushFree a).pushFree x) τ).pushFree x)
        F.val W a at h
    simpa only [hEnv] using h
  have hTotal (x : Raw) (hx : mem_l hℳ x O.val) : ∃! a : Raw,
      mem_l hℳ a A.val ∧ ψ.satisfies
        (((PowerlessRelativeClassRelativization.env_l ξ).pushFree a).pushFree x) := by
    obtain ⟨a, ⟨ha, hRank⟩, hUnique⟩ := PowerlessRelativeCutoffLeastWitnessStage.exists_l K
      hBase hω hΩ hW φ (η.pushFree x) (hSome x hx)
    refine ⟨a, ⟨ha, (hRead x a).mpr
      ((PowerlessRelativeHistoryWitnessStage.rank_iff_l φ (η.pushFree x) hΩ.1 hF ha).mpr hRank)⟩, ?_⟩
    rintro b ⟨hb, hψb⟩
    exact hUnique b ⟨hb,
      (PowerlessRelativeHistoryWitnessStage.rank_iff_l φ (η.pushFree x) hΩ.1 hF hb).mp ((hRead x b).mp hψb)⟩
  obtain ⟨G, hG, hGraph⟩ := PowerlessRelativeClassRawFunction.exists_l (hBase := hBase) hψ ξ O A hTotal
  refine ⟨G, hG, fun x a => ?_⟩
  constructor
  · intro hValue
    obtain ⟨hx, ha, hψa⟩ := (hGraph x a).mp hValue
    exact ⟨hx, ha,
      (PowerlessRelativeHistoryWitnessStage.rank_iff_l φ (η.pushFree x) hΩ.1 hF ha).mp ((hRead x a).mp hψa)⟩
  · rintro ⟨hx, ha, hRank⟩
    exact (hGraph x a).mpr ⟨hx, ha, (hRead x a).mpr
      ((PowerlessRelativeHistoryWitnessStage.rank_iff_l φ (η.pushFree x) hΩ.1 hF ha).mpr hRank)⟩

/-- 前史与最小阶段图都在证明内构造，不增加 Class 图来源假设。 -/
theorem exists_l (K : source_coding_l hℳ) {B ω Ω W : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B ω Ω)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W)
    {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) (η : Env 𝒱 [] Δ)
    (hParams : ∀ s (v : Variable Δ s), PowerlessRelativeClassCorrespondence.member_l hℳ B (η.freeVal v))
    (hSome : ∀ x, mem_l hℳ x ω → ∃ y, mem_l hℳ y W ∧ φ.satisfies ((η.pushFree x).pushFree y)) :
    ∃ F G : type_l hℳ B, PowerlessRelativeHierarchySemantics.history_l hℳ B Ω F.val W ∧
      map_l (ℳ := 𝒱) G.val ω Ω ∧ ∀ x a,
        value_l (ℳ := 𝒱) G.val x a ↔ mem_l hℳ x ω ∧ mem_l hℳ a Ω ∧
          PowerlessRelativeWitnessLeastStage.rank_l φ (η.pushFree x) B a := by
  obtain ⟨F, hF⟩ := PowerlessRelativeCutoffClassHistory.exists_l hℳ K hBase hω hΩ hW
  obtain ⟨G, hG, hRead⟩ := history_l K hBase hω hΩ hW F hF hφ η hParams hSome
  exact ⟨F, G, hF, hG, hRead⟩

/-- 实际阶段函数的精确值域属于 Class 且类内可数；其并集可数另须证明。 -/
theorem range_l (K : source_coding_l hℳ) {B ω Ω : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hω : SecondOrderOmega.omega_l hℳ ω) (G : type_l hℳ B)
    (hG : map_l (ℳ := 𝒱) G.val ω Ω) :
    ∃ C : type_l hℳ B, PowerlessRelativeOrdinalCutoff.countable_l B ω C.val ∧
      ∀ a, mem_l hℳ a C.val ↔ ∃ x, value_l (ℳ := 𝒱) G.val x a := by
  let O : type_l hℳ B := ⟨ω, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ hω)⟩
  obtain ⟨C, hC⟩ := PowerlessRelativeClassFunctionRange.exists_l hBase O G hG
  have hMap : map_l (ℳ := 𝒱) G.val ω C.val := by
    constructor
    · intro p hp
      obtain ⟨x, a, hx, _, hxa⟩ := hG.1 p hp
      exact ⟨x, a, hx, (hC a).mpr ⟨x, p, hp, hxa⟩, hxa⟩
    · intro x hx
      obtain ⟨a, ⟨_, hxa⟩, _⟩ := hG.2 x hx
      exact ⟨a, ⟨(hC a).mpr ⟨x, hxa⟩, hxa⟩, fun b hb =>
        SecondOrderFunctionProperties.value_unique_l hℳ hG hb.2 hxa⟩
  have hOnto (a : Raw) (ha : mem_l hℳ a C.val) :
      ∃ x, mem_l hℳ x ω ∧ value_l (ℳ := 𝒱) G.val x a := by
    obtain ⟨x, hxa⟩ := (hC a).mp ha
    exact ⟨x, (SecondOrderFunctionProperties.value_mem_l hℳ hG hxa).1, hxa⟩
  exact ⟨C, PowerlessRelativeClassOntoCountability.countable_l (hBase := hBase)
    K hω C.property G.property hMap hOnto, hC⟩

#print axioms graph_formula_l
#print axioms history_l
#print axioms exists_l
#print axioms range_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffWitnessStageGraph
