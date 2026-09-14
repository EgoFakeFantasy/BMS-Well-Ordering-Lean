import BMSConstructibleBridge.FiniteStageReflection
import BMSConstructibleBridge.ConstructibleStabilityFormulaData
import YesMetaZFC.BMS.ExpansionReflectionInput
import YesMetaZFC.BMS.LocalDescent

/-!
# 按种子高度局部化的有限层稳定边界

高度 `h` 只需要一个第 `h + 3` 层稳定对。其最小下端点给出统一有限支撑，
三次单点反射产生该高度的种子表示；组合下降随后只在此局部框架中进行。

本模块不构造全层稳定边界，也不证明有限层稳定对在二阶算术中存在。
终局定理显式保留逐层存在性 `pairs_l`，其余对象仍是 Lean 宿主层的实际序数。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge.FiniteStability

open StabilityFrame

/-- 第 `n` 层稳定对的最小下端点。 -/
def boundary_l (n : Nat) (σ : Ordinal.{u}) : Prop :=
  (∃ β, stageStableLt n σ β) ∧
    ∀ α, α < σ → ¬ ∃ β, stageStableLt n α β

/-- 每个有限层各有稳定对；不要求这些层共享端点。 -/
def pairs_l : Prop :=
  ∀ n, ∃ α β : Ordinal.{u}, stageStableLt n α β

/-- 从给定层的存在性选择最小下端点。 -/
noncomputable def least_l (n : Nat)
    (h : ∃ α β : Ordinal.{u}, stageStableLt n α β) : Ordinal.{u} :=
  Ordinal.lt_wf.min {α | ∃ β, stageStableLt n α β} h

/-- 所选下端点具有稳定后继，且没有更小的同层下端点。 -/
theorem least_spec_l (n : Nat)
    (h : ∃ α β : Ordinal.{u}, stageStableLt n α β) :
    boundary_l n (least_l n h) := by
  constructor
  · exact Ordinal.lt_wf.min_mem _ h
  · intro α hα hβ
    exact (Ordinal.lt_wf.not_lt_min _ hβ) hα

/-- 最小第 `n` 层边界以下，所有真稳定关系的层号均小于 `n`。 -/
theorem cutoff_l {n k : Nat} {σ α β : Ordinal.{u}}
    (h : boundary_l n σ) (hα : α < σ)
    (hβ : stageStableLt k α β) : k < n := by
  apply Nat.lt_of_not_ge
  intro h₁
  exact h.2 α hα ⟨β, stageStableLt_levelMonotone h₁ hβ⟩

/-- 边界以下的有限支撑有共同截断值 `n`。 -/
theorem support_l {n : Nat} {σ : Ordinal.{u}}
    (h : boundary_l n σ) :
    (boundedConstructibleStabilityFrame σ).FiniteLevelSupport := by
  intro α β
  exact ⟨n, fun _ h₁ => cutoff_l h α.2 h₁⟩

/-- 一个足够高的有限层边界已能提供指定高度的三个种子标签。 -/
noncomputable def seed_l
    (D : ConstructibleStabilityFormulaData.{u}
      (stageStableLt : Nat → Ordinal.{u} → Ordinal.{u} → Prop))
    {n h : Nat} {σ : Ordinal.{u}}
    (hσ : boundary_l n σ) (h₀ : h + 3 ≤ n) :
    SeedStabilityData (boundedConstructibleStabilityFrame σ) h := by
  let β := Classical.choose hσ.1
  have hβ : stageStableLt n σ β := Classical.choose_spec hσ.1
  have h₁ := exists_reflectedSingleton_l D
    (lower := fun i : Fin 0 => Fin.elim0 i)
    (cutoff := 0)
    (hAlphaBeta := stageStableLt_levelMonotone h₀ hβ)
    (hLower := fun i => Fin.elim0 i)
    (hCutoff := fun i _ _ => Fin.elim0 i)
  let α := Classical.choose h₁
  have hα := Classical.choose_spec h₁
  have h₂ := exists_reflectedSingleton_l D
    (lower := fun _ : Fin 1 => α)
    (cutoff := n)
    (hAlphaBeta := stageStableLt_levelMonotone
      (show h + 2 ≤ n by omega) hβ)
    (hLower := fun _ => hα.2.1)
    (hCutoff := fun _ _ hγ => cutoff_l hσ hα.2.1 hγ)
  let γ := Classical.choose h₂
  have hγ := Classical.choose_spec h₂
  have h₃ := exists_reflectedSingleton_l D
    (lower := fun i : Fin 2 => if i.1 = 0 then α else γ)
    (cutoff := n)
    (hAlphaBeta := stageStableLt_levelMonotone
      (show h + 1 ≤ n by omega) hβ)
    (hLower := by
      intro i
      split
      · exact hα.2.1
      · exact hγ.2.1)
    (hCutoff := by
      intro i k hδ
      apply cutoff_l hσ (β := σ) (k := k) _ hδ
      split
      · exact hα.2.1
      · exact hγ.2.1)
  let δ := Classical.choose h₃
  have hδ := Classical.choose_spec h₃
  refine {
    lower := ⟨α, hα.2.1⟩
    upper := ⟨γ, hγ.2.1⟩
    bound := ⟨δ, hδ.2.1⟩
    lower_lt_upper := hγ.1 (0 : Fin 1)
    upper_lt_bound := hδ.1 (1 : Fin 2)
    lower_stableLt_upper := ?_ }
  intro k hκ
  exact hγ.2.2.1 (0 : Fin 1) k (hα.2.2.2 k (by omega))

/-- 有限层边界提供的局部种子，在实际 BM4 一步关系下可达。 -/
theorem seed_acc_l
    (D : ConstructibleStabilityFormulaData.{u}
      (stageStableLt : Nat → Ordinal.{u} → Ordinal.{u} → Prop))
    {n h : Nat} {σ : Ordinal.{u}}
    (hσ : boundary_l n σ) (h₀ : h + 3 ≤ n) :
    Acc Step (validSeed h) := by
  let p := seed_l D hσ h₀
  have h₁ : LocalDescent.expands_l (boundedConstructibleStabilityFrame σ) :=
    ExpansionReflectionState.expand_bounded (boundedFiniteReflection_l D σ)
      (support_l hσ) (fun hα hβ => hα.trans hβ)
      boundedConstructibleStabilityFrame_stableLt_trans
  exact LocalDescent.acc_l h₁ p.representation
    (p.representation_boundedBy (fun hα hβ => hα.trans hβ))

/-- 逐层存在性给出全部种子的统一可达性，不选择共同的全层框架。 -/
theorem seeds_acc_l (h : pairs_l.{u}) : ∀ n, Acc Step (validSeed n) := by
  intro n
  exact seed_acc_l constructibleStabilityFormulaData_l.{u}
    (least_spec_l (n + 3) (h (n + 3))) (Nat.le_refl _)

/-- 仅保留逐有限层稳定对存在性的一步良基定理。 -/
theorem wf_l (h : pairs_l.{u}) : WellFounded GeneratedStep :=
  LocalDescent.wf_l (seeds_acc_l h)

/-- 仅保留逐有限层存在性的 BM4 严格良序定理。 -/
theorem wellOrder_l (h : pairs_l.{u}) :
    StrictWellOrder GeneratedArray GeneratedStrictDescent :=
  LocalDescent.wellOrder_l (seeds_acc_l h)

/-- 同一局部化证明排除 BM4 无限下降链。 -/
theorem no_descent_l (h : pairs_l.{u}) :
    ¬ ∃ f : Nat → GeneratedArray,
      ∀ n, GeneratedStep (f (n + 1)) (f n) :=
  LocalDescent.no_descent_l (seeds_acc_l h)

end YesMetaZFC.BMS.ConstructibleBridge.FiniteStability
