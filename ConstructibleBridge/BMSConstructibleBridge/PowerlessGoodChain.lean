import BMSConstructibleBridge.PowerlessGoodLabels
import BMSConstructibleBridge.PowerlessFiniteChain

/-!
# 任意内部有限长度的好标签链

固定正的外部高度后，只需把最高所用行的稳定关系作为一个内部参数。
先分离对上界稳定的好标签集合，再对其实际隶属关系作内部有限链构造。
较低行由单调性取得；列数可以非标准，不把内部归纳换成宿主 Nat 归纳。
这给出任意有限宽度的标签资源，尚未连接实际 BMS 展开与终止性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessGoodChain

open Logic FirstOrder ThirdOrderSemantics
open PowerlessRelabelLevels (level_m)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

private def parameter_m {Γ : SortContext ℒ} (i : Fin 10) :
    Term ℒ Γ (.set :: List.replicate 10 .set) .set :=
  .fvar (.there (SetTheory.Definitional.Project.fo_bound_variable i))

/-- 同一上界以下存在任意内部有限长度的严格递增好标签链，保留每个实际行层。 -/
theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ c N n α β A B S R F G q : carrier_l ℳ}
    (hω : omega_l ω) (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (hA : PowerlessStageEvaluation.system_l ω e T t₁ t₂ t₃ α A S F)
    (hB : PowerlessStageEvaluation.system_l ω e T t₁ t₂ t₃ β B R G)
    {H : Nat} (hc : PowerlessGoodBoundary.code_l ω e T t₁ t₂ t₃ c N
      (level_m (H + 1) (H + 1)))
    (hc₀ : member_l ℳ c ω) (hN : member_l ℳ N ω)
    (hn : PowerlessNumeral.numeral_l e (level_m (H + 1) (H + 1)) n)
    (hs : PowerlessGoodBoundary.stable_l ω e T t₁ t₂ t₃ c N n α β)
    (hq : member_l ℳ q ω) :
    ∃ f, map_l f q α ∧
      (∀ i a, value_l f i a → PowerlessCodedDiagram.good_l ω e T t₁ t₂ t₃ c N a ∧
        PowerlessGoodLabels.stable_l ω e T t₁ t₂ t₃ c N (H + 1) a α) ∧
      ∀ i j a b, member_l ℳ i j → value_l f i a → value_l f j b →
        member_l ℳ a b ∧ PowerlessGoodLabels.stable_l ω e T t₁ t₂ t₃ c N (H + 1) a b := by
  obtain ⟨m, hm⟩ := PowerlessNumeral.exists_l hℳ e (level_m (H + 1) H)
  have h₀ {a b : carrier_l ℳ}
      (h : PowerlessGoodLabels.stable_l ω e T t₁ t₂ t₃ c N (H + 1) a b) :
      PowerlessGoodBoundary.stable_l ω e T t₁ t₂ t₃ c N m a b := by
    obtain ⟨m₀, hm₀, h⟩ := h H (Nat.lt_succ_self H)
    exact PowerlessNumeral.unique_l hℳ hm₀ hm ▸ h
  have h₁ {a b : carrier_l ℳ}
      (h : PowerlessGoodBoundary.stable_l ω e T t₁ t₂ t₃ c N m a b) :
      PowerlessGoodLabels.stable_l ω e T t₁ t₂ t₃ c N (H + 1) a b := by
    intro j hj
    obtain ⟨v, hv⟩ := PowerlessNumeral.exists_l hℳ e (level_m (H + 1) j)
    exact ⟨v, hv, PowerlessGoodBoundary.monotone_l hℳ hω ht.1 hT
      (PowerlessNumeral.natural_l hℳ hω ht.1 hv)
      (PowerlessSourceStandardBudget.numeral_le_subset_l hℳ e
        (PowerlessRelabelLevels.mono_m (H + 1) (Nat.le_of_lt_succ hj)) hv hm) h⟩
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 10 :=
    { bound := Fin.cases ω (Fin.cases e (Fin.cases T (Fin.cases t₁ (Fin.cases t₂
        (Fin.cases t₃ (Fin.cases c (Fin.cases N (Fin.cases m (fun _ => α))))))))),
      free := fun _ => α }
  let φ : Formula ℒ [] (.set :: List.replicate 10 .set) :=
    PowerlessGoodBoundary.stable_m (parameter_m 0) (parameter_m 1) (parameter_m 2)
      (parameter_m 3) (parameter_m 4) (parameter_m 5) (parameter_m 6) (parameter_m 7)
      (parameter_m 8) (.fvar .here) (parameter_m 9)
  have hφ (a : carrier_l ℳ) :
      φ.satisfies ((PowerlessComprehension.env_l η).pushFree a) ↔
        PowerlessGoodBoundary.stable_l ω e T t₁ t₂ t₃ c N m a α := by
    rw [PowerlessGoodBoundary.stable_formula_l hℳ]
    rfl
  obtain ⟨X, hX⟩ := PowerlessComprehension.separation_l hℳ φ η α
  have hX₀ (a : carrier_l ℳ) : member_l ℳ a X ↔ member_l ℳ a α ∧
      PowerlessGoodBoundary.stable_l ω e T t₁ t₂ t₃ c N m a α :=
    (hX a).trans (and_congr Iff.rfl (hφ a))
  obtain ⟨Y, hY⟩ := PowerlessOrdinalRelation.exists_l hℳ X
  have hE : ∃ a, member_l ℳ a X := by
    obtain ⟨a, _, ha, hS⟩ := PowerlessGoodLabels.below_l hℳ hω ht hT hA hB hc hc₀ hN hn hs
    exact ⟨a, (hX₀ a).mpr ⟨ha, h₀ hS⟩⟩
  have hR : ∀ x y z, value_l Y x y → value_l Y y z → value_l Y x z := by
    intro x y z hxy hyz
    obtain ⟨hx, _, hxy⟩ := (PowerlessOrdinalRelation.value_l hℳ hY).mp hxy
    obtain ⟨_, hz, hyz⟩ := (PowerlessOrdinalRelation.value_l hℳ hY).mp hyz
    exact (PowerlessOrdinalRelation.value_l hℳ hY).mpr ⟨hx, hz,
      PowerlessOrdinal.transitive_l ((hX₀ z).mp hz).2.1.2.1.1 y x hyz hxy⟩
  have hS : ∀ x, member_l ℳ x X → ∃ y, member_l ℳ y X ∧ value_l Y x y := by
    intro x hx
    obtain ⟨hxα, hxS⟩ := (hX₀ x).mp hx
    have heω := PowerlessNatural.zero_mem_l hℳ hω ht.1
    obtain ⟨p, hp⟩ := PowerlessNatural.successor_exists_l hℳ e
    obtain ⟨f, C, hf, hf₀⟩ := PowerlessExtension.constant_l hℳ p x
    have hxA := (PowerlessStageOrdinal.member_l hℳ hω ht hT hA.1 hxS.1.2.1.1).mpr hxα
    have hfA : map_l f p A := PowerlessFunction.range_l hℳ hf (fun i a ha => by
      rw [((hf₀ i a).mp ha).2]
      exact hxA)
    have hfα : ∀ i a, value_l f i a → member_l ℳ a α := by
      intro i a ha
      rw [((hf₀ i a).mp ha).2]
      exact hxα
    obtain ⟨y, _, hyα, hyS, h⟩ := PowerlessGoodLabels.insert_l hℳ hω ht hT hA hB
      hc hc₀ hN hn hs (PowerlessNatural.successor_mem_l hℳ hω heω hp) hfA hfα
    have hyX := (hX₀ y).mpr ⟨hyα, h₀ hyS⟩
    have hfx := (hf₀ e x).mpr ⟨(hp e).mpr (Or.inr rfl), rfl⟩
    exact ⟨y, hyX, (PowerlessOrdinalRelation.value_l hℳ hY).mpr ⟨hx, hyX, (h e x hfx).1⟩⟩
  obtain ⟨f, hf, hF⟩ := PowerlessFiniteChain.serial_l hℳ hω hE hR hS q hq
  have hV {i a : carrier_l ℳ} (ha : value_l f i a) :=
    (hX₀ a).mp (PowerlessFunction.value_mem_l hℳ hf ha).2
  refine ⟨f, PowerlessFunction.range_l hℳ hf (fun _ _ ha => (hV ha).1), ?_, ?_⟩
  · exact fun _ _ ha => ⟨(hV ha).2.1, h₁ (hV ha).2⟩
  · intro i j a b hij ha hb
    have hab := ((PowerlessOrdinalRelation.value_l hℳ hY).mp (hF i j a b hij ha hb)).2.2
    exact ⟨hab, h₁ (PowerlessGoodBoundary.interpolate_l hℳ hω hab (hV ha).2 (hV hb).2)⟩

/-- 支持码和最小边界只随外部高度选择一次，同一边界容纳所有内部有限宽度。 -/
theorem initial_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T) (H : Nat) :
    ∃ c N n σ, member_l ℳ c ω ∧ member_l ℳ N ω ∧
      PowerlessGoodBoundary.code_l ω e T t₁ t₂ t₃ c N (level_m (H + 1) (H + 1)) ∧
      PowerlessNumeral.numeral_l e (level_m (H + 1) (H + 1)) n ∧
      PowerlessGoodBoundary.boundary_l ω e T t₁ t₂ t₃ c N n σ ∧
      ∀ q, member_l ℳ q ω → ∃ f, map_l f q σ ∧
        (∀ i a, value_l f i a → PowerlessCodedDiagram.good_l ω e T t₁ t₂ t₃ c N a ∧
          PowerlessGoodLabels.stable_l ω e T t₁ t₂ t₃ c N (H + 1) a σ) ∧
        ∀ i j a b, member_l ℳ i j → value_l f i a → value_l f j b →
          member_l ℳ a b ∧ PowerlessGoodLabels.stable_l ω e T t₁ t₂ t₃ c N (H + 1) a b := by
  obtain ⟨c, N, hc₀, hN, hc, h⟩ := PowerlessRelabelLevels.boundaries_l hℳ hω ht hT (H + 1)
  obtain ⟨n, σ, hn, hσ⟩ := h (H + 1) (Nat.le_refl _)
  obtain ⟨β, hs⟩ := hσ.1
  obtain ⟨A, B, S, R, F, G, hA, hB, _⟩ := hs.2.2.2.2
  exact ⟨c, N, n, σ, hc₀, hN, hc, hn, hσ,
    fun _ hq => exists_l hℳ hω ht hT hA hB hc hc₀ hN hn hs hq⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessGoodChain
