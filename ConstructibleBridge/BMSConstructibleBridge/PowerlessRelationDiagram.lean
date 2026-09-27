import BMSConstructibleBridge.PowerlessStageFiniteRanges
import BMSConstructibleBridge.PowerlessFiniteProduct
import BMSConstructibleBridge.PowerlessProduct

/-!
# 从实际标签关系构造低层有限关系图

固定源公式通过两张标签图拉回到索引对。公式长度只依赖源公式，
不依赖模型内部的两个索引长度。筛选在背景模型完成，结果再由内部有限
覆盖落入小层；标签、标签图及源公式参数都不要求属于小层。
乘积枚举由内部有限积定理构造，不预设有限图反射或稳定关系复杂度。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationDiagram

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

/-- 源公式前两个自由槽改读两列的标签，其他参数越过索引对和两张标签图。 -/
def binding_m {Γ : SortContext ℒ} : Substitution ℒ [] (.set :: .set :: Γ)
    [.set, .set, .set, .set] (.set :: .set :: .set :: Γ) :=
  .map (fun v => nomatch v) (fun {s} v => match s, v with
    | .set, .here => .bvar .here
    | .set, .there .here => .bvar (.there .here)
    | .set, .there (.there v) => .fvar (.there (.there (.there v))))

theorem binding_formula_l {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : Env ℳ [] Γ) (f g p i j a b : carrier_l ℳ) :
    (φ.substitute binding_m).satisfies
      (((((((η.pushFree g).pushFree f).pushFree p).pushBound i).pushBound j).pushBound a).pushBound b) ↔
      φ.satisfies ((η.pushFree a).pushFree b) := by
  rw [Formula.satisfies_substitute]
  apply Iff.of_eq
  congr 1
  apply Env.ext
  · intro s v
    nomatch v
  · intro s v
    match s, v with
    | .set, .here => rfl
    | .set, .there .here => rfl
    | .set, .there (.there v) => rfl

/-- 自由槽依次为索引对、左标签图、右标签图、原参数。 -/
def selector_m {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ)) :
    Formula ℒ [] (.set :: .set :: .set :: Γ) :=
  .existsE .set (.existsE .set (.existsE .set (.existsE .set (.conj
    (SecondOrderObjectSyntax.ordered_m (.bvar (.there (.there (.there .here))))
      (.bvar (.there (.there .here))) (.fvar .here))
    (.conj (SecondOrderObjectSyntax.value_m (.fvar (.there .here))
      (.bvar (.there (.there (.there .here)))) (.bvar (.there .here)))
    (.conj (SecondOrderObjectSyntax.value_m (.fvar (.there (.there .here)))
      (.bvar (.there (.there .here))) (.bvar .here))
      (φ.substitute binding_m)))))))

def selected_l {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : Env ℳ [] Γ) (f g p : carrier_l ℳ) : Prop :=
  ∃ i j a b, ordered_l i j p ∧ value_l f i a ∧ value_l g j b ∧
    φ.satisfies ((η.pushFree a).pushFree b)

theorem selector_formula_l {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : Env ℳ [] Γ) (f g p : carrier_l ℳ) :
    (selector_m φ).satisfies (((η.pushFree g).pushFree f).pushFree p) ↔
      selected_l φ η f g p := by
  simp only [selector_m, selected_l, Formula.satisfies, ordered_formula_l, value_formula_l]
  apply exists_congr
  intro i
  apply exists_congr
  intro j
  apply exists_congr
  intro a
  apply exists_congr
  intro b
  exact and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl
    (binding_formula_l φ η f g p i j a b)))

/-- 对实际两张标签函数图，选中一个索引对恰好等价于对应标签满足原关系。 -/
theorem selected_iff_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ)) (η : Env ℳ [] Γ)
    {f g p q B C i j a b z : carrier_l ℳ} (hf : map_l f p B) (hg : map_l g q C)
    (hz : ordered_l i j z) (ha : value_l f i a) (hb : value_l g j b) :
    selected_l φ η f g z ↔ φ.satisfies ((η.pushFree a).pushFree b) := by
  constructor
  · rintro ⟨i₀, j₀, a₀, b₀, hz₀, ha₀, hb₀, hφ⟩
    obtain ⟨rfl, rfl⟩ := (PowerlessBasic.ordered_eq_l hℳ hz₀ hz).mp rfl
    have h₁ := PowerlessFunction.value_unique_l hℳ hf ha₀ ha
    have h₂ := PowerlessFunction.value_unique_l hℳ hg hb₀ hb
    subst a₀
    subst b₀
    exact hφ
  · exact fun hφ => ⟨i, j, a, b, hz, ha, hb, hφ⟩

/-- 两个内部有限初段的所有索引对都属于实际极限层。 -/
theorem product_subset_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ α A p q P : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hα : PowerlessStagePair.limit_l α) (hωα : subset_l ω α)
    (hp : member_l ℳ p ω) (hq : member_l ℳ q ω)
    (hP : PowerlessProduct.product_l p q P) : subset_l P A := by
  intro z hz
  obtain ⟨i, hi, j, hj, hz⟩ := (hP z).mp hz
  have h := PowerlessStageParameters.naturals_l hℳ hω ht hT hA hωα
  exact PowerlessStageGraphClosure.ordered_l hℳ hω ht hT hA hα
    (h i (PowerlessNaturalOrder.subset_l hℳ hω p hp i hi))
    (h j (PowerlessNaturalOrder.subset_l hℳ hω q hq j hj)) hz

/-- 实际构造内部有限乘积的枚举，再筛选精确关系图并证明其属于小层。
不要求两张标签图或源公式环境位于该层。 -/
theorem separation_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ α A p q P : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hα : PowerlessStagePair.limit_l α) (hωα : subset_l ω α)
    (hp : member_l ℳ p ω) (hq : member_l ℳ q ω)
    (hP : PowerlessProduct.product_l p q P)
    {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (f g : carrier_l ℳ) :
    ∃ D, member_l ℳ D A ∧ ∀ z, member_l ℳ z D ↔
      member_l ℳ z P ∧ selected_l φ (PowerlessComprehension.env_l η) f g z := by
  obtain ⟨n, F, hn, hF, hC⟩ := PowerlessFiniteProduct.enumeration_l hℳ hω hp hq hP
  have hPA := product_subset_l hℳ hω ht hT hA hα hωα hp hq hP
  have hFA := PowerlessFunction.range_l hℳ hF
    (fun _ z hz => hPA z (PowerlessFunction.value_mem_l hℳ hF hz).2)
  let ζ : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ)
      ((.set :: .set :: Γ) : SortContext ℒ).length := (η.push g).push f
  have hζ : PowerlessComprehension.env_l ζ =
      ((PowerlessComprehension.env_l η).pushFree g).pushFree f := by
    apply Env.ext
    · intro s v
      nomatch v
    · intro s v
      cases v with
      | here => rfl
      | there v => cases v <;> rfl
  obtain ⟨D, hD, h⟩ := PowerlessStageFiniteRanges.separation_l hℳ hω ht hT hA hα hn hFA
    (selector_m φ) ζ
  refine ⟨D, hD, fun z => (h z).trans (and_congr ?_ ?_)⟩
  · exact ⟨fun ⟨i, hi⟩ => (PowerlessFunction.value_mem_l hℳ hF hi).2, hC z⟩
  · rw [hζ]
    exact selector_formula_l φ (PowerlessComprehension.env_l η) f g z

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationDiagram
