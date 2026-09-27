import BMSConstructibleBridge.PowerlessDiagramRelabelConditions
import BMSConstructibleBridge.PowerlessStableTrace

/-!
# 原标签图的精确有限关系记录

先在背景模型中筛选实际原关系，再以内部有限性证明记录属于下层。
标签图、标签和稳定上端点都可以在下层之外；不把内部列数改为宿主 Fin。
七槽、九槽环境仅为固定公式的系统参数，不枚举列。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelabelDiagram

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

/-- 在指定内部索引乘积上精确记录原两图之间为真的关系。 -/
def edges_l (r : carrier_l ℳ → carrier_l ℳ → Prop) (p q f g D : carrier_l ℳ) : Prop :=
  ∀ z, member_l ℳ z D ↔ ∃ i j a b, member_l ℳ i p ∧ member_l ℳ j q ∧
    ordered_l i j z ∧ value_l f i a ∧ value_l g j b ∧ r a b

/-- 精确记录哪些内部列的原标签满足指定性质。 -/
def trace_l (r : carrier_l ℳ → Prop) (q g D : carrier_l ℳ) : Prop :=
  ∀ i, member_l ℳ i D ↔ member_l ℳ i q ∧ ∃ a, value_l g i a ∧ r a

private def parameter_m {n : Nat} (i : Fin n) : Term ℒ [] (List.replicate n .set) .set :=
  .fvar (SetTheory.Definitional.Project.fo_bound_variable i)

theorem edges_exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ α A p q : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hα : PowerlessStagePair.limit_l α) (hωα : subset_l ω α)
    (hp : member_l ℳ p ω) (hq : member_l ℳ q ω)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Δ.length)
    (r : carrier_l ℳ → carrier_l ℳ → Prop)
    (hφ : ∀ a b, φ.satisfies (((PowerlessComprehension.env_l η).pushFree a).pushFree b) ↔ r a b)
    (f g : carrier_l ℳ) : ∃ D, member_l ℳ D A ∧ edges_l r p q f g D := by
  obtain ⟨P, hP⟩ := PowerlessProduct.exists_l hℳ p q
  obtain ⟨D, hDA, hD⟩ := PowerlessRelationDiagram.separation_l hℳ hω ht hT hA hα hωα
    hp hq hP φ η f g
  refine ⟨D, hDA, fun z => (hD z).trans ?_⟩
  constructor
  · rintro ⟨hz, i, j, a, b, hij, ha, hb, h⟩
    obtain ⟨i₀, hi, j₀, hj, hij₀⟩ := (hP z).mp hz
    obtain ⟨hᵢ, hⱼ⟩ := (PowerlessBasic.ordered_eq_l hℳ hij₀ hij).mp rfl
    exact ⟨i, j, a, b, hᵢ ▸ hi, hⱼ ▸ hj, hij, ha, hb, (hφ a b).mp h⟩
  · rintro ⟨i, j, a, b, hi, hj, hij, ha, hb, h⟩
    exact ⟨(hP z).mpr ⟨i, hi, j, hj, hij⟩, i, j, a, b, hij, ha, hb, (hφ a b).mpr h⟩

/-- 原序关系的真实有限图；原标签与原图不要求位于下层。 -/
theorem order_exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ α A p q : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hα : PowerlessStagePair.limit_l α) (hωα : subset_l ω α)
    (hp : member_l ℳ p ω) (hq : member_l ℳ q ω) (f g : carrier_l ℳ) :
    ∃ D, member_l ℳ D A ∧ edges_l (member_l ℳ) p q f g D := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 0 :=
    { bound := Fin.elim0, free := fun _ => ω }
  exact edges_exists_l hℳ hω ht hT hA hα hωα hp hq
    (PowerlessRelabelMatrix.order_m (Δ := [])) η (member_l ℳ) (fun _ _ => Iff.rfl) f g

/-- 具名稳定关系的真实有限图；层号仍为内部集合参数。 -/
theorem stable_exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ α A p q : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hα : PowerlessStagePair.limit_l α) (hωα : subset_l ω α)
    (hp : member_l ℳ p ω) (hq : member_l ℳ q ω) (n f g : carrier_l ℳ) :
    ∃ D, member_l ℳ D A ∧ edges_l (PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ n) p q f g D := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 7 :=
    { bound := Fin.cases ω (Fin.cases e (Fin.cases T (Fin.cases t₁
        (Fin.cases t₂ (Fin.cases t₃ (fun _ => n)))))), free := fun _ => ω }
  apply edges_exists_l hℳ hω ht hT hA hα hωα hp hq
    (PowerlessStableDiagram.relation_m (parameter_m (n := 7) 0) (parameter_m 1) (parameter_m 2)
      (parameter_m 3) (parameter_m 4) (parameter_m 5) (parameter_m 6)) η _ _ f g
  intro a b
  rw [PowerlessStableDiagram.relation_formula_l hℳ]
  rfl

/-- 原上端点稳定迹在下层中存在，但上端点与原标签图不作为下层成员前提。 -/
theorem trace_exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ α A q : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hα : PowerlessStagePair.limit_l α) (hωα : subset_l ω α)
    (hq : member_l ℳ q ω) (n β g : carrier_l ℳ) :
    ∃ D, member_l ℳ D A ∧ trace_l (fun a => PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ n a β) q g D := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 9 :=
    { bound := Fin.cases ω (Fin.cases e (Fin.cases T (Fin.cases t₁ (Fin.cases t₂ (Fin.cases t₃
        (Fin.cases n (Fin.cases β (fun _ => g)))))))), free := fun _ => ω }
  exact PowerlessStableTrace.exists_l (Γ := List.replicate 9 .set) hℳ hω ht hT hA hα hωα hq η
    (parameter_m (n := 9) 0) (parameter_m 1) (parameter_m 2) (parameter_m 3) (parameter_m 4)
    (parameter_m 5) (parameter_m 6) (parameter_m 7) (parameter_m 8)

/-- 原两图自动实现其精确记录，不额外假设一个源矩阵共同见证。 -/
theorem realizes_l {r : carrier_l ℳ → carrier_l ℳ → Prop} {p q f g D : carrier_l ℳ}
    (hD : edges_l r p q f g D) : PowerlessDiagramRelabelConditions.preserves_l r D f g := by
  intro z hz
  obtain ⟨i, j, a, b, _, _, hij, ha, hb, h⟩ := (hD z).mp hz
  exact ⟨i, j, a, b, hij, ha, hb, h⟩

theorem trace_subset_l {r : carrier_l ℳ → Prop} {q g D : carrier_l ℳ}
    (hD : trace_l r q g D) : subset_l D q := fun i hi => ((hD i).mp hi).1

theorem trace_realizes_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {r : carrier_l ℳ → Prop} {q g B D : carrier_l ℳ}
    (hg : map_l g q B) (hD : trace_l r q g D) :
    ∀ i, member_l ℳ i D → ∀ a, value_l g i a → r a := by
  intro i hi a ha
  obtain ⟨_, b, hb, h⟩ := (hD i).mp hi
  exact PowerlessFunction.value_unique_l hℳ hg hb ha ▸ h

/-- 将指定边的存在式还原为新图在原下标上的逐值关系，避免丢失坐标对应。 -/
theorem preserves_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {r : carrier_l ℳ → carrier_l ℳ → Prop} {p q f g D f₁ g₁ B C : carrier_l ℳ}
    (hD : edges_l r p q f g D) (hf : map_l f₁ p B) (hg : map_l g₁ q C)
    (h : PowerlessDiagramRelabelConditions.preserves_l r D f₁ g₁)
    {i j a b a₁ b₁ : carrier_l ℳ} (hi : member_l ℳ i p) (hj : member_l ℳ j q)
    (ha : value_l f i a) (hb : value_l g j b) (hr : r a b)
    (ha₁ : value_l f₁ i a₁) (hb₁ : value_l g₁ j b₁) : r a₁ b₁ := by
  obtain ⟨z, hz⟩ := PowerlessBasic.ordered_exists_l hℳ i j
  obtain ⟨i₀, j₀, a₀, b₀, hz₀, ha₀, hb₀, hr₀⟩ :=
    h z ((hD z).mpr ⟨i, j, a, b, hi, hj, hz, ha, hb, hr⟩)
  obtain ⟨rfl, rfl⟩ := (PowerlessBasic.ordered_eq_l hℳ hz₀ hz).mp rfl
  have h₁ := PowerlessFunction.value_unique_l hℳ hf ha₀ ha₁
  have h₂ := PowerlessFunction.value_unique_l hℳ hg hb₀ hb₁
  exact h₁ ▸ h₂ ▸ hr₀

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelabelDiagram
