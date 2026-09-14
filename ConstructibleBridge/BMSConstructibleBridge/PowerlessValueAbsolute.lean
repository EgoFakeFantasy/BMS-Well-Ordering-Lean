import BMSConstructibleBridge.PowerlessSourceGraphAbsolute
import BMSConstructibleBridge.PowerlessEvaluationClause

/-!
# 图坐标、赋值更新与局部查询的传递子域绝对性

有序对见证属于图，其坐标沿两次成员关系回到传递域。不要求图是函数，
也不要求该域有集合论核心或另行含有整个值域集合。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessValueAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {B : carrier_l ℳ}
  {hB : ∃ x, member_l ℳ x B} (hBT : PowerlessNaturalOrder.transitive_l B)

include hBT

theorem coordinates_l {F x y : carrier_l ℳ} (hF : member_l ℳ F B) (h : value_l F x y) :
    member_l ℳ x B ∧ member_l ℳ y B := by
  obtain ⟨p, hp, u, v, _, hv, h⟩ := h
  have hpB := hBT F p hF hp
  have hvB := hBT p v hpB ((h v).mpr (Or.inr rfl))
  exact ⟨hBT v x hvB ((hv x).mpr (Or.inl rfl)), hBT v y hvB ((hv y).mpr (Or.inr rfl))⟩

theorem update_l {f i a g : type_l B} :
    PowerlessAssignmentUpdate.update_l (ℳ := structure_l B hB) f i a g ↔
      PowerlessAssignmentUpdate.update_l f.val i.val a.val g.val := by
  have h₀ : ∀ x y : type_l B,
      ((x = i ∧ y = a) ∨ (x ≠ i ∧ value_l (ℳ := structure_l B hB) f x y)) ↔
        ((x.val = i.val ∧ y.val = a.val) ∨ (x.val ≠ i.val ∧ value_l f.val x.val y.val)) := by
    intro x y
    exact or_congr (and_congr Subtype.ext_iff Subtype.ext_iff)
      (and_congr (not_congr Subtype.ext_iff) (PowerlessSourceGraphAbsolute.value_l hBT))
  constructor
  · intro h x y
    constructor
    · intro hxy
      obtain ⟨hx, hy⟩ := coordinates_l hBT g.property hxy
      exact (h₀ ⟨x, hx⟩ ⟨y, hy⟩).mp
        ((h ⟨x, hx⟩ ⟨y, hy⟩).mp ((PowerlessSourceGraphAbsolute.value_l hBT).mpr hxy))
    · intro hxy
      have h₁ : member_l ℳ x B ∧ member_l ℳ y B := by
        rcases hxy with ⟨rfl, rfl⟩ | ⟨_, hxy⟩
        · exact ⟨i.property, a.property⟩
        · exact coordinates_l hBT f.property hxy
      exact (PowerlessSourceGraphAbsolute.value_l hBT).mp
        ((h ⟨x, h₁.1⟩ ⟨y, h₁.2⟩).mpr ((h₀ ⟨x, h₁.1⟩ ⟨y, h₁.2⟩).mpr hxy))
  · intro h x y
    exact (PowerlessSourceGraphAbsolute.value_l hBT).trans ((h x.val y.val).trans (h₀ x y).symm)

theorem query_l {H n f : type_l B} :
    PowerlessEvaluationClause.query_l (ℳ := structure_l B hB) H n f ↔
      PowerlessEvaluationClause.query_l H.val n.val f.val := by
  constructor
  · rintro ⟨Y, hY, hf⟩
    exact ⟨Y.val, (PowerlessSourceGraphAbsolute.value_l hBT).mp hY, hf⟩
  · rintro ⟨Y, hY, hf⟩
    exact ⟨⟨Y, (coordinates_l hBT H.property hY).2⟩, (PowerlessSourceGraphAbsolute.value_l hBT).mpr hY, hf⟩

theorem equal_l {f i j : type_l B} :
    PowerlessEvaluationClause.equal_l (ℳ := structure_l B hB) f i j ↔
      PowerlessEvaluationClause.equal_l f.val i.val j.val := by
  constructor
  · rintro ⟨a, hi, hj⟩
    exact ⟨a.val, (PowerlessSourceGraphAbsolute.value_l hBT).mp hi, (PowerlessSourceGraphAbsolute.value_l hBT).mp hj⟩
  · rintro ⟨a, hi, hj⟩
    exact ⟨⟨a, (coordinates_l hBT f.property hi).2⟩,
      (PowerlessSourceGraphAbsolute.value_l hBT).mpr hi, (PowerlessSourceGraphAbsolute.value_l hBT).mpr hj⟩

theorem update_source_l {Γ Δ : SortContext ℒ} (η : Env (structure_l B hB) Γ Δ)
    (f i a g : Term ℒ Γ Δ .set) :
    Formula.satisfies η (PowerlessAssignmentUpdate.update_m f i a g) ↔
      PowerlessAssignmentUpdate.update_l (f.eval η).val (i.eval η).val (a.eval η).val (g.eval η).val := by
  exact (PowerlessAssignmentUpdate.update_formula_l η f i a g).trans (update_l hBT)

theorem member_l {f i j : type_l B} :
    PowerlessEvaluationClause.member_l (ℳ := structure_l B hB) f i j ↔
      PowerlessEvaluationClause.member_l f.val i.val j.val := by
  constructor
  · rintro ⟨a, b, hi, hj, hab⟩
    exact ⟨a.val, b.val, (PowerlessSourceGraphAbsolute.value_l hBT).mp hi,
      (PowerlessSourceGraphAbsolute.value_l hBT).mp hj, hab⟩
  · rintro ⟨a, b, hi, hj, hab⟩
    exact ⟨⟨a, (coordinates_l hBT f.property hi).2⟩, ⟨b, (coordinates_l hBT f.property hj).2⟩,
      (PowerlessSourceGraphAbsolute.value_l hBT).mpr hi, (PowerlessSourceGraphAbsolute.value_l hBT).mpr hj, hab⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessValueAbsolute
