import BMSConstructibleBridge.PowerlessOrdinalRelationAbsolute
import BMSConstructibleBridge.PowerlessOrdinalRecursion

/-!
# 原序数递归公式在传递子域中的语法语义桥

先按原正文显露关系见证 R，再用环境中的关系规格比较子域内的两种前史。
全过程不把子域当作核心模型；实际 R 的域内存在还给出候选有序对闭包，
不把同一个已可推出的条件重复留在公开出口。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessOrdinalRecursionAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ : SortContext ℒ}

theorem presentation_l (φ : Formula ℒ [] (.set :: .set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (f A : carrier_l ℳ) :
    (PowerlessOrdinalRecursion.recursion_m φ).satisfies
      (((PowerlessComprehension.env_l η).pushFree A).pushFree f) ↔
      ∃ R, PowerlessOrdinalRelation.relation_l A R ∧ PowerlessWellRecursionPresentation.recursion_l φ η f A R := by
  simp only [PowerlessOrdinalRecursion.recursion_m, Formula.satisfies,
    PowerlessOrdinalRelation.relation_formula_l, Formula.satisfies_substitute]
  apply exists_congr
  intro R
  apply and_congr Iff.rfl
  rw [← PowerlessWellRecursionPresentation.recursion_formula_l φ η f A R]
  apply Iff.of_eq
  apply congrArg (fun η => (PowerlessWellRecursionPresentation.recursion_m φ).satisfies η)
  apply Env.ext (bound := []) (fun {_} v => nomatch v)
  · intro s v
    match s, v with
    | .set, .here => rfl
    | .set, .there .here => rfl
    | .set, .there (.there .here) => rfl
    | .set, .there (.there (.there v)) => rfl

theorem history_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {B : carrier_l ℳ} {hB : ∃ x, member_l ℳ x B} (hBT : PowerlessNaturalOrder.transitive_l B)
    {A R f D H a : type_l B} (hR : PowerlessOrdinalRelation.relation_l A.val R.val)
    (hf : map_l (ℳ := structure_l B hB) f A D) (ha : member_l (structure_l B hB) a A) :
    PowerlessHistory.history_l (ℳ := structure_l B hB) H f R a ↔
      PowerlessOrdinalRecursion.history_l (ℳ := structure_l B hB) H f a := by
  apply forall_congr'
  intro p
  apply iff_congr Iff.rfl
  apply exists_congr
  intro x
  apply exists_congr
  intro y
  constructor
  · rintro ⟨hp, hx, hy⟩
    exact ⟨hp, ((PowerlessOrdinalRelation.value_l hℳ hR).mp
      ((PowerlessSourceGraphAbsolute.value_l hBT).mp hx)).2.2, hy⟩
  · rintro ⟨hp, hx, hy⟩
    have hf₀ := (PowerlessSourceGraphAbsolute.map_l hBT).mp hf
    have hx₀ := (PowerlessFunction.value_mem_l hℳ hf₀ ((PowerlessSourceGraphAbsolute.value_l hBT).mp hy)).1
    exact ⟨hp, (PowerlessSourceGraphAbsolute.value_l hBT).mpr
      ((PowerlessOrdinalRelation.value_l hℳ hR).mpr ⟨hx₀, ha, hx⟩), hy⟩

theorem recursion_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {B : carrier_l ℳ} {hB : ∃ x, member_l ℳ x B} (hBT : PowerlessNaturalOrder.transitive_l B)
    (φ : Formula ℒ [] (.set :: .set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (structure_l B hB)) Γ.length)
    {A R f : type_l B} (hR : PowerlessOrdinalRelation.relation_l A.val R.val) :
    PowerlessWellRecursionPresentation.recursion_l φ η f A R ↔ PowerlessOrdinalRecursion.recursion_l φ η f A := by
  apply exists_congr
  intro D
  apply and_congr_right
  intro hf
  apply forall_congr'
  intro a
  apply forall_congr'
  intro y
  apply imp_congr_right
  intro hy
  have ha := (PowerlessFunction.value_mem_l hℳ ((PowerlessSourceGraphAbsolute.map_l hBT).mp hf)
    ((PowerlessSourceGraphAbsolute.value_l hBT).mp hy)).1
  exact exists_congr fun H => and_congr (history_l hℳ hBT hR hf ha) Iff.rfl

theorem source_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {B : carrier_l ℳ} {hB : ∃ x, member_l ℳ x B} (hBT : PowerlessNaturalOrder.transitive_l B)
    (φ : Formula ℒ [] (.set :: .set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (structure_l B hB)) Γ.length)
    (f A : type_l B)
    (hR : ∃ R : type_l B, PowerlessOrdinalRelation.relation_l A.val R.val) :
    (PowerlessOrdinalRecursion.recursion_m φ).satisfies
      (((PowerlessComprehension.env_l η).pushFree A).pushFree f) ↔ PowerlessOrdinalRecursion.recursion_l φ η f A := by
  have hP : ∀ p, PowerlessOrdinalRelationAbsolute.cut_l A.val p → member_l ℳ p B := by
    obtain ⟨R, hR⟩ := hR
    exact fun p hp => hBT R.val p R.property ((hR p).mpr hp)
  rw [presentation_l]
  constructor
  · rintro ⟨R, hR, hf⟩
    exact (recursion_l hℳ hBT φ η ((PowerlessOrdinalRelationAbsolute.relation_l hBT hP).mp hR)).mp hf
  · intro hf
    obtain ⟨R, hR⟩ := hR
    exact ⟨R, (PowerlessOrdinalRelationAbsolute.relation_l hBT hP).mpr hR,
      (recursion_l hℳ hBT φ η hR).mpr hf⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessOrdinalRecursionAbsolute
