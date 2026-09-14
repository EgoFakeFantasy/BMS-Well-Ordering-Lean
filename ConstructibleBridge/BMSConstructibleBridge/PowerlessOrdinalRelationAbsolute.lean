import BMSConstructibleBridge.PowerlessSourceGraphAbsolute
import BMSConstructibleBridge.PowerlessOrdinalRelation
import BMSConstructibleBridge.PowerlessOperatorClosure

/-!
# 原序数关系图的成员公式及传递子域绝对性

逐点成员条件的两个坐标由定义域参数取回。全称关系判定还须取回任意
满足该条件的有序对；不能仅凭坐标在域内就断言有序对也在域内。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessOrdinalRelationAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def cut_l (A p : carrier_l ℳ) : Prop :=
  ∃ x y, member_l ℳ x A ∧ member_l ℳ y A ∧ member_l ℳ x y ∧ ordered_l x y p

def cut_m {Γ Δ : SortContext ℒ} (A p : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := (t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .existsE .set (.existsE .set (.conj (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (w A))
    (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) (w A))
      (.conj (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (.bvar .here))
        (SecondOrderObjectSyntax.ordered_m (.bvar (.there .here)) (.bvar .here) (w p))))))

theorem cut_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (A p : Term ℒ Γ Δ .set) :
    (cut_m A p).satisfies η ↔ cut_l (A.eval η) (p.eval η) := by
  simp only [cut_m, cut_l, Formula.satisfies, ordered_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

theorem cut_absolute_l {B : carrier_l ℳ} {hB : ∃ x, member_l ℳ x B}
    (hBT : PowerlessNaturalOrder.transitive_l B) {A p : type_l B} :
    cut_l (ℳ := structure_l B hB) A p ↔ cut_l A.val p.val := by
  constructor
  · rintro ⟨x, y, hx, hy, hxy, hp⟩
    exact ⟨x.val, y.val, hx, hy, hxy, (PowerlessSourceGraphAbsolute.ordered_l hBT).mp hp⟩
  · rintro ⟨x, y, hx, hy, hxy, hp⟩
    exact ⟨⟨x, hBT A.val x A.property hx⟩, ⟨y, hBT A.val y A.property hy⟩, hx, hy, hxy,
      (PowerlessSourceGraphAbsolute.ordered_l hBT).mpr hp⟩

theorem relation_l {B : carrier_l ℳ} {hB : ∃ x, member_l ℳ x B}
    (hBT : PowerlessNaturalOrder.transitive_l B) {A R : type_l B}
    (hP : ∀ p, cut_l A.val p → member_l ℳ p B) :
    PowerlessOrdinalRelation.relation_l (ℳ := structure_l B hB) A R ↔
      PowerlessOrdinalRelation.relation_l A.val R.val := by
  constructor
  · intro h p
    constructor
    · intro hp
      have hpB := hBT R.val p R.property hp
      exact (cut_absolute_l hBT).mp ((h ⟨p, hpB⟩).mp hp)
    · intro hp
      exact (h ⟨p, hP p hp⟩).mpr ((cut_absolute_l hBT).mpr hp)
  · intro h p
    exact (h p.val).trans (cut_absolute_l hBT).symm

theorem source_l {B : carrier_l ℳ} {hB : ∃ x, member_l ℳ x B}
    (hBT : PowerlessNaturalOrder.transitive_l B) {Γ Δ : SortContext ℒ}
    (η : Env (structure_l B hB) Γ Δ) (A R : Term ℒ Γ Δ .set)
    (hP : ∀ p, cut_l (A.eval η).val p → member_l ℳ p B) :
    (PowerlessOrdinalRelation.relation_m A R).satisfies η ↔
      PowerlessOrdinalRelation.relation_l (A.eval η).val (R.eval η).val :=
  (PowerlessOrdinalRelation.relation_formula_l η A R).trans (relation_l hBT hP)

theorem operator_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ B D A R : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hD : PowerlessEvaluationOperator.operator_l ω e T t₁ t₂ t₃ B D)
    (hBT : PowerlessNaturalOrder.transitive_l B) (hA : member_l ℳ A B)
    (hR : PowerlessOrdinalRelation.relation_l A R) (hRB : subset_l R B) : member_l ℳ R D := by
  let hB : ∃ x, member_l ℳ x B := ⟨A, hA⟩
  let η : Env (structure_l B hB) [.set] [] := Env.empty.pushBound ⟨A, hA⟩
  let φ : Formula ℒ [.set, .set] [] := cut_m (.bvar (.there .here)) (.bvar .here)
  apply PowerlessOperatorClosure.specified_l hℳ hω ht hT hD φ η
  intro p
  have h₀ (hp : member_l ℳ p B) : φ.satisfies (η.pushBound ⟨p, hp⟩) ↔ member_l ℳ p R := by
    rw [cut_formula_l]
    exact (cut_absolute_l hBT).trans (hR p).symm
  constructor
  · intro hp
    exact ⟨hRB p hp, (h₀ (hRB p hp)).mpr hp⟩
  · rintro ⟨hp, h⟩
    exact (h₀ hp).mp h

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessOrdinalRelationAbsolute
