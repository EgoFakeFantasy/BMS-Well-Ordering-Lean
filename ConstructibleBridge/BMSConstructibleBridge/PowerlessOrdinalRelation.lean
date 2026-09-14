import BMSConstructibleBridge.PowerlessOrdinal
import BMSConstructibleBridge.PowerlessProduct
import BMSConstructibleBridge.PowerlessHistory

/-!
# 内部序数上的隶属关系图

从 A×A 分离实际的 ∈ 图，核验它在内部序数上良序，并识别前驱域。
因此通用集合关系递归可以直接作用于上游内部序数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessOrdinalRelation

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def relation_l (A R : carrier_l ℳ) : Prop :=
  ∀ p, member_l ℳ p R ↔ ∃ x y, member_l ℳ x A ∧ member_l ℳ y A ∧ member_l ℳ x y ∧ ordered_l x y p

def relation_m {Γ Δ : SortContext ℒ} (A R : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let A₃ := ((A.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .forallE .set (.iff (SecondOrderObjectSyntax.member_m (.bvar .here) (R.weakenBound SetTheory.SetSort.set))
    (.existsE .set (.existsE .set (.conj (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) A₃)
      (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) A₃)
      (.conj (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (.bvar .here))
        (SecondOrderObjectSyntax.ordered_m (.bvar (.there .here)) (.bvar .here) (.bvar (.there (.there .here))))))))))

theorem relation_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (A R : Term ℒ Γ Δ .set) :
    (relation_m A R).satisfies η ↔ relation_l (A.eval η) (R.eval η) := by
  simp only [relation_m, relation_l, Formula.satisfies, ordered_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (A : carrier_l ℳ) : ∃ R, relation_l A R := by
  obtain ⟨P, hP⟩ := PowerlessProduct.exists_l hℳ A A
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 0 :=
    { bound := Fin.elim0, free := fun _ => A }
  let φ : Formula ℒ [] [.set] := .existsE .set (.existsE .set (.conj
    (SecondOrderObjectSyntax.ordered_m (.bvar (.there .here)) (.bvar .here) (.fvar .here))
    (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (.bvar .here))))
  have h : ∀ p, φ.satisfies ((PowerlessComprehension.env_l η).pushFree p) ↔
      ∃ x y, ordered_l x y p ∧ member_l ℳ x y := by
    intro p
    simp only [φ, Formula.satisfies, ordered_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval]
    rfl
  obtain ⟨R, hR⟩ := PowerlessComprehension.separation_l hℳ φ η P
  refine ⟨R, fun p => (hR p).trans ((and_congr Iff.rfl (h p)).trans ?_)⟩
  constructor
  · rintro ⟨hp, x, y, hp₀, hxy⟩
    obtain ⟨a, ha, b, hb, hp₁⟩ := (hP p).mp hp
    obtain ⟨h₀, h₁⟩ := (PowerlessBasic.ordered_eq_l hℳ hp₀ hp₁).mp rfl
    subst a
    subst b
    exact ⟨x, y, ha, hb, hxy, hp₀⟩
  · rintro ⟨x, y, hx, hy, hxy, hp⟩
    exact ⟨(hP p).mpr ⟨x, hx, y, hy, hp⟩, x, y, hp, hxy⟩

theorem unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {A R S : carrier_l ℳ} (hR : relation_l A R) (hS : relation_l A S) : R = S :=
  (PowerlessTheory.ext_l hℳ).eq_of_same_members R S (fun p => (hR p).trans (hS p).symm)

theorem value_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {A R x y : carrier_l ℳ} (hR : relation_l A R) :
    ThirdOrderSemantics.value_l R x y ↔ member_l ℳ x A ∧ member_l ℳ y A ∧ member_l ℳ x y := by
  constructor
  · rintro ⟨p, hp, h₀⟩
    obtain ⟨a, b, ha, hb, hab, h₁⟩ := (hR p).mp hp
    obtain ⟨h₂, h₃⟩ := (PowerlessBasic.ordered_eq_l hℳ h₀ h₁).mp rfl
    subst a
    subst b
    exact ⟨ha, hb, hab⟩
  · rintro ⟨hx, hy, hxy⟩
    obtain ⟨p, hp⟩ := PowerlessBasic.ordered_exists_l hℳ x y
    exact ⟨p, (hR p).mpr ⟨x, y, hx, hy, hxy, hp⟩, hp⟩

theorem wellOrder_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {A R : carrier_l ℳ} (hA : PowerlessOrdinal.ordinal_l A) (hR : relation_l A R) :
    ThirdOrderSemantics.wellOrder_l A R := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x _ hx
    have h := ((value_l hℳ hR).mp hx).2.2
    exact PowerlessNatural.asymmetry_l hℳ h h
  · intro x y z h hx hy
    exact (value_l hℳ hR).mpr ⟨h.1, h.2.2,
      PowerlessOrdinal.transitive_l (PowerlessOrdinal.mem_l hA h.2.2) y x
        ((value_l hℳ hR).mp hy).2.2 ((value_l hℳ hR).mp hx).2.2⟩
  · intro x y h
    rcases PowerlessOrdinal.compare_l hℳ hA h.1 h.2 with h₀ | h₀ | h₀
    · exact Or.inl ((value_l hℳ hR).mpr ⟨h.1, h.2, h₀⟩)
    · exact Or.inr (Or.inl h₀)
    · exact Or.inr (Or.inr ((value_l hℳ hR).mpr ⟨h.2, h.1, h₀⟩))
  · intro B h
    obtain ⟨x, hx, h₀⟩ := PowerlessBasic.foundation_l hℳ h.2
    exact ⟨x, hx, fun y hy h₁ => h₀ y ((value_l hℳ hR).mp h₁).2.2 hy⟩

theorem predecessor_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {A R a : carrier_l ℳ} (hA : PowerlessOrdinal.ordinal_l A) (hR : relation_l A R)
    (ha : member_l ℳ a A) : PowerlessInitialSegment.predecessor_l a A R a := by
  intro x
  constructor
  · intro hx
    have hx₀ := PowerlessOrdinal.transitive_l hA a x ha hx
    exact ⟨hx₀, (value_l hℳ hR).mpr ⟨hx₀, ha, hx⟩⟩
  · rintro ⟨_, hx⟩
    exact ((value_l hℳ hR).mp hx).2.2

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessOrdinalRelation
