import BMSConstructibleBridge.PowerlessBasic
import BMSConstructibleBridge.PowerlessComprehension

/-!
# 用收集而非幂集构造笛卡尔积

先收集一个固定左坐标的有序对行，再收集全部行并取并。
两次精确像集均消费实际纯公式与唯一性证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessProduct

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def row_m {Γ Δ : SortContext ℒ} (a b c : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.iff (SecondOrderObjectSyntax.member_m (.bvar .here) (c.weakenBound SetTheory.SetSort.set))
    (.existsE .set (.conj (SecondOrderObjectSyntax.member_m (.bvar .here)
      ((b.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set))
      (SecondOrderObjectSyntax.ordered_m
        ((a.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set)
        (.bvar .here) (.bvar (.there .here))))))

def row_l (a b c : carrier_l ℳ) : Prop :=
  ∀ p, member_l ℳ p c ↔ ∃ y, member_l ℳ y b ∧ ordered_l a y p

def product_l (a b c : carrier_l ℳ) : Prop :=
  ∀ p, member_l ℳ p c ↔ ∃ x, member_l ℳ x a ∧ ∃ y, member_l ℳ y b ∧ ordered_l x y p

theorem row_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (a b c : Term ℒ Γ Δ .set) :
    Formula.satisfies η (row_m a b c) ↔ row_l (a.eval η) (b.eval η) (c.eval η) := by
  simp only [row_m, Formula.satisfies, SecondOrderObjectSyntax.member_m, Arguments.eval,
    ordered_formula_l, Term.eval_weakenBound]
  rfl

theorem row_exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (a b : carrier_l ℳ) :
    ∃ c, row_l a b c := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 1 :=
    { bound := fun _ => a, free := fun _ => b }
  let φ : Formula ℒ [] [.set, .set, .set] :=
    SecondOrderObjectSyntax.ordered_m (.fvar (.there (.there .here)))
      (.fvar (.there .here)) (.fvar .here)
  have h : ∀ y p, φ.satisfies (((PowerlessComprehension.env_l η).pushFree y).pushFree p) ↔
      ordered_l a y p := by
    intro y p
    dsimp only [φ]
    rw [ordered_formula_l]
    rfl
  obtain ⟨c, hc⟩ := PowerlessComprehension.image_l hℳ φ η b
    (fun y _ => (PowerlessBasic.ordered_exists_l hℳ a y).imp fun p hp => (h y p).mpr hp)
    (fun y _ p q hp hq => PowerlessBasic.ordered_unique_l hℳ ((h y p).mp hp) ((h y q).mp hq))
  exact ⟨c, fun p => (hc p).trans (exists_congr fun y => and_congr Iff.rfl (h y p))⟩

theorem row_unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {a b c d : carrier_l ℳ} (hc : row_l a b c) (hd : row_l a b d) : c = d := by
  apply (PowerlessTheory.ext_l hℳ).eq_of_same_members
  intro p
  exact (hc p).trans (hd p).symm

theorem family_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (a b : carrier_l ℳ) :
    ∃ c, ∀ d, member_l ℳ d c ↔ ∃ x, member_l ℳ x a ∧ row_l x b d := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 1 :=
    { bound := fun _ => b, free := fun _ => a }
  let φ : Formula ℒ [] [.set, .set, .set] :=
    row_m (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)
  have h : ∀ x d, φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree d) ↔
      row_l x b d := by
    intro x d
    dsimp only [φ]
    rw [row_formula_l]
    rfl
  obtain ⟨c, hc⟩ := PowerlessComprehension.image_l hℳ φ η a
    (fun x _ => (row_exists_l hℳ x b).imp fun d hd => (h x d).mpr hd)
    (fun x _ d e hd he => row_unique_l hℳ ((h x d).mp hd) ((h x e).mp he))
  exact ⟨c, fun d => (hc d).trans (exists_congr fun x => and_congr Iff.rfl (h x d))⟩

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (a b : carrier_l ℳ) :
    ∃ c, product_l a b c := by
  obtain ⟨d, hd⟩ := family_l hℳ a b
  obtain ⟨c, hc⟩ := PowerlessBasic.union_l hℳ d
  refine ⟨c, fun p => (hc p).trans ?_⟩
  constructor
  · rintro ⟨e, he, hp⟩
    obtain ⟨x, hx, h₀⟩ := (hd e).mp he
    obtain ⟨y, hy, h₁⟩ := (h₀ p).mp hp
    exact ⟨x, hx, y, hy, h₁⟩
  · rintro ⟨x, hx, y, hy, h₀⟩
    obtain ⟨e, he⟩ := row_exists_l hℳ x b
    exact ⟨e, (hd e).mpr ⟨x, hx, he⟩, (he p).mpr ⟨y, hy, h₀⟩⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessProduct
