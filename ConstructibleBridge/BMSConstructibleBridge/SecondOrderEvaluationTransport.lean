import BMSConstructibleBridge.SecondOrderEvaluationRespect

/-!
# 两个内部数域呈现之间的全部公式求值保持

不同的相等图、成员图及量词域由内部关系 K 对应；K 在两侧量词域全域，
两种原子真值保持。由实际反例集合的最小元证明全部内部编号的迁移，不只
对外部 AST 归纳。前提全部显式，本模块尚不交付枚举无关的 Def 对象定理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEvaluationTransport

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (value_l relation_l)
open SecondOrderAssignmentSyntax (valid_l)
open SecondOrderRelatedAssignments (related_l)
open SecondOrderEvaluationRule (conjunction_l existential_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 两个不同原子图在对应的两对参数上保持真值。 -/
def atoms_l (K G H : set_l ℳ) : Prop := ∀ x y a b,
  relation_l K x a → relation_l K y b → (relation_l G x y ↔ relation_l H a b)

def property_l (E K T U : set_l ℳ) (n : num_l ℳ) : Prop :=
  ∀ l c d, valid_l E c l → valid_l E d l → related_l E K c d →
    (relation_l T n (value_l l c) ↔ relation_l U n (value_l l d))

def formula_m : Formula signature_m [] [.num, .set, .set, .set, .set] :=
  .forallE .num <| .forallE .num <| .forallE .num <|
    .imp (SecondOrderAssignmentSyntax.formula_m (.fvar (.there .here))
      (.bvar (.there .here)) (.bvar (.there (.there .here)))) <|
      .imp (SecondOrderAssignmentSyntax.formula_m (.fvar (.there .here))
        (.bvar .here) (.bvar (.there (.there .here)))) <|
        .imp (SecondOrderRelatedAssignments.formula_m (.fvar (.there .here))
          (.fvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)) <|
          .iff (SecondOrderEvaluationCongruence.read_m (.fvar (.there (.there (.there .here))))
            (.fvar .here) (.bvar (.there (.there .here))) (.bvar (.there .here)))
            (SecondOrderEvaluationCongruence.read_m (.fvar (.there (.there (.there (.there .here)))))
              (.fvar .here) (.bvar (.there (.there .here))) (.bvar .here))

theorem pure_m : language_m formula_m = true := pure_language_m _ rfl

theorem formula_l (η : Env ℳ [] [.num, .set, .set, .set, .set]) : formula_m.satisfies η ↔
    property_l (η.freeVal (.there .here)) (η.freeVal (.there (.there .here)))
      (η.freeVal (.there (.there (.there .here))))
      (η.freeVal (.there (.there (.there (.there .here))))) (η.freeVal .here) := by
  simp only [formula_m, Formula.satisfies, SecondOrderAssignmentSyntax.raw_l,
    SecondOrderRelatedAssignments.formula_l, SecondOrderEvaluationCongruence.read_l]
  rfl

theorem atomic_l (E K G H : set_l ℳ) (hGH : atoms_l K G H) (l c d p : num_l ℳ)
    (hc : valid_l E c l) (hd : valid_l E d l) (h : related_l E K c d) :
    SecondOrderEvaluationRule.atomic_l E G c p ↔ SecondOrderEvaluationRule.atomic_l E H d p := by
  constructor
  · rintro ⟨i, j, x, y, hp, hx, hy, hxy⟩
    obtain ⟨a, ha, _⟩ := hd.1 i (hc.2 i x hx)
    obtain ⟨b, hb, _⟩ := hd.1 j (hc.2 j y hy)
    exact ⟨i, j, a, b, hp, ha, hb, (hGH x y a b (h i x a hx ha) (h j y b hy hb)).mp hxy⟩
  · rintro ⟨i, j, a, b, hp, ha, hb, hab⟩
    obtain ⟨x, hx, _⟩ := hc.1 i (hd.2 i a ha)
    obtain ⟨y, hy, _⟩ := hc.1 j (hd.2 j b hb)
    exact ⟨i, j, x, y, hp, hx, hy, (hGH x y a b (h i x a hx ha) (h j y b hy hb)).mpr hab⟩

theorem existential_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
    (hE : SecondOrderBinaryPowers.spec_l E) (D D' K T U : set_l ℳ)
    (hL : ∀ x, mem_l x D → ∃ y, mem_l y D' ∧ relation_l K x y)
    (hR : ∀ y, mem_l y D' → ∃ x, mem_l x D ∧ relation_l K x y)
    (l c d p : num_l ℳ) (hc : valid_l E c l) (hd : valid_l E d l)
    (h : related_l E K c d) (hP : property_l E K T U p) :
    SecondOrderEvaluationRule.existential_l E D T l c p ↔
      SecondOrderEvaluationRule.existential_l E D' U l d p := by
  constructor
  · rintro ⟨x, a, s, hx, ha, rfl, hT⟩
    obtain ⟨y, hy, hxy⟩ := hL x hx
    obtain ⟨b, hb⟩ := SecondOrderAssignmentCongruence.extension_exists_l hℳ hE d l y hd
    have h₀ := SecondOrderRelatedAssignments.extension_l hℳ E K l c d a b x y h ha hb hxy
    exact ⟨y, b, _, hy, hb, rfl, (hP (succ_l l) a b ha.1 hb.1 h₀).mp hT⟩
  · rintro ⟨y, b, s, hy, hb, rfl, hU⟩
    obtain ⟨x, hx, hxy⟩ := hR y hy
    obtain ⟨a, ha⟩ := SecondOrderAssignmentCongruence.extension_exists_l hℳ hE c l x hc
    have h₀ := SecondOrderRelatedAssignments.extension_l hℳ E K l c d a b x y h ha hb hxy
    exact ⟨x, a, _, hx, ha, rfl, (hP (succ_l l) a b ha.1 hb.1 h₀).mpr hU⟩

theorem step_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
    (hE : SecondOrderBinaryPowers.spec_l E) (D D' K Q Q' R R' T U : set_l ℳ)
    (hL : ∀ x, mem_l x D → ∃ y, mem_l y D' ∧ relation_l K x y)
    (hR : ∀ y, mem_l y D' → ∃ x, mem_l x D ∧ relation_l K x y)
    (hQ : atoms_l K Q Q') (hM : atoms_l K R R')
    (hT : SecondOrderEvaluationEquations.spec_l E D Q R T)
    (hU : SecondOrderEvaluationEquations.spec_l E D' Q' R' U) (n : num_l ℳ)
    (hI : ∀ i, SecondOrderOrder.lt_l i n → property_l E K T U i) : property_l E K T U n := by
  intro l c d hc hd h
  rw [hT, hU, SecondOrderEvaluationCongruence.state_l hℳ,
    SecondOrderEvaluationCongruence.state_l hℳ, and_iff_right hc, and_iff_right hd]
  apply exists_congr
  intro t
  apply exists_congr
  intro p
  apply and_congr_right
  intro hp
  have hp₀ := (SecondOrderFormulaCode.bounds_l hℳ t p).2
  rw [hp] at hp₀
  have hC : conjunction_l T p (value_l l c) ↔ conjunction_l U p (value_l l d) := by
    apply exists_congr
    intro i
    apply exists_congr
    intro j
    apply and_congr_right
    intro hij
    have h₁ := SecondOrderFormulaCode.children_l hℳ t i j
    rw [hij, hp] at h₁
    exact and_congr (hI i h₁.1 l c d hc hd h) (hI j h₁.2 l c d hc hd h)
  exact or_congr (and_congr Iff.rfl (atomic_l E K Q Q' hQ l c d p hc hd h))
    (or_congr (and_congr Iff.rfl (atomic_l E K R R' hM l c d p hc hd h))
      (or_congr (and_congr Iff.rfl (not_congr (hI p hp₀ l c d hc hd h)))
        (or_congr (and_congr Iff.rfl hC)
          (and_congr Iff.rfl (existential_l hℳ hE D D' K T U hL hR l c d p hc hd h (hI p hp₀))))))

theorem transport_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
    (hE : SecondOrderBinaryPowers.spec_l E) (D D' K Q Q' R R' T U : set_l ℳ)
    (hL : ∀ x, mem_l x D → ∃ y, mem_l y D' ∧ relation_l K x y)
    (hR : ∀ y, mem_l y D' → ∃ x, mem_l x D ∧ relation_l K x y)
    (hQ : atoms_l K Q Q') (hM : atoms_l K R R')
    (hT : SecondOrderEvaluationEquations.spec_l E D Q R T)
    (hU : SecondOrderEvaluationEquations.spec_l E D' Q' R' U) (n : num_l ℳ) :
    property_l E K T U n := by
  classical
  let η := ((((Env.empty (M := ℳ)).pushFree U).pushFree T).pushFree K).pushFree E
  obtain ⟨X, hX⟩ := comprehension_l hℳ (.neg formula_m) pure_m η
  have h₁ i : mem_l i X ↔ ¬ property_l E K T U i :=
    (hX i).trans (not_congr (formula_l (η.pushFree i)))
  by_contra hn
  obtain ⟨i, hi, hMin⟩ := SecondOrderMinimum.exists_l hℳ X ⟨n, (h₁ n).mpr hn⟩
  apply (h₁ i).mp hi
  apply step_l hℳ hE D D' K Q Q' R R' T U hL hR hQ hM hT hU i
  intro j hj
  by_contra h
  exact hMin j hj ((h₁ j).mpr h)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEvaluationTransport
