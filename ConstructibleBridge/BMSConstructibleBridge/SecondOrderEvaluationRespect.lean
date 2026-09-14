import BMSConstructibleBridge.SecondOrderRelatedAssignments

/-!
# 全部内部公式的代表替换不变性

Q 在数域上自反，且相等图 Q 与成员图 R 均对 Q 对应保持真值时，逐项 Q
对应的两个有效赋值在全部模型公式编号上有相同求值。使用实际反例集合。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEvaluationRespect

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (value_l relation_l)
open SecondOrderAssignmentSyntax (valid_l)
open SecondOrderRelatedAssignments (related_l respects_l)
open SecondOrderEvaluationRule (atomic_l conjunction_l existential_l cases_l rule_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def property_l (E Q T : set_l ℳ) (n : num_l ℳ) : Prop :=
  ∀ l c d, valid_l E c l → valid_l E d l → related_l E Q c d →
    (relation_l T n (value_l l c) ↔ relation_l T n (value_l l d))

def formula_m : Formula signature_m [] [.num, .set, .set, .set] :=
  .forallE .num <| .forallE .num <| .forallE .num <|
    .imp (SecondOrderAssignmentSyntax.formula_m (.fvar (.there .here)) (.bvar (.there .here))
      (.bvar (.there (.there .here)))) <|
      .imp (SecondOrderAssignmentSyntax.formula_m (.fvar (.there .here)) (.bvar .here)
        (.bvar (.there (.there .here)))) <|
        .imp (SecondOrderRelatedAssignments.formula_m (.fvar (.there .here)) (.fvar (.there (.there .here)))
          (.bvar (.there .here)) (.bvar .here)) <|
          .iff (SecondOrderEvaluationCongruence.read_m (.fvar (.there (.there (.there .here)))) (.fvar .here)
            (.bvar (.there (.there .here))) (.bvar (.there .here)))
            (SecondOrderEvaluationCongruence.read_m (.fvar (.there (.there (.there .here)))) (.fvar .here)
              (.bvar (.there (.there .here))) (.bvar .here))

theorem pure_m : language_m formula_m = true := pure_language_m _ rfl

theorem formula_l (η : Env ℳ [] [.num, .set, .set, .set]) : Formula.satisfies η formula_m ↔
    property_l (η.freeVal (.there .here)) (η.freeVal (.there (.there .here)))
      (η.freeVal (.there (.there (.there .here)))) (η.freeVal .here) := by
  simp only [formula_m, Formula.satisfies, SecondOrderAssignmentSyntax.raw_l,
    SecondOrderRelatedAssignments.formula_l, SecondOrderEvaluationCongruence.read_l]
  rfl

theorem atomic_l (E Q G : set_l ℳ) (hG : respects_l Q G) (l c d p : num_l ℳ)
    (hc : valid_l E c l) (hd : valid_l E d l) (h : related_l E Q c d) :
    SecondOrderEvaluationRule.atomic_l E G c p ↔ SecondOrderEvaluationRule.atomic_l E G d p := by
  constructor
  · rintro ⟨i, j, x, y, hp, hx, hy, hxy⟩
    obtain ⟨a, ha, _⟩ := hd.1 i (hc.2 i x hx)
    obtain ⟨b, hb, _⟩ := hd.1 j (hc.2 j y hy)
    exact ⟨i, j, a, b, hp, ha, hb, (hG x y a b (h i x a hx ha) (h j y b hy hb)).mp hxy⟩
  · rintro ⟨i, j, a, b, hp, ha, hb, hab⟩
    obtain ⟨x, hx, _⟩ := hc.1 i (hd.2 i a ha)
    obtain ⟨y, hy, _⟩ := hc.1 j (hd.2 j b hb)
    exact ⟨i, j, x, y, hp, hx, hy, (hG x y a b (h i x a hx ha) (h j y b hy hb)).mpr hab⟩

theorem existential_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ} (hE : SecondOrderBinaryPowers.spec_l E)
    (D Q T : set_l ℳ) (hQ : ∀ x, relation_l Q x x) (l c d p : num_l ℳ)
    (hc : valid_l E c l) (hd : valid_l E d l) (h : related_l E Q c d) (hP : property_l E Q T p) :
    SecondOrderEvaluationRule.existential_l E D T l c p ↔ SecondOrderEvaluationRule.existential_l E D T l d p := by
  constructor
  · rintro ⟨x, a, s, hx, ha, rfl, hT⟩
    obtain ⟨b, hb⟩ := SecondOrderAssignmentCongruence.extension_exists_l hℳ hE d l x hd
    have h₀ := SecondOrderRelatedAssignments.extension_l hℳ E Q l c d a b x x h ha hb (hQ x)
    exact ⟨x, b, _, hx, hb, rfl, (hP (succ_l l) a b ha.1 hb.1 h₀).mp hT⟩
  · rintro ⟨x, b, s, hx, hb, rfl, hT⟩
    obtain ⟨a, ha⟩ := SecondOrderAssignmentCongruence.extension_exists_l hℳ hE c l x hc
    have h₀ := SecondOrderRelatedAssignments.extension_l hℳ E Q l c d a b x x h ha hb (hQ x)
    exact ⟨x, a, _, hx, ha, rfl, (hP (succ_l l) a b ha.1 hb.1 h₀).mpr hT⟩

theorem step_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ} (hE : SecondOrderBinaryPowers.spec_l E)
    (D Q R T : set_l ℳ) (h₀ : ∀ x, relation_l Q x x) (hQ : respects_l Q Q) (hR : respects_l Q R)
    (hT : SecondOrderEvaluationEquations.spec_l E D Q R T) (n : num_l ℳ)
    (hI : ∀ i, SecondOrderOrder.lt_l i n → property_l E Q T i) : property_l E Q T n := by
  intro l c d hc hd h
  rw [hT, hT, SecondOrderEvaluationCongruence.state_l hℳ, SecondOrderEvaluationCongruence.state_l hℳ,
    and_iff_right hc, and_iff_right hd]
  apply exists_congr
  intro t
  apply exists_congr
  intro p
  apply and_congr_right
  intro hp
  have hp₀ := (SecondOrderFormulaCode.bounds_l hℳ t p).2
  rw [hp] at hp₀
  have hC : conjunction_l T p (value_l l c) ↔ conjunction_l T p (value_l l d) := by
    apply exists_congr
    intro i
    apply exists_congr
    intro j
    apply and_congr_right
    intro hij
    have h₁ := SecondOrderFormulaCode.children_l hℳ t i j
    rw [hij, hp] at h₁
    exact and_congr (hI i h₁.1 l c d hc hd h) (hI j h₁.2 l c d hc hd h)
  exact or_congr (and_congr Iff.rfl (atomic_l E Q Q hQ l c d p hc hd h))
    (or_congr (and_congr Iff.rfl (atomic_l E Q R hR l c d p hc hd h))
      (or_congr (and_congr Iff.rfl (not_congr (hI p hp₀ l c d hc hd h)))
        (or_congr (and_congr Iff.rfl hC)
          (and_congr Iff.rfl (existential_l hℳ hE D Q T h₀ l c d p hc hd h (hI p hp₀))))))

theorem respect_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ} (hE : SecondOrderBinaryPowers.spec_l E)
    (D Q R T : set_l ℳ) (h₀ : ∀ x, relation_l Q x x) (hQ : respects_l Q Q) (hR : respects_l Q R)
    (hT : SecondOrderEvaluationEquations.spec_l E D Q R T) (n : num_l ℳ) : property_l E Q T n := by
  classical
  let η := (((Env.empty (M := ℳ)).pushFree T).pushFree Q).pushFree E
  obtain ⟨X, hX⟩ := comprehension_l hℳ (.neg formula_m) pure_m η
  have h₁ (i : num_l ℳ) : mem_l i X ↔ ¬ property_l E Q T i :=
    (hX i).trans (not_congr (formula_l (η.pushFree i)))
  by_contra hn
  obtain ⟨i, hi, hM⟩ := SecondOrderMinimum.exists_l hℳ X ⟨n, (h₁ n).mpr hn⟩
  apply (h₁ i).mp hi
  apply step_l hℳ hE D Q R T h₀ hQ hR hT i
  intro j hj
  by_contra h
  exact hM j hj ((h₁ j).mpr h)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEvaluationRespect
