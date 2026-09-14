import BMSConstructibleBridge.SecondOrderEvaluationFixedPoint
import BMSConstructibleBridge.SecondOrderAssignmentCongruence

/-!
# 内部求值的赋值换码不变性

用实际反例集合的最小元推进全部模型编号，而非外部语法树归纳。
只要求两赋值的读取图相同，不把数码唯一性留作隐含前提。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEvaluationCongruence

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (value_l relation_l)
open SecondOrderAssignmentCongruence (same_l)
open SecondOrderEvaluationRule (atomic_l conjunction_l existential_l cases_l rule_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def read_template_m : Formula signature_m [] [.set, .num, .num, .num] :=
  .existsE .num (.conj
    (PrimitiveFormulas.pair_m (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here)))) (.bvar .here))
    (GraphSyntax.edge_m (.fvar .here) (.fvar (.there .here)) (.bvar .here)))

private def bind {Γ Δ : SortContext signature_m} (T : Term signature_m Γ Δ .set)
    (n l c : Term signature_m Γ Δ .num) : Substitution signature_m [] [.set, .num, .num, .num] Γ Δ :=
  .map (fun v => nomatch v) (fun v => match v with
    | .here => T
    | .there .here => n
    | .there (.there .here) => l
    | .there (.there (.there .here)) => c)

def read_m {Γ Δ : SortContext signature_m} (T : Term signature_m Γ Δ .set)
    (n l c : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ := read_template_m.substitute (bind T n l c)

theorem read_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ) (T : Term signature_m Γ Δ .set)
    (n l c : Term signature_m Γ Δ .num) : Formula.satisfies η (read_m T n l c) ↔
      relation_l (T.eval η) (n.eval η) (value_l (l.eval η) (c.eval η)) := by
  simp only [read_m, Formula.satisfies_substitute, read_template_m, Formula.satisfies,
    SecondOrderPairing.formula_l, SecondOrderPairing.edge_l]
  change (∃ s, value_l (l.eval η) (c.eval η) = s ∧ relation_l (T.eval η) (n.eval η) s) ↔ _
  constructor
  · rintro ⟨s, rfl, h⟩
    exact h
  · intro h
    exact ⟨_, rfl, h⟩

def property_l (E T : set_l ℳ) (n : num_l ℳ) : Prop :=
  ∀ l c d, same_l E c d → (relation_l T n (value_l l c) ↔ relation_l T n (value_l l d))

def formula_m : Formula signature_m [] [.num, .set, .set] :=
  .forallE .num <| .forallE .num <| .forallE .num <|
    .imp (SecondOrderAssignmentCongruence.formula_m (.fvar (.there .here)) (.bvar (.there .here)) (.bvar .here))
      (.iff (read_m (.fvar (.there (.there .here))) (.fvar .here) (.bvar (.there (.there .here))) (.bvar (.there .here)))
        (read_m (.fvar (.there (.there .here))) (.fvar .here) (.bvar (.there (.there .here))) (.bvar .here)))

theorem pure_m : language_m formula_m = true := pure_language_m _ rfl

theorem formula_l (η : Env ℳ [] [.num, .set, .set]) : Formula.satisfies η formula_m ↔
    property_l (η.freeVal (.there .here)) (η.freeVal (.there (.there .here))) (η.freeVal .here) := by
  simp only [formula_m, Formula.satisfies, SecondOrderAssignmentCongruence.formula_l, read_l]
  rfl

theorem atomic_congr_l (E Q : set_l ℳ) (c d p : num_l ℳ) (h : same_l E c d) :
    atomic_l E Q c p ↔ atomic_l E Q d p := by
  unfold same_l at h
  unfold atomic_l
  simp only [h]

theorem existential_congr_l (E D T : set_l ℳ) (l c d p : num_l ℳ) (h : same_l E c d) :
    existential_l E D T l c p ↔ existential_l E D T l d p := by
  unfold existential_l
  simp only [SecondOrderAssignmentCongruence.extension_congr_l E c d l _ _ h]

theorem state_l (hℳ : Theory.Models ℳ theory_m) (E D Q R T : set_l ℳ) (n l c : num_l ℳ) :
    rule_l E D Q R T n (value_l l c) ↔ SecondOrderAssignmentSyntax.valid_l E c l ∧
      ∃ t p, SecondOrderFormulaCode.node_l t p = n ∧ cases_l E D Q R T l c t p (value_l l c) := by
  constructor
  · rintro ⟨l', c', h, hc, ht⟩
    obtain ⟨rfl, rfl⟩ := SecondOrderPairingBounds.injective_l hℳ l' c' l c h
    exact ⟨hc, ht⟩
  · rintro ⟨hc, ht⟩
    exact ⟨l, c, rfl, hc, ht⟩

theorem step_l (hℳ : Theory.Models ℳ theory_m) (E D Q R T : set_l ℳ) (n : num_l ℳ)
    (hT : ∀ n a, relation_l T n a ↔ rule_l E D Q R T n a)
    (hI : ∀ i, SecondOrderOrder.lt_l i n → property_l E T i) : property_l E T n := by
  intro l c d h
  rw [hT, hT, state_l hℳ, state_l hℳ]
  apply and_congr (SecondOrderAssignmentCongruence.valid_congr_l E c d l h)
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
    have h₀ := SecondOrderFormulaCode.children_l hℳ t i j
    rw [hij, hp] at h₀
    exact and_congr (hI i h₀.1 l c d h) (hI j h₀.2 l c d h)
  exact or_congr (and_congr Iff.rfl (atomic_congr_l E Q c d p h))
    (or_congr (and_congr Iff.rfl (atomic_congr_l E R c d p h))
      (or_congr (and_congr Iff.rfl (not_congr (hI p hp₀ l c d h)))
        (or_congr (and_congr Iff.rfl hC) (and_congr Iff.rfl (existential_congr_l E D T l c d p h)))))

theorem congr_l (hℳ : Theory.Models ℳ theory_m) (E D Q R T : set_l ℳ)
    (hT : ∀ n a, relation_l T n a ↔ rule_l E D Q R T n a) (n : num_l ℳ) : property_l E T n := by
  classical
  let η := ((Env.empty (M := ℳ)).pushFree T).pushFree E
  obtain ⟨X, hX⟩ := comprehension_l hℳ (.neg formula_m) pure_m η
  have h₀ (i : num_l ℳ) : mem_l i X ↔ ¬ property_l E T i :=
    (hX i).trans (not_congr (formula_l (η.pushFree i)))
  by_contra hn
  obtain ⟨i, hi, hM⟩ := SecondOrderMinimum.exists_l hℳ X ⟨n, (h₀ n).mpr hn⟩
  apply (h₀ i).mp hi
  apply step_l hℳ E D Q R T i hT
  intro j hj
  by_contra h
  exact hM j hj ((h₀ j).mpr h)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEvaluationCongruence
