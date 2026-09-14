import BMSConstructibleBridge.SecondOrderSequenceSyntax

/-!
# 数值编码的内部迭代历史

历史码是一个模型数，读取、有限函数性及转移方程全部用数量词表达。幂图和
转移图是显式实数参数；没有把此编码等同于原编译器的 β 编码或 PRA 证明码。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderNumberHistory

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def entry_l {E : set_l ℳ} (hE : SecondOrderBinaryPowers.spec_l E) (c i b : num_l ℳ) : Prop :=
  SecondOrderDigit.holds_l c (SecondOrderPowers.value_l hE (value_l i b))

def spec_l {E : set_l ℳ} (hE : SecondOrderBinaryPowers.spec_l E) (F : set_l ℳ)
    (c a n : num_l ℳ) : Prop :=
  (∀ i, SecondOrderOrder.lt_l i (succ_l n) → ∃! b, entry_l hE c i b) ∧
    entry_l hE c (zero_l ℳ) a ∧
      ∀ i b d, SecondOrderOrder.lt_l i n → entry_l hE c i b →
        entry_l hE c (succ_l i) d → relation_l F b d

private def zero {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .zero .nil

private def succ {Γ Δ : SortContext signature_m} (s : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num := Term.app (σ := signature_m) .succ (.cons s .nil)

private def entry {Γ : SortContext signature_m} (i b : Term signature_m Γ [.set, .set, .num, .num, .num] .num) :
    Formula signature_m Γ [.set, .set, .num, .num, .num] :=
  SecondOrderSequenceSyntax.formula_m (.fvar .here) (.fvar (.there (.there .here))) i b

/-- 自由参数为幂图、转移图、历史码、初值、末索引。 -/
def formula_m : Formula signature_m [] [.set, .set, .num, .num, .num] :=
  .conj
    (.forallE .num (.imp
      (PrimitiveFormulas.lt_m (.bvar .here) (succ (.fvar (.there (.there (.there (.there .here)))))))
      (.existsE .num (.conj (entry (.bvar (.there .here)) (.bvar .here))
        (.forallE .num (.imp (entry (.bvar (.there (.there .here))) (.bvar .here))
          (.equal (.bvar .here) (.bvar (.there .here)))))))))
    (.conj (entry zero (.fvar (.there (.there (.there .here)))))
      (.forallE .num (.forallE .num (.forallE .num (.imp
        (PrimitiveFormulas.lt_m (.bvar (.there (.there .here)))
          (.fvar (.there (.there (.there (.there .here))))))
        (.imp (entry (.bvar (.there (.there .here))) (.bvar (.there .here)))
          (.imp (entry (succ (.bvar (.there (.there .here)))) (.bvar .here))
            (GraphSyntax.edge_m (.fvar (.there .here)) (.bvar (.there .here)) (.bvar .here)))))))))

theorem pure_m : language_m formula_m = true := pure_language_m _ rfl

theorem formula_l (η : Env ℳ [] [.set, .set, .num, .num, .num])
    (hE : SecondOrderBinaryPowers.spec_l (η.freeVal .here)) :
    Formula.satisfies η formula_m ↔ spec_l hE (η.freeVal (.there .here))
      (η.freeVal (.there (.there .here))) (η.freeVal (.there (.there (.there .here))))
      (η.freeVal (.there (.there (.there (.there .here))))) := by
  simp only [formula_m, Formula.satisfies, entry, SecondOrderSequenceSyntax.raw_l,
    SecondOrderOrder.formula_l, SecondOrderPairing.edge_l]
  let E := η.freeVal .here
  let F := η.freeVal (.there .here)
  let c := η.freeVal (.there (.there .here))
  let a := η.freeVal (.there (.there (.there .here)))
  let n := η.freeVal (.there (.there (.there (.there .here))))
  change ((∀ i, SecondOrderOrder.lt_l i (succ_l n) → ∃ b,
    SecondOrderSequenceSyntax.read_l E c i b ∧
      ∀ d, SecondOrderSequenceSyntax.read_l E c i d → d = b) ∧
    SecondOrderSequenceSyntax.read_l E c (zero_l ℳ) a ∧
      ∀ i b d, SecondOrderOrder.lt_l i n → SecondOrderSequenceSyntax.read_l E c i b →
        SecondOrderSequenceSyntax.read_l E c (succ_l i) d → relation_l F b d) ↔ _
  have h (i b : num_l ℳ) : SecondOrderSequenceSyntax.read_l E c i b ↔ entry_l hE c i b :=
    SecondOrderSequenceSyntax.read_eq_l hE c i b
  simp only [h]
  rfl

private def bind {Γ Δ : SortContext signature_m} (E F : Term signature_m Γ Δ .set)
    (c a n : Term signature_m Γ Δ .num) :
    Substitution signature_m [] [.set, .set, .num, .num, .num] Γ Δ :=
  .map (fun v => nomatch v) (fun v => match v with
    | .here => E
    | .there .here => F
    | .there (.there .here) => c
    | .there (.there (.there .here)) => a
    | .there (.there (.there (.there .here))) => n)

def instantiate_m {Γ Δ : SortContext signature_m} (E F : Term signature_m Γ Δ .set)
    (c a n : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  formula_m.substitute (bind E F c a n)

theorem instantiate_pure_m {Γ Δ : SortContext signature_m} (E F : Term signature_m Γ Δ .set)
    (c a n : Term signature_m Γ Δ .num) (hE : pure_term_m E = true) (hF : pure_term_m F = true)
    (hc : pure_term_m c = true) (ha : pure_term_m a = true) (hn : pure_term_m n = true) :
    language_m (instantiate_m E F c a n) = true := by
  refine (SecondOrderSubstitution.form_subst_m formula_m _ _ ?_ ?_).trans pure_m
  · intro s v
    nomatch v
  · intro s v
    match v with
    | .here => exact hE
    | .there .here => exact hF
    | .there (.there .here) => exact hc
    | .there (.there (.there .here)) => exact ha
    | .there (.there (.there (.there .here))) => exact hn

theorem instantiate_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (E F : Term signature_m Γ Δ .set) (c a n : Term signature_m Γ Δ .num)
    (hE : SecondOrderBinaryPowers.spec_l (E.eval η)) :
    Formula.satisfies η (instantiate_m E F c a n) ↔
      spec_l hE (F.eval η) (c.eval η) (a.eval η) (n.eval η) := by
  rw [instantiate_m, Formula.satisfies_substitute, formula_l _ hE]
  rfl

/-- 把任一内部实数历史的完整有限图转为数码，并保留迭代规格。 -/
theorem encode_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
    (hE : SecondOrderBinaryPowers.spec_l E) (F H : set_l ℳ) (a n : num_l ℳ)
    (hH : SecondOrderHistory.spec_l F H a n) : ∃ c, spec_l hE F c a n := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  obtain ⟨c, hc⟩ := SecondOrderSequenceCode.history_l hℳ hE F H a n hH
  have h₀ : 0 < succ_l n := (SecondOrderNaturalGraph.lt_succ_l hℳ 0 n).mpr (zero_le_l hℳ n)
  refine ⟨c, ?_, (hc _ a).mpr ⟨h₀, hH.2.1⟩, ?_⟩
  · intro i hi
    obtain ⟨b, hb, h⟩ := hH.1 i hi
    exact ⟨b, (hc i b).mpr ⟨hi, hb⟩, fun d hd => h d ((hc i d).mp hd).2⟩
  · intro i b d hi hb hd
    exact hH.2.2 i b d hi ((hc i b).mp hb).2 ((hc (succ_l i) d).mp hd).2

/-- 任意全域数值转移关系在每个模型长度上都有单数历史码。 -/
theorem exists_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
    (hE : SecondOrderBinaryPowers.spec_l E) (F : set_l ℳ) (a : num_l ℳ)
    (hF : ∀ b, ∃ d, relation_l F b d) (n : num_l ℳ) : ∃ c, spec_l hE F c a n := by
  obtain ⟨H, hH⟩ := SecondOrderHistory.exists_l hℳ F a hF n
  exact encode_l hℳ hE F H a n hH

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderNumberHistory
