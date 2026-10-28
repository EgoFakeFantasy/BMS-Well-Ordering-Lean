import BMSConstructibleBridge.SecondOrderParity
import BMSConstructibleBridge.SecondOrderMultiplication

/-! # 原内部自然数上的三角数关系

以 2t=n(n+1) 表示三角数，不从存在唯一性抽取 Type 层函数。
存在性沿实际算术公式归纳，后继见证显式为 t+(n+1)；倍增单射给唯一性。
覆盖全部内部自然数，并将存在唯一闭句回传原 Z₂ 推导核。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderTriangularArithmetic

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel SecondOrderNumbers

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def relation_l (n t : num_l ℳ) : Prop := add_l t t = mul_l n (succ_l n)

def relation_m {Γ Δ : SortContext signature_m} (n t : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .equal (Term.app (σ := signature_m) .add (.cons t (.cons t .nil)))
    (Term.app (σ := signature_m) .mul (.cons n (.cons (Term.app (σ := signature_m) .succ (.cons n .nil)) .nil)))

theorem relation_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (n t : Term signature_m Γ Δ .num) :
    (relation_m n t).satisfies η ↔ relation_l (ℳ := ℳ) (n.eval η) (t.eval η) := Iff.rfl

private theorem double_add_l (hℳ : Theory.Models ℳ theory_m) (a b : num_l ℳ) :
    add_l (add_l a b) (add_l a b) = add_l (add_l a a) (add_l b b) := by
  rw [add_assoc_l hℳ a b (add_l a b), ← add_assoc_l hℳ b a b, add_comm_l hℳ b a,
    add_assoc_l hℳ a b b, ← add_assoc_l hℳ a a (add_l b b)]

theorem step_l (hℳ : Theory.Models ℳ theory_m) {n t : num_l ℳ} (ht : relation_l n t) :
    relation_l (succ_l n) (add_l t (succ_l n)) := by
  change add_l (add_l t (succ_l n)) (add_l t (succ_l n)) = mul_l (succ_l n) (succ_l (succ_l n))
  calc
    _ = add_l (add_l t t) (add_l (succ_l n) (succ_l n)) := double_add_l hℳ t (succ_l n)
    _ = add_l (mul_l n (succ_l n)) (add_l (succ_l n) (succ_l n)) := by rw [ht]
    _ = add_l (mul_l (succ_l n) (succ_l n)) (succ_l n) := by
      rw [SecondOrderMultiplication.succ_mul_l hℳ, add_assoc_l hℳ]
    _ = mul_l (succ_l n) (succ_l (succ_l n)) := (mul_succ_l hℳ _ _).symm

def existence_m : Formula signature_m [] [.num] :=
  .existsE .num (relation_m (.fvar .here) (.bvar .here))

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (n : num_l ℳ) : ∃ t, relation_l n t := by
  apply induct_l hℳ existence_m (pure_language_m _ rfl) (Env.empty (M := ℳ))
    (fun n => ∃ t, relation_l n t) ?_ ?_ ?_ n
  · intro k
    simp only [existence_m, Formula.satisfies, relation_formula_l, Term.eval]
    rfl
  · refine ⟨zero_l ℳ, ?_⟩
    change add_l (zero_l ℳ) (zero_l ℳ) = mul_l (zero_l ℳ) (succ_l (zero_l ℳ))
    rw [add_zero_l hℳ, SecondOrderMultiplication.zero_mul_l hℳ]
  · rintro k ⟨t, ht⟩
    exact ⟨add_l t (succ_l k), step_l hℳ ht⟩

theorem unique_l (hℳ : Theory.Models ℳ theory_m) {n t v : num_l ℳ}
    (ht : relation_l n t) (hv : relation_l n v) : t = v :=
  SecondOrderParity.even_injective_l hℳ (ht.trans hv.symm)

theorem successor_l (hℳ : Theory.Models ℳ theory_m) {n t v : num_l ℳ}
    (ht : relation_l n t) (hv : relation_l (succ_l n) v) : v = add_l t (succ_l n) :=
  unique_l hℳ hv (step_l hℳ ht)

def sentence_m : Sentence signature_m := .forallE .num <| .existsE .num <| .conj
  (relation_m (.bvar (.there .here)) (.bvar .here)) <|
  .forallE .num <| .imp (relation_m (.bvar (.there (.there .here))) (.bvar .here))
    (.equal (.bvar .here) (.bvar (.there .here)))

theorem derives_m : Derives theory_m [] sentence_m := by
  apply SecondOrderCompleteness.derives_m
  intro ℳ hℳ
  change ∀ n : num_l ℳ, ∃ t, relation_l n t ∧ ∀ v, relation_l n v → v = t
  intro n
  obtain ⟨t, ht⟩ := exists_l hℳ n
  exact ⟨t, ht, fun v hv => unique_l hℳ hv ht⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderTriangularArithmetic
