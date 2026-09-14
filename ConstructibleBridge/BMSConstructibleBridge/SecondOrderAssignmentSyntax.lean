import BMSConstructibleBridge.SecondOrderAssignment

/-!
# 有限赋值与量词扩张的实际公式

数码、长度和新值均为数量词参数；唯一实数参数是已证存在的二进制幂图。
有效性同时检查界内输出存在唯一与界外无边。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAssignmentSyntax

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderNumberHistory

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private def zero {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .zero .nil

private def succ {Γ Δ : SortContext signature_m} (s : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num := Term.app (σ := signature_m) .succ (.cons s .nil)

private def read {Γ : SortContext signature_m} (i b : Term signature_m Γ [.set, .num, .num] .num) :
    Formula signature_m Γ [.set, .num, .num] :=
  SecondOrderSequenceSyntax.formula_m (.fvar .here) (.fvar (.there .here)) i b

def template_m : Formula signature_m [] [.set, .num, .num] :=
  .conj
    (.forallE .num (.imp (PrimitiveFormulas.lt_m (.bvar .here) (.fvar (.there (.there .here))))
      (.existsE .num (.conj (read (.bvar (.there .here)) (.bvar .here))
        (.forallE .num (.imp (read (.bvar (.there (.there .here))) (.bvar .here))
          (.equal (.bvar .here) (.bvar (.there .here)))))))))
    (.forallE .num (.forallE .num (.imp (read (.bvar (.there .here)) (.bvar .here))
      (PrimitiveFormulas.lt_m (.bvar (.there .here)) (.fvar (.there (.there .here)))))))

private def bind {Γ Δ : SortContext signature_m} (E : Term signature_m Γ Δ .set)
    (c n : Term signature_m Γ Δ .num) : Substitution signature_m [] [.set, .num, .num] Γ Δ :=
  .map (fun v => nomatch v) (fun v => match v with
    | .here => E
    | .there .here => c
    | .there (.there .here) => n)

def formula_m {Γ Δ : SortContext signature_m} (E : Term signature_m Γ Δ .set)
    (c n : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ := template_m.substitute (bind E c n)

theorem pure_m {Γ Δ : SortContext signature_m} (E : Term signature_m Γ Δ .set)
    (c n : Term signature_m Γ Δ .num) (hE : pure_term_m E = true) (hc : pure_term_m c = true)
    (hn : pure_term_m n = true) : language_m (formula_m E c n) = true := by
  refine (SecondOrderSubstitution.form_subst_m template_m _ _ ?_ ?_).trans (pure_language_m _ rfl)
  · intro s v
    nomatch v
  · intro s v
    match v with
    | .here => exact hE
    | .there .here => exact hc
    | .there (.there .here) => exact hn

def valid_l (E : set_l ℳ) (c n : num_l ℳ) : Prop :=
  (∀ i, SecondOrderOrder.lt_l i n → ∃! b, SecondOrderSequenceSyntax.read_l E c i b) ∧
    ∀ i b, SecondOrderSequenceSyntax.read_l E c i b → SecondOrderOrder.lt_l i n

theorem raw_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (E : Term signature_m Γ Δ .set) (c n : Term signature_m Γ Δ .num) :
    Formula.satisfies η (formula_m E c n) ↔ valid_l (E.eval η) (c.eval η) (n.eval η) := by
  simp only [formula_m, Formula.satisfies_substitute, template_m, Formula.satisfies,
    read, SecondOrderSequenceSyntax.raw_l, SecondOrderOrder.formula_l]
  rfl

theorem template_l (η : Env ℳ [] [.set, .num, .num])
    (hE : SecondOrderBinaryPowers.spec_l (η.freeVal .here)) :
    Formula.satisfies η template_m ↔
      SecondOrderAssignment.spec_l hE (η.freeVal (.there .here)) (η.freeVal (.there (.there .here))) := by
  simp only [template_m, Formula.satisfies, read, SecondOrderSequenceSyntax.raw_l, SecondOrderOrder.formula_l]
  let E := η.freeVal .here
  let c := η.freeVal (.there .here)
  let n := η.freeVal (.there (.there .here))
  change ((∀ i, SecondOrderOrder.lt_l i n → ∃ b, SecondOrderSequenceSyntax.read_l E c i b ∧
    ∀ d, SecondOrderSequenceSyntax.read_l E c i d → d = b) ∧
      ∀ i b, SecondOrderSequenceSyntax.read_l E c i b → SecondOrderOrder.lt_l i n) ↔ _
  have h (i b : num_l ℳ) : SecondOrderSequenceSyntax.read_l E c i b ↔ entry_l hE c i b :=
    SecondOrderSequenceSyntax.read_eq_l hE c i b
  simp only [h]
  rfl

theorem formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (E : Term signature_m Γ Δ .set) (c n : Term signature_m Γ Δ .num)
    (hE : SecondOrderBinaryPowers.spec_l (E.eval η)) :
    Formula.satisfies η (formula_m E c n) ↔ SecondOrderAssignment.spec_l hE (c.eval η) (n.eval η) := by
  rw [formula_m, Formula.satisfies_substitute, template_l _ hE]
  rfl

/-- 参数为幂图、旧码、旧长度、新码、前插值。 -/
def prepend_m : Formula signature_m [] [.set, .num, .num, .num, .num] :=
  .conj (formula_m (.fvar .here) (.fvar (.there (.there (.there .here))))
    (succ (.fvar (.there (.there .here)))))
    (.conj
      (.forallE .num (.iff
        (SecondOrderSequenceSyntax.formula_m (.fvar .here) (.fvar (.there (.there (.there .here)))) zero (.bvar .here))
        (.equal (.bvar .here) (.fvar (.there (.there (.there (.there .here))))))))
      (.forallE .num (.forallE .num (.iff
        (SecondOrderSequenceSyntax.formula_m (.fvar .here) (.fvar (.there (.there (.there .here))))
          (succ (.bvar (.there .here))) (.bvar .here))
        (SecondOrderSequenceSyntax.formula_m (.fvar .here) (.fvar (.there .here)) (.bvar (.there .here)) (.bvar .here))))))

theorem prepend_pure_m : language_m prepend_m = true := pure_language_m _ rfl

def extension_l (E : set_l ℳ) (c n d x : num_l ℳ) : Prop :=
  valid_l E d (succ_l n) ∧
    (∀ b, SecondOrderSequenceSyntax.read_l E d (zero_l ℳ) b ↔ b = x) ∧
    ∀ i b, SecondOrderSequenceSyntax.read_l E d (succ_l i) b ↔ SecondOrderSequenceSyntax.read_l E c i b

private def extension_bind {Γ Δ : SortContext signature_m} (E : Term signature_m Γ Δ .set)
    (c n d x : Term signature_m Γ Δ .num) :
    Substitution signature_m [] [.set, .num, .num, .num, .num] Γ Δ :=
  .map (fun v => nomatch v) (fun v => match v with
    | .here => E
    | .there .here => c
    | .there (.there .here) => n
    | .there (.there (.there .here)) => d
    | .there (.there (.there (.there .here))) => x)

def extension_m {Γ Δ : SortContext signature_m} (E : Term signature_m Γ Δ .set)
    (c n d x : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  prepend_m.substitute (extension_bind E c n d x)

theorem extension_pure_m {Γ Δ : SortContext signature_m} (E : Term signature_m Γ Δ .set)
    (c n d x : Term signature_m Γ Δ .num) (hE : pure_term_m E = true)
    (hc : pure_term_m c = true) (hn : pure_term_m n = true)
    (hd : pure_term_m d = true) (hx : pure_term_m x = true) : language_m (extension_m E c n d x) = true := by
  refine (SecondOrderSubstitution.form_subst_m prepend_m _ _ ?_ ?_).trans prepend_pure_m
  · intro s v
    nomatch v
  · intro s v
    match v with
    | .here => exact hE
    | .there .here => exact hc
    | .there (.there .here) => exact hn
    | .there (.there (.there .here)) => exact hd
    | .there (.there (.there (.there .here))) => exact hx

theorem extension_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (E : Term signature_m Γ Δ .set) (c n d x : Term signature_m Γ Δ .num) :
    Formula.satisfies η (extension_m E c n d x) ↔
      extension_l (E.eval η) (c.eval η) (n.eval η) (d.eval η) (x.eval η) := by
  simp only [extension_m, Formula.satisfies_substitute, prepend_m, Formula.satisfies,
    raw_l, SecondOrderSequenceSyntax.raw_l]
  rfl

theorem prepend_l (η : Env ℳ [] [.set, .num, .num, .num, .num])
    (hE : SecondOrderBinaryPowers.spec_l (η.freeVal .here)) :
    Formula.satisfies η prepend_m ↔
      SecondOrderAssignment.spec_l hE (η.freeVal (.there (.there (.there .here))))
        (succ_l (η.freeVal (.there (.there .here)))) ∧
      (∀ b, entry_l hE (η.freeVal (.there (.there (.there .here)))) (zero_l ℳ) b ↔
        b = η.freeVal (.there (.there (.there (.there .here))))) ∧
      ∀ i b, entry_l hE (η.freeVal (.there (.there (.there .here)))) (succ_l i) b ↔
        entry_l hE (η.freeVal (.there .here)) i b := by
  simp only [prepend_m, Formula.satisfies]
  apply and_congr (formula_l η (.fvar .here) _ _ hE)
  apply and_congr
  · apply forall_congr'
    intro b
    exact iff_congr (SecondOrderSequenceSyntax.formula_l (η.pushBound b) (.fvar .here) _ _ _ hE) Iff.rfl
  · apply forall_congr'
    intro i
    apply forall_congr'
    intro b
    exact iff_congr (SecondOrderSequenceSyntax.formula_l ((η.pushBound i).pushBound b) (.fvar .here) _ _ _ hE)
      (SecondOrderSequenceSyntax.formula_l ((η.pushBound i).pushBound b) (.fvar .here) _ _ _ hE)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAssignmentSyntax
