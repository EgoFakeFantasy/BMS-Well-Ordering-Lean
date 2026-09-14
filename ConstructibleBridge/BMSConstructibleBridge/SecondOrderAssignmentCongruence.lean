import BMSConstructibleBridge.SecondOrderAssignmentSyntax

/-! # 赋值读取相同与前插关系的换码不变性 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAssignmentCongruence

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderSequenceSyntax (read_l)
open SecondOrderAssignmentSyntax (valid_l extension_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def same_l (E : set_l ℳ) (c d : num_l ℳ) : Prop := ∀ i b, read_l E c i b ↔ read_l E d i b

def template_m : Formula signature_m [] [.set, .num, .num] :=
  .forallE .num (.forallE .num (.iff
    (SecondOrderSequenceSyntax.formula_m (.fvar .here) (.fvar (.there .here)) (.bvar (.there .here)) (.bvar .here))
    (SecondOrderSequenceSyntax.formula_m (.fvar .here) (.fvar (.there (.there .here)))
      (.bvar (.there .here)) (.bvar .here))))

private def bind {Γ Δ : SortContext signature_m} (E : Term signature_m Γ Δ .set)
    (c d : Term signature_m Γ Δ .num) : Substitution signature_m [] [.set, .num, .num] Γ Δ :=
  .map (fun v => nomatch v) (fun v => match v with
    | .here => E
    | .there .here => c
    | .there (.there .here) => d)

def formula_m {Γ Δ : SortContext signature_m} (E : Term signature_m Γ Δ .set)
    (c d : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ := template_m.substitute (bind E c d)

theorem pure_m {Γ Δ : SortContext signature_m} (E : Term signature_m Γ Δ .set)
    (c d : Term signature_m Γ Δ .num) (hE : pure_term_m E = true)
    (hc : pure_term_m c = true) (hd : pure_term_m d = true) : language_m (formula_m E c d) = true := by
  refine (SecondOrderSubstitution.form_subst_m template_m _ _ ?_ ?_).trans (pure_language_m _ rfl)
  · intro s v
    nomatch v
  · intro s v
    match v with
    | .here => exact hE
    | .there .here => exact hc
    | .there (.there .here) => exact hd

theorem formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (E : Term signature_m Γ Δ .set) (c d : Term signature_m Γ Δ .num) :
    Formula.satisfies η (formula_m E c d) ↔ same_l (E.eval η) (c.eval η) (d.eval η) := by
  simp only [formula_m, Formula.satisfies_substitute, template_m, Formula.satisfies,
    SecondOrderSequenceSyntax.raw_l]
  rfl

theorem valid_congr_l (E : set_l ℳ) (c d n : num_l ℳ) (h : same_l E c d) :
    valid_l E c n ↔ valid_l E d n := by
  unfold same_l at h
  unfold valid_l
  simp only [h]

theorem extension_congr_l (E : set_l ℳ) (c c' n d x : num_l ℳ) (h : same_l E c c') :
    extension_l E c n d x ↔ extension_l E c' n d x := by
  unfold same_l at h
  unfold extension_l
  simp only [h]

theorem valid_iff_l {E : set_l ℳ} (hE : SecondOrderBinaryPowers.spec_l E) (c n : num_l ℳ) :
    valid_l E c n ↔ SecondOrderAssignment.spec_l hE c n := by
  unfold valid_l SecondOrderAssignment.spec_l
  simp only [SecondOrderSequenceSyntax.read_eq_l hE]
  rfl

theorem extension_exists_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
    (hE : SecondOrderBinaryPowers.spec_l E) (c n x : num_l ℳ) (hc : valid_l E c n) :
    ∃ d, extension_l E c n d x := by
  obtain ⟨d, hd, h₀, h₁⟩ := SecondOrderAssignment.prepend_l hℳ hE c n x ((valid_iff_l hE c n).mp hc)
  refine ⟨d, (valid_iff_l hE d (succ_l n)).mpr hd, ?_, ?_⟩
  · intro b
    exact (SecondOrderSequenceSyntax.read_eq_l hE d (zero_l ℳ) b).trans (h₀ b)
  · intro i b
    exact (SecondOrderSequenceSyntax.read_eq_l hE d (succ_l i) b).trans
      ((h₁ i b).trans (SecondOrderSequenceSyntax.read_eq_l hE c i b).symm)

theorem extension_same_l (hℳ : Theory.Models ℳ theory_m) (E : set_l ℳ)
    (c n d e x : num_l ℳ) (hd : extension_l E c n d x) (he : extension_l E c n e x) : same_l E d e := by
  intro i b
  rcases predecessor_l hℳ i with rfl | ⟨j, rfl⟩
  · exact (hd.2.1 b).trans (he.2.1 b).symm
  · exact (hd.2.2 j b).trans (he.2.2 j b).symm

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAssignmentCongruence
