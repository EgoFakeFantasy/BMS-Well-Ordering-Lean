import BMSConstructibleBridge.SecondOrderDefinableFamilyTheorem

/-!
# 相对于内部代表关系的赋值对应

数码读取的值可不同，但同一位置的两个值须满足给定内部关系 Q。
关系的自反性和原子相容性留作后续定理的明确前提，不在此默认为逻辑相等。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelatedAssignments

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)
open SecondOrderSequenceSyntax (read_l)
open SecondOrderAssignmentSyntax (valid_l extension_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def related_l (E Q : set_l ℳ) (c d : num_l ℳ) : Prop :=
  ∀ i x y, read_l E c i x → read_l E d i y → relation_l Q x y

def template_m : Formula signature_m [] [.set, .set, .num, .num] :=
  .forallE .num <| .forallE .num <| .forallE .num <|
    .imp (SecondOrderSequenceSyntax.formula_m (.fvar .here) (.fvar (.there (.there .here)))
      (.bvar (.there (.there .here))) (.bvar (.there .here))) <|
      .imp (SecondOrderSequenceSyntax.formula_m (.fvar .here) (.fvar (.there (.there (.there .here))))
        (.bvar (.there (.there .here))) (.bvar .here)) <|
        GraphSyntax.edge_m (.fvar (.there .here)) (.bvar (.there .here)) (.bvar .here)

private def bind {Γ Δ : SortContext signature_m} (E Q : Term signature_m Γ Δ .set)
    (c d : Term signature_m Γ Δ .num) : Substitution signature_m [] [.set, .set, .num, .num] Γ Δ :=
  .map (fun w => nomatch w) (fun w => match w with
    | .here => E
    | .there .here => Q
    | .there (.there .here) => c
    | .there (.there (.there .here)) => d)

def formula_m {Γ Δ : SortContext signature_m} (E Q : Term signature_m Γ Δ .set)
    (c d : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ := template_m.substitute (bind E Q c d)

theorem pure_m {Γ Δ : SortContext signature_m} (E Q : Term signature_m Γ Δ .set)
    (c d : Term signature_m Γ Δ .num) (hE : pure_term_m E = true) (hQ : pure_term_m Q = true)
    (hc : pure_term_m c = true) (hd : pure_term_m d = true) : language_m (formula_m E Q c d) = true := by
  refine (SecondOrderSubstitution.form_subst_m template_m _ _ ?_ ?_).trans (pure_language_m _ rfl)
  · intro s w
    nomatch w
  · intro s w
    match w with
    | .here => exact hE
    | .there .here => exact hQ
    | .there (.there .here) => exact hc
    | .there (.there (.there .here)) => exact hd

theorem formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ) (E Q : Term signature_m Γ Δ .set)
    (c d : Term signature_m Γ Δ .num) : Formula.satisfies η (formula_m E Q c d) ↔
      related_l (E.eval η) (Q.eval η) (c.eval η) (d.eval η) := by
  simp only [formula_m, Formula.satisfies_substitute, template_m, Formula.satisfies,
    SecondOrderSequenceSyntax.raw_l, SecondOrderPairing.edge_l]
  rfl

theorem reflexive_l (E Q : set_l ℳ) (hQ : ∀ x, relation_l Q x x) (c l : num_l ℳ)
    (hc : valid_l E c l) : related_l E Q c c := by
  intro i x y hx hy
  obtain ⟨z, _, hU⟩ := hc.1 i (hc.2 i x hx)
  have h : x = y := (hU x hx).trans (hU y hy).symm
  exact h ▸ hQ x

theorem extension_l (hℳ : Theory.Models ℳ theory_m) (E Q : set_l ℳ) (l c d a b x y : num_l ℳ)
    (h : related_l E Q c d) (ha : SecondOrderAssignmentSyntax.extension_l E c l a x)
    (hb : SecondOrderAssignmentSyntax.extension_l E d l b y) (hxy : relation_l Q x y) : related_l E Q a b := by
  intro i u v hu hv
  rcases predecessor_l hℳ i with rfl | ⟨j, rfl⟩
  · have hu₀ := (ha.2.1 u).mp hu
    have hv₀ := (hb.2.1 v).mp hv
    subst u v
    exact hxy
  · exact h j u v ((ha.2.2 j u).mp hu) ((hb.2.2 j v).mp hv)

/-- 两个原子关系在 Q 对应的两对参数上保持真值。 -/
def respects_l (Q G : set_l ℳ) : Prop := ∀ a b a' b', relation_l Q a a' → relation_l Q b b' →
  (relation_l G a b ↔ relation_l G a' b')

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelatedAssignments
