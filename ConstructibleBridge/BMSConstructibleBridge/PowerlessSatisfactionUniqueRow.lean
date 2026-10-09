import BMSConstructibleBridge.PowerlessBMSQuotientStrongInduction
import BMSConstructibleBridge.PowerlessSatisfactionSpecification

/-! # 同一内部合法性图的 Sat 一致性归纳行

归纳行量化全环境的内部长度及实际有限赋值图，比较两张 Sat 图的读值。
只有这条明确纯公式的实例可用原 Z₂ 强归纳；构造子步仍须实际证明，
不能把此工具或宿主 Prop 本身当成 Sat 唯一性已完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSatisfactionUniqueRow

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax
open PowerlessBMSQuotientCoding

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def row_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω A F R S c : carrier_l ℳ₀) : Prop :=
  ∀ L, member_l ℳ₀ L ω → ∀ f, value_l F c L → map_l f L A → (value_l R c f ↔ value_l S c f)

def row_m {Γ Δ : SortContext ℒ} (ω A F R S c : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (member_m (.bvar .here) (up ω)) <| .forallE .set <|
      .imp (value_m (up (up F)) (up (up c)) (.bvar (.there .here))) <|
        .imp (map_m (.bvar .here) (.bvar (.there .here)) (up (up A))) <|
          .iff (value_m (up (up R)) (up (up c)) (.bvar .here))
            (value_m (up (up S)) (up (up c)) (.bvar .here))

theorem row_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (ω A F R S c : Term ℒ Γ Δ .set) :
    (row_m ω A F R S c).satisfies η ↔
      row_l (ω.eval η) (A.eval η) (F.eval η) (R.eval η) (S.eval η) (c.eval η) := by
  simp only [row_m, Formula.satisfies, value_formula_l, map_formula_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def template_m : Formula ℒ [] [.set, .set, .set, .set, .set, .set] :=
  row_m (.fvar (.there .here)) (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here)))))) (.fvar .here)

theorem induct_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
    (K : source_coding_l hℳ) (A F R S : SecondOrderQuotient.type_l hℳ)
    (hStep : ∀ n, (∀ k, SecondOrderOrder.lt_l k n →
      row_l (ℳ₀ := SecondOrderQuotient.structure_l hℳ) K.omega A F R S (numberCode_l K k).val) →
      row_l (ℳ₀ := SecondOrderQuotient.structure_l hℳ) K.omega A F R S (numberCode_l K n).val) :
    ∀ n, row_l (ℳ₀ := SecondOrderQuotient.structure_l hℳ) K.omega A F R S (numberCode_l K n).val := by
  let η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set, .set, .set, .set, .set] :=
    ((((Env.empty.pushFree S).pushFree R).pushFree F).pushFree A).pushFree K.omega
  apply PowerlessBMSQuotientStrongInduction.strong_induct_l K template_m η _ _ hStep
  intro n
  exact row_formula_l (η.pushFree (numberCode_l K n).val) _ _ _ _ _ _

#print axioms induct_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSatisfactionUniqueRow
