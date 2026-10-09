import BMSConstructibleBridge.PowerlessBMSClassRelationDomain
import BMSConstructibleBridge.SecondOrderGraphFormulaGuard

/-!
# 实际可定义集合值类映射的内部成员图

通过一次原 Z₂ 理解构造成员边实数，再核验全部内部根无下降链。
定义域为模型的全部内部自然数；输出总性与单值性必须由实际源公式满足。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSClassRelation

open Logic FirstOrder PowerlessBMSQuotientCoding

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private def insert_m {Γ Δ : SortContext ℒ}
    (x y : Term ℒ Γ (.set :: .set :: Δ) .set) :
    VariableSubstitution ℒ (.set :: .set :: Δ) Γ (.set :: .set :: Δ)
  | _, .here => y
  | _, .there .here => x
  | _, .there (.there v) => .fvar (.there (.there v))

private def at_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (x y : Term ℒ Γ (.set :: .set :: Δ) .set) : Formula ℒ Γ (.set :: .set :: Δ) :=
  φ.substitute (show Substitution ℒ [] (.set :: .set :: Δ) Γ (.set :: .set :: Δ) from
    .map (fun v => nomatch v) (insert_m x y))

/-- 两个首自由槽是输入编号对应的集合自然数，其后为原参数。 -/
def edge_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [] (.set :: .set :: Δ) :=
  .existsE .set (.existsE .set (.conj
    (at_m φ (.fvar .here) (.bvar (.there .here)))
    (.conj (at_m φ (.fvar (.there .here)) (.bvar .here))
      (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (.bvar .here)))))

theorem edge_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒩 [] Δ) (n m : 𝒩.Carrier .set) :
    (edge_m φ).satisfies ((η.pushFree m).pushFree n) ↔ ∃ y z,
      φ.satisfies ((η.pushFree n).pushFree y) ∧
      φ.satisfies ((η.pushFree m).pushFree z) ∧
      𝒩.relInterp .membership (.cons y (.cons z .nil)) := by
  simp only [edge_m, Formula.satisfies, SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval]
  apply exists_congr
  intro y
  apply exists_congr
  intro z
  refine and_congr ?_ (and_congr ?_ Iff.rfl)
  all_goals
    refine (Formula.satisfies_substitute _ _ φ).trans ?_
    apply Iff.of_eq
    apply congrArg (fun η => φ.satisfies η)
    apply Env.ext
    · intro s v
      nomatch v
    · intro s v
      cases v with
      | here => rfl
      | there v => cases v <;> rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

private abbrev quotient_l := SecondOrderQuotient.structure_l hℳ

/-- 完整内部成员图的实际实数表示，并非额外假定可定义类的图已经是集合。 -/
theorem exists_l (C : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env quotient_l [] Δ)
    (hTotal : ∀ n, ∃ y, φ.satisfies ((η.pushFree (numberCode_l C n).val).pushFree y))
    (hUnique : ∀ n y z,
      φ.satisfies ((η.pushFree (numberCode_l C n).val).pushFree y) →
      φ.satisfies ((η.pushFree (numberCode_l C n).val).pushFree z) → y = z) :
    ∃ R : SecondOrderModel.set_l ℳ,
      (∀ n m, SecondOrderPairing.relation_l R n m ↔ ∃ y z,
        φ.satisfies ((η.pushFree (numberCode_l C n).val).pushFree y) ∧
        φ.satisfies ((η.pushFree (numberCode_l C m).val).pushFree z) ∧
        SecondOrderQuotient.mem_l hℳ y z) ∧
      ∀ n, SecondOrderDomain.wf_l R n := by
  obtain ⟨R, hR⟩ := SecondOrderGraphFormulaRelation.exists_l hℳ (edge_m φ) η C.less C.less
  have hEdge n m : SecondOrderPairing.relation_l R n m ↔ ∃ y z,
      φ.satisfies ((η.pushFree (numberCode_l C n).val).pushFree y) ∧
      φ.satisfies ((η.pushFree (numberCode_l C m).val).pushFree z) ∧
      SecondOrderQuotient.mem_l hℳ y z :=
    (hR n m (SecondOrderNaturalGraph.wf_l hℳ C.less C.less_spec n)
      (SecondOrderNaturalGraph.wf_l hℳ C.less C.less_spec m)).trans (edge_formula_l φ η _ _)
  exact ⟨R, hEdge, PowerlessBMSClassRelationDomain.wf_l C φ η R hTotal hUnique
    (fun n m h => (hEdge n m).mp h)⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSClassRelation
