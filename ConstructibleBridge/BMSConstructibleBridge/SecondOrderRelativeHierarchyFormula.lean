import BMSConstructibleBridge.SecondOrderRelativeHierarchyStep
import BMSConstructibleBridge.SecondOrderCanonicalMemberDefFormulaSemantics
import BMSConstructibleBridge.SecondOrderPredecessorUnionFormula
import BMSConstructibleBridge.SecondOrderPointwiseOperator

/-! # 相对层次三类阶段的实际正文

公开自由槽依次为输出图、阶段数、历史、前驱关系、基图。后继阶段绑定
最大前驱和它的实际历史行，极限阶段调用已验证的完整并集公式。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeHierarchyFormula

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def minimal_m {Γ Δ : SortContext signature_m} (R : Term signature_m Γ Δ .set)
    (n : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .forallE .num <| .neg (GraphSyntax.edge_m (R.weakenBound sort_m.num)
    (.bvar .here) (n.weakenBound sort_m.num))

def immediate_m {Γ Δ : SortContext signature_m} (R : Term signature_m Γ Δ .set)
    (m n : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .conj (GraphSyntax.edge_m R m n) <| .forallE .num <| .imp
    (GraphSyntax.edge_m (R.weakenBound sort_m.num) (.bvar .here) (n.weakenBound sort_m.num))
    (.disj (.equal (.bvar .here) (m.weakenBound sort_m.num))
      (GraphSyntax.edge_m (R.weakenBound sort_m.num) (.bvar .here) (m.weakenBound sort_m.num)))

theorem minimal_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (R : Term signature_m Γ Δ .set) (n : Term signature_m Γ Δ .num) :
    (minimal_m R n).satisfies η ↔ SecondOrderRelativeHierarchyStep.minimal_l (R.eval η) (n.eval η) := by
  simp only [minimal_m, Formula.satisfies, SecondOrderPairing.edge_l, Term.eval_weakenBound, Term.eval]
  rfl

theorem immediate_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (R : Term signature_m Γ Δ .set) (m n : Term signature_m Γ Δ .num) :
    (immediate_m R m n).satisfies η ↔
      SecondOrderRelativeHierarchyStep.immediate_l (R.eval η) (m.eval η) (n.eval η) := by
  simp only [immediate_m, Formula.satisfies, SecondOrderPairing.edge_l, Term.eval_weakenBound, Term.eval]
  rfl

abbrev context_m : SortContext signature_m := [.set, .num, .set, .set, .set]

private def base_m : Formula signature_m [] context_m :=
  .conj (minimal_m (.fvar (.there (.there (.there .here)))) (.fvar (.there .here)))
    (.equal (.fvar .here) (.fvar (.there (.there (.there (.there .here))))))

private def successor_m : Formula signature_m [] context_m :=
  .existsE .num <| .existsE .set <| .conj
    (immediate_m (.fvar (.there (.there (.there .here)))) (.bvar (.there .here)) (.fvar (.there .here))) <|
    .conj (SecondOrderSections.formula_m (.fvar (.there (.there .here))) (.bvar .here) (.bvar (.there .here)))
      (SecondOrderCanonicalMemberDefFormula.formula_m (.bvar .here)
        (Term.app (σ := signature_m) .zero .nil) (.fvar .here))

private def limit_m : Formula signature_m [] context_m :=
  .conj (.conj (.neg (minimal_m (.fvar (.there (.there (.there .here)))) (.fvar (.there .here))))
    (.neg (.existsE .num (immediate_m (.fvar (.there (.there (.there .here))))
      (.bvar .here) (.fvar (.there .here))))))
    (SecondOrderPredecessorUnionFormula.formula_m (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here))

def formula_m : Formula signature_m [] context_m := .disj base_m (.disj successor_m limit_m)

private theorem disj_pure_m {Γ Δ : SortContext signature_m} (φ ψ : Formula signature_m Γ Δ)
    (hφ : language_m φ = true) (hψ : language_m ψ = true) : language_m (.disj φ ψ) = true := by
  change (language_m φ && language_m ψ) = true
  rw [hφ, hψ]
  rfl

private theorem base_pure_m : language_m base_m = true := rfl

private theorem successor_pure_m : language_m successor_m = true := by
  have hDef := SecondOrderCanonicalMemberDefFormula.pure_m
    (Γ := [.set, .num]) (Δ := context_m) (.bvar .here)
    (Term.app (σ := signature_m) .zero .nil) (.fvar .here) rfl rfl rfl
  have hSection := SecondOrderSections.pure_m
    (Γ := [.set, .num]) (Δ := context_m) (.fvar (.there (.there .here)))
    (.bvar .here) (.bvar (.there .here)) rfl rfl rfl
  have hImmediate : language_m (immediate_m
      (Γ := [.set, .num]) (Δ := context_m) (.fvar (.there (.there (.there .here))))
      (.bvar (.there .here)) (.fvar (.there .here))) = true := pure_language_m _ rfl
  exact SecondOrderFormulaArguments.exists_pure_m .num _
    (SecondOrderFormulaArguments.exists_pure_m .set _
      (SecondOrderFormulaArguments.conj_pure_m _ _ hImmediate
        (SecondOrderFormulaArguments.conj_pure_m _ _ hSection hDef)))

private theorem limit_pure_m : language_m limit_m = true := by
  have hUnion := SecondOrderPredecessorUnionFormula.pure_m
    (Γ := []) (Δ := context_m) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here) rfl rfl rfl rfl
  have hGuard : language_m (.conj
      (.neg (minimal_m (Γ := []) (Δ := context_m) (.fvar (.there (.there (.there .here)))) (.fvar (.there .here))))
      (.neg (.existsE .num (immediate_m (.fvar (.there (.there (.there .here))))
        (.bvar .here) (.fvar (.there .here)))))) = true := pure_language_m _ rfl
  exact SecondOrderFormulaArguments.conj_pure_m _ _ hGuard hUnion

theorem pure_m : language_m formula_m = true :=
  disj_pure_m _ _ base_pure_m (disj_pure_m _ _ successor_pure_m limit_pure_m)

theorem formula_l (hℳ : Theory.Models ℳ theory_m) (η : Env ℳ [] context_m) :
    formula_m.satisfies η ↔ SecondOrderRelativeHierarchyStep.spec_l
      (η.freeVal (.there (.there (.there (.there .here)))))
      (η.freeVal (.there (.there (.there .here)))) (η.freeVal (.there (.there .here)))
      (η.freeVal (.there .here)) (η.freeVal .here) := by
  simp only [formula_m, base_m, successor_m, limit_m, Formula.satisfies,
    minimal_formula_l, immediate_formula_l, SecondOrderSections.formula_l,
    SecondOrderCanonicalMemberDefFormulaSemantics.formula_l hℳ,
    SecondOrderPredecessorUnionFormula.formula_l hℳ, Term.eval]
  rfl

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeHierarchyFormula
