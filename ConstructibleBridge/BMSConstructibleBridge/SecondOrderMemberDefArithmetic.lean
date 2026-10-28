import BMSConstructibleBridge.SecondOrderRelationSpecification
import BMSConstructibleBridge.SecondOrderInternalFormulaSyntax
import BMSConstructibleBridge.SecondOrderDefinableFamily

/-!
# Def 枚举证书中的算术部分

合法公式、二进制幂、全数域、内部求值和切片关系分别由实际 AST 表达。
这些公式只约束原模型的数和实数；母集、枚举和精确子集族在纯集合层连接。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberDefArithmetic

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private abbrev up {Γ Δ : SortContext signature_m} {s : sort_m}
    (t : Term signature_m Γ Δ s) := t.weakenBound sort_m.num

private def succ_m {Γ Δ : SortContext signature_m} (t : Term signature_m Γ Δ .num) :=
  Term.app (σ := signature_m) .succ (.cons t .nil)

def powers_m {Γ Δ : SortContext signature_m} (E : Term signature_m Γ Δ .set) :
    Formula signature_m Γ Δ :=
  .conj
    (.forallE .num <| .existsE .num <| .conj
      (GraphSyntax.edge_m (up (up E)) (.bvar (.there .here)) (.bvar .here))
      (.forallE .num <| .imp
        (GraphSyntax.edge_m (up (up (up E))) (.bvar (.there (.there .here))) (.bvar .here))
        (.equal (.bvar .here) (.bvar (.there .here))))) <|
  .conj (GraphSyntax.edge_m E (numeral_m 0) (numeral_m 1)) <|
    .forallE .num <| .forallE .num <| .forallE .num <| .imp
      (GraphSyntax.edge_m (up (up (up E))) (.bvar (.there (.there .here))) (.bvar (.there .here))) <|
      .imp (GraphSyntax.edge_m (up (up (up E))) (succ_m (.bvar (.there (.there .here)))) (.bvar .here))
        (.equal (.bvar .here) (Term.app (σ := signature_m) .mul
          (.cons (.bvar (.there .here)) (.cons (numeral_m 2) .nil))))

def syntax_m {Γ Δ : SortContext signature_m} (V : Term signature_m Γ Δ .set) :
    Formula signature_m Γ Δ :=
  SecondOrderRelationSpecification.formula_m SecondOrderInternalFormulaSyntax.formula_m V
    (fun v => match v with | .here => V)

def evaluation_m {Γ Δ : SortContext signature_m} (E D Q R T : Term signature_m Γ Δ .set) :
    Formula signature_m Γ Δ :=
  SecondOrderRelationSpecification.formula_m SecondOrderEvaluationRule.formula_m T
    (fun v => match v with
      | .here => T
      | .there .here => E
      | .there (.there .here) => D
      | .there (.there (.there .here)) => Q
      | .there (.there (.there (.there .here))) => R)

def family_m {Γ Δ : SortContext signature_m} (E D T F : Term signature_m Γ Δ .set) :
    Formula signature_m Γ Δ :=
  SecondOrderRelationSpecification.formula_m SecondOrderDefinableFamily.formula_m F
    (fun v => match v with
      | .here => E
      | .there .here => D
      | .there (.there .here) => T)

def packet_m {Γ Δ : SortContext signature_m} (V E D Q R T F : Term signature_m Γ Δ .set) :
    Formula signature_m Γ Δ :=
  .conj (syntax_m V) <| .conj (powers_m E) <|
    .conj (.forallE .num (.rel .mem (.cons (.bvar .here) (.cons (up D) .nil)))) <|
      .conj (evaluation_m E D Q R T) (family_m E D T F)

def formula_m : Formula signature_m [] [.set, .set, .set, .set, .set, .set, .set] :=
  packet_m (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))

theorem pure_m : language_m formula_m = true := by
  have hV := SecondOrderRelationSpecification.pure_m SecondOrderInternalFormulaSyntax.formula_m
    (Γ := []) (Ξ := [.set, .set, .set, .set, .set, .set, .set]) (.fvar .here)
    (fun v => match v with | .here => .fvar .here) SecondOrderInternalFormulaSyntax.pure_m rfl
    (by
      intro s v
      cases v with
      | here => rfl
      | there v => nomatch v)
  have hT := SecondOrderRelationSpecification.pure_m SecondOrderEvaluationRule.formula_m
    (Γ := []) (Ξ := [.set, .set, .set, .set, .set, .set, .set])
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (fun v => match v with
      | .here => .fvar (.there (.there (.there (.there (.there .here)))))
      | .there .here => .fvar (.there .here)
      | .there (.there .here) => .fvar (.there (.there .here))
      | .there (.there (.there .here)) => .fvar (.there (.there (.there .here)))
      | .there (.there (.there (.there .here))) => .fvar (.there (.there (.there (.there .here)))))
    SecondOrderEvaluationRule.pure_m rfl (by
      intro s v
      cases v with
      | here => rfl
      | there v => cases v with
        | here => rfl
        | there v => cases v with
          | here => rfl
          | there v => cases v with
            | here => rfl
            | there v => cases v with
              | here => rfl
              | there v => nomatch v)
  have hF := SecondOrderRelationSpecification.pure_m SecondOrderDefinableFamily.formula_m
    (Γ := []) (Ξ := [.set, .set, .set, .set, .set, .set, .set])
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
    (fun v => match v with
      | .here => .fvar (.there .here)
      | .there .here => .fvar (.there (.there .here))
      | .there (.there .here) => .fvar (.there (.there (.there (.there (.there .here))))))
    SecondOrderDefinableFamily.pure_m rfl (by
      intro s v
      cases v with
      | here => rfl
      | there v => cases v with
        | here => rfl
        | there v => cases v with
          | here => rfl
          | there v => nomatch v)
  change (language_m (syntax_m _) && (language_m (powers_m _) &&
    (true && (language_m (evaluation_m _ _ _ _ _) && language_m (family_m _ _ _ _))))) = true
  simp only [syntax_m, evaluation_m, family_m]
  rw [hV, hT, hF]
  rfl

theorem powers_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (E : Term signature_m Γ Δ .set) : (powers_m E).satisfies η ↔
      SecondOrderBinaryPowers.spec_l (E.eval η) := by
  simp only [powers_m, Formula.satisfies, SecondOrderPairing.edge_l, up,
    Term.eval_weakenBound, Term.eval, succ_m]
  rfl

theorem syntax_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (V : Term signature_m Γ Δ .set) : (syntax_m V).satisfies η ↔
      SecondOrderInternalFormulaSyntax.spec_l (V.eval η) := by
  simp only [syntax_m, SecondOrderRelationSpecification.formula_l,
    SecondOrderInternalFormulaSyntax.formula_m, SecondOrderInternalFormulaSyntax.rule_formula_l]
  rfl

theorem evaluation_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (E D Q R T : Term signature_m Γ Δ .set) : (evaluation_m E D Q R T).satisfies η ↔
      SecondOrderEvaluationEquations.spec_l (E.eval η) (D.eval η) (Q.eval η) (R.eval η) (T.eval η) := by
  simp only [evaluation_m, SecondOrderRelationSpecification.formula_l, SecondOrderEvaluationRule.formula_l]
  rfl

theorem family_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (E D T F : Term signature_m Γ Δ .set) : (family_m E D T F).satisfies η ↔
      SecondOrderDefinableFamily.spec_l (E.eval η) (D.eval η) (T.eval η) (F.eval η) := by
  simp only [family_m, SecondOrderRelationSpecification.formula_l, SecondOrderDefinableFamily.formula_l]
  rfl

theorem packet_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (V E D Q R T F : Term signature_m Γ Δ .set) : (packet_m V E D Q R T F).satisfies η ↔
      SecondOrderInternalFormulaSyntax.spec_l (V.eval η) ∧ SecondOrderBinaryPowers.spec_l (E.eval η) ∧
      (∀ n, mem_l n (D.eval η)) ∧
      SecondOrderEvaluationEquations.spec_l (E.eval η) (D.eval η) (Q.eval η) (R.eval η) (T.eval η) ∧
      SecondOrderDefinableFamily.spec_l (E.eval η) (D.eval η) (T.eval η) (F.eval η) := by
  simp only [packet_m, Formula.satisfies, syntax_formula_l, powers_formula_l,
    evaluation_formula_l, family_formula_l, up, Arguments.eval, Term.eval_weakenBound, Term.eval]
  rfl

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberDefArithmetic
