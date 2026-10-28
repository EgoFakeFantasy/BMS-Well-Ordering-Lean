import BMSConstructibleBridge.SecondOrderFormulaParameters
import BMSConstructibleBridge.SecondOrderRelationSpecification
import BMSConstructibleBridge.SecondOrderWellFoundedAgreement

/-! # 唯一逐行操作的实际全历史算子

逐行正文是原语言公式，自由槽为输出实数、阶段数、历史实数和额外参数。
全历史输出由一次二元理解构造，不选取实数值函数。原图唯一性保证存在式
成员定义恰好给出每个阶段的那一行；前驱局部性也按同一正文传输。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPointwiseOperator

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def stage_l {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.set :: .num :: .set :: Δ))
    (η : Env ℳ [] Δ) (H : set_l ℳ) (n : num_l ℳ) (W : set_l ℳ) : Prop :=
  φ.satisfies (((η.pushFree H).pushFree n).pushFree W)

private def insert_m {Δ : SortContext signature_m} :
    VariableSubstitution signature_m (.set :: .num :: .set :: Δ) [.set]
      (.num :: .num :: .set :: Δ)
  | _, .here => .bvar .here
  | _, .there .here => .fvar .here
  | _, .there (.there .here) => .fvar (.there (.there .here))
  | _, .there (.there (.there v)) => .fvar (.there (.there (.there v)))

def body_m {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.set :: .num :: .set :: Δ)) :
    Formula signature_m [] (.num :: .num :: .set :: Δ) :=
  .existsE .set <| .conj (SecondOrderFormulaParameters.formula_m φ insert_m)
    (.rel .mem (.cons (.fvar (.there .here)) (.cons (.bvar .here) .nil)))

theorem body_pure_m {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.set :: .num :: .set :: Δ))
    (hφ : language_m φ = true) : language_m (body_m φ) = true := by
  have hBody := SecondOrderFormulaParameters.pure_m φ insert_m hφ (by
    intro s v
    cases v with
    | here => rfl
    | there v => cases v with
      | here => rfl
      | there v => cases v with
        | here => rfl
        | there v => cases s <;> rfl)
  change (language_m _ && true) = true
  exact congrArg (fun b : Bool => b && true) hBody

theorem body_formula_l {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.set :: .num :: .set :: Δ)) (η : Env ℳ [] Δ)
    (H : set_l ℳ) (n t : num_l ℳ) :
    (body_m φ).satisfies (((η.pushFree H).pushFree t).pushFree n) ↔
      ∃ W, stage_l φ η H n W ∧ mem_l t W := by
  simp only [body_m, Formula.satisfies, SecondOrderFormulaParameters.formula_l]
  apply exists_congr
  intro W
  apply and_congr _ Iff.rfl
  unfold stage_l
  apply Iff.of_eq
  apply congrArg (fun ξ => φ.satisfies ξ)
  apply Env.ext (bound := []) (fun {_} v => nomatch v)
  · intro s v
    rcases v with _ | _ | _ | v
    all_goals first | rfl | cases s <;> rfl

private def parameters_m {Δ : SortContext signature_m} :
    VariableSubstitution signature_m (.set :: Δ) [.set, .set] Δ
  | _, .here => .bvar (.there .here)
  | _, .there v => .fvar v

def formula_m {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.set :: .num :: .set :: Δ)) :
    Formula signature_m [.set, .set] Δ :=
  SecondOrderRelationSpecification.formula_m (body_m φ) (.bvar .here) parameters_m

theorem pure_m {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.set :: .num :: .set :: Δ))
    (hφ : language_m φ = true) : language_m (formula_m φ) = true := by
  apply SecondOrderRelationSpecification.pure_m _ _ _ (body_pure_m φ hφ) rfl
  intro s v
  cases v with
  | here => rfl
  | there v => cases s <;> rfl

theorem formula_l {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.set :: .num :: .set :: Δ)) (η : Env ℳ [] Δ)
    (H U : set_l ℳ) : SecondOrderSetOperator.relation_l (formula_m φ) η H U ↔
      ∀ n t, relation_l U n t ↔ ∃ W, stage_l φ η H n W ∧ mem_l t W := by
  unfold SecondOrderSetOperator.relation_l formula_m
  rw [SecondOrderRelationSpecification.formula_l]
  have hEnv : SecondOrderRelationSpecification.parameters_l ((η.pushBound H).pushBound U)
      parameters_m = η.pushFree H := by
    apply Env.ext (bound := []) (fun {_} v => nomatch v)
    · intro s v
      cases v with
      | here => rfl
      | there v => cases s <;> rfl
  rw [hEnv]
  simp only [Term.eval, body_formula_l]
  rfl

theorem total_l (hℳ : Theory.Models ℳ theory_m) {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.set :: .num :: .set :: Δ))
    (hφ : language_m φ = true) (η : Env ℳ [] Δ) :
    ∀ H, ∃ U, SecondOrderSetOperator.relation_l (formula_m φ) η H U := by
  intro H
  obtain ⟨U, hU⟩ := SecondOrderRelations.comprehension_l hℳ (body_m φ)
    (body_pure_m φ hφ) (η.pushFree H)
  exact ⟨U, (formula_l φ η H U).mpr (fun n t => (hU n t).trans (body_formula_l φ η H n t))⟩

theorem rows_l {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.set :: .num :: .set :: Δ)) (η : Env ℳ [] Δ)
    {H U : set_l ℳ} (hU : SecondOrderSetOperator.relation_l (formula_m φ) η H U)
    (hTotal : ∀ n, ∃! W, stage_l φ η H n W) :
    ∀ n, ∃ W, stage_l φ η H n W ∧ SecondOrderSections.spec_l U n W := by
  intro n
  obtain ⟨W, hW, hUnique⟩ := hTotal n
  refine ⟨W, hW, fun t => ?_⟩
  rw [(formula_l φ η H U).mp hU n t]
  constructor
  · exact fun ht => ⟨W, hW, ht⟩
  · rintro ⟨Y, hY, ht⟩
    exact hUnique Y hY ▸ ht

theorem local_l {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.set :: .num :: .set :: Δ)) (η : Env ℳ [] Δ) (R : set_l ℳ)
    (h : ∀ H K n, (∀ i, relation_l R i n → ∀ t, relation_l H i t ↔ relation_l K i t) →
      ∀ W, stage_l φ η H n W ↔ stage_l φ η K n W) :
    SecondOrderWellFoundedAgreement.local_l (SecondOrderSetOperator.relation_l (formula_m φ) η) R := by
  intro H K U V hU hV n hPast t
  rw [(formula_l φ η H U).mp hU, (formula_l φ η K V).mp hV]
  exact exists_congr (fun W => and_congr (h H K n hPast W) Iff.rfl)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPointwiseOperator
