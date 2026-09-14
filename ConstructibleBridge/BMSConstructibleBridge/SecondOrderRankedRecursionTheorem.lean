import BMSConstructibleBridge.SecondOrderRankedRecursion
import BMSConstructibleBridge.SecondOrderSetIterationTheorem

/-!
# 内部数值编号递归的对象方案

全域性和严格初段局部性均为句中的明确前提，结论为唯一内部固定点。
它将用于求值算子的正确性，不直接断言某个尚未构造的满足关系已存在。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRankedRecursionTheorem

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderSetIterationTheorem (parameters_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private def operation {Γ Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ)
    (X Y : Term signature_m Γ Δ .set) : Formula signature_m Γ Δ :=
  SecondOrderSetOperator.formula_m φ X Y (fun v => .fvar v)

def total_m {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ) : Formula signature_m [] Δ :=
  .forallE .set (.existsE .set (operation φ (.bvar (.there .here)) (.bvar .here)))

def local_m {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ) : Formula signature_m [] Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <| .forallE .set <| .forallE .num <| .forallE .num <|
    .imp (operation φ (.bvar (.there (.there (.there (.there (.there .here))))))
      (.bvar (.there (.there (.there .here)))))
      (.imp (operation φ (.bvar (.there (.there (.there (.there .here))))) (.bvar (.there (.there .here))))
        (.imp (SecondOrderInitialAgreement.formula_m
          (.bvar (.there (.there (.there (.there (.there .here))))))
          (.bvar (.there (.there (.there (.there .here))))) (.bvar (.there .here)))
          (.iff (GraphSyntax.edge_m (.bvar (.there (.there (.there .here)))) (.bvar (.there .here)) (.bvar .here))
            (GraphSyntax.edge_m (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)))))

def fixed_m {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ) : Formula signature_m [] Δ :=
  .existsE .set (.conj (operation φ (.bvar .here) (.bvar .here))
    (.forallE .set (.imp (operation φ (.bvar .here) (.bvar .here))
      (.forallE .num (.iff
        (.rel .mem (.cons (.bvar .here) (.cons (.bvar (.there .here)) .nil)))
        (.rel .mem (.cons (.bvar .here) (.cons (.bvar (.there (.there .here))) .nil))))))))

def schema_m {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ) :
    Formula signature_m [] Δ := .imp (total_m φ) (.imp (local_m φ) (fixed_m φ))

def sentence_m {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ) :
    Sentence signature_m := Metatheory.Formula.forall_close (schema_m φ)

theorem pure_m {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ)
    (hφ : language_m φ = true) : language_m (schema_m φ) = true := by
  have h {Γ : SortContext signature_m} (X Y : Term signature_m Γ Δ .set)
      (hX : pure_term_m X = true) (hY : pure_term_m Y = true) : language_m (operation φ X Y) = true :=
    SecondOrderSetOperator.pure_m φ X Y _ hφ hX hY (fun _ => rfl)
  simp only [schema_m, total_m, local_m, fixed_m, language_m]
  rw [h (Γ := [.set, .set]) (.bvar (.there .here)) (.bvar .here) rfl rfl,
    h (Γ := [.num, .num, .set, .set, .set, .set])
      (.bvar (.there (.there (.there (.there (.there .here))))))
      (.bvar (.there (.there (.there .here)))) rfl rfl,
    h (Γ := [.num, .num, .set, .set, .set, .set])
      (.bvar (.there (.there (.there (.there .here))))) (.bvar (.there (.there .here))) rfl rfl,
    h (Γ := [.set]) (.bvar .here) (.bvar .here) rfl rfl,
    h (Γ := [.set, .set]) (.bvar .here) (.bvar .here) rfl rfl]
  rfl

theorem total_l {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ) (η : Env ℳ [] Δ) :
    Formula.satisfies η (total_m φ) ↔ ∀ X, ∃ Y, SecondOrderSetOperator.relation_l φ (parameters_l η) X Y := by
  simp only [total_m, Formula.satisfies, operation, SecondOrderSetOperator.formula_l]
  rfl

theorem local_l {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ) (η : Env ℳ [] Δ) :
    Formula.satisfies η (local_m φ) ↔
      SecondOrderRankedStability.local_l (SecondOrderSetOperator.relation_l φ (parameters_l η)) := by
  simp only [local_m, Formula.satisfies, operation, SecondOrderSetOperator.formula_l,
    SecondOrderInitialAgreement.formula_l, SecondOrderPairing.edge_l]
  constructor
  · intro h X Y U V hU hV n hn a
    exact h X Y U V n a hU hV hn
  · intro h X Y U V n a hU hV hn
    exact h X Y U V hU hV n hn a

theorem fixed_l {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ) (η : Env ℳ [] Δ) :
    Formula.satisfies η (fixed_m φ) ↔ ∃ S,
      SecondOrderSetOperator.relation_l φ (parameters_l η) S S ∧
        ∀ T, SecondOrderSetOperator.relation_l φ (parameters_l η) T T → ∀ a, mem_l a T ↔ mem_l a S := by
  simp only [fixed_m, Formula.satisfies, operation, SecondOrderSetOperator.formula_l]
  rfl

theorem models_l (hℳ : Theory.Models ℳ theory_m) {Δ : SortContext signature_m}
    (φ : Formula signature_m [.set, .set] Δ) (hφ : language_m φ = true) (η : Env ℳ [] Δ) :
    Formula.satisfies η (schema_m φ) := by
  change Formula.satisfies η (total_m φ) → Formula.satisfies η (local_m φ) → Formula.satisfies η (fixed_m φ)
  rw [total_l, local_l, fixed_l]
  intro hT hP
  obtain ⟨S, hS, hU⟩ := SecondOrderRankedRecursion.exists_l hℳ φ hφ (parameters_l η) hT hP
  exact ⟨S, hS, fun T hT a => (hU T hT) ▸ Iff.rfl⟩

theorem derives_m {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ)
    (hφ : language_m φ = true) : Derives theory_m [] (sentence_m φ) := by
  apply SecondOrderCompleteness.derives_m
  intro ℳ hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff (schema_m φ)).mpr
  exact models_l hℳ φ hφ

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRankedRecursionTheorem
