import BMSConstructibleBridge.SecondOrderSetIteration
import BMSConstructibleBridge.SecondOrderCompleteness
import YesMetaZFC.Automation.ModelClosure

/-!
# 唯一集合值迭代的对象方案

每个实际操作公式及其全部参数给出一个对象 `Z₂` 定理：若操作全域且输出唯一，
则任意初值都有内部阶段图。前提不会被删除，也不替换成任意关系的依赖选择。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSetIterationTheorem

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private def zero {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .zero .nil

private def succ {Γ Δ : SortContext signature_m} (s : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num := Term.app (σ := signature_m) .succ (.cons s .nil)

private def operation {Γ Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ)
    (X Y : Term signature_m Γ Δ .set) : Formula signature_m Γ Δ :=
  SecondOrderSetOperator.formula_m φ X Y (fun v => .fvar v)

def total_m {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ) : Formula signature_m [] Δ :=
  .conj (.forallE .set (.existsE .set (operation φ (.bvar (.there .here)) (.bvar .here))))
    (.forallE .set (.forallE .set (.forallE .set (.imp
      (operation φ (.bvar (.there (.there .here))) (.bvar (.there .here)))
      (.imp (operation φ (.bvar (.there (.there .here))) (.bvar .here))
        (.forallE .num (.iff
          (.rel .mem (.cons (.bvar .here) (.cons (.bvar (.there (.there .here))) .nil)))
          (.rel .mem (.cons (.bvar .here) (.cons (.bvar (.there .here)) .nil))))))))))

def iteration_m {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ) :
    Formula signature_m [] Δ :=
  .forallE .set <| .existsE .set <|
    .conj (SecondOrderSections.formula_m (.bvar .here) (.bvar (.there .here)) zero) <|
      .forallE .num <| .forallE .set <| .forallE .set <|
        .imp (SecondOrderSections.formula_m (.bvar (.there (.there (.there .here))))
          (.bvar (.there .here)) (.bvar (.there (.there .here))))
          (.imp (SecondOrderSections.formula_m (.bvar (.there (.there (.there .here))))
            (.bvar .here) (succ (.bvar (.there (.there .here)))))
            (operation φ (.bvar (.there .here)) (.bvar .here)))

def schema_m {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ) :
    Formula signature_m [] Δ := .imp (total_m φ) (iteration_m φ)

def sentence_m {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ) :
    Sentence signature_m := Metatheory.Formula.forall_close (schema_m φ)

theorem pure_m {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ)
    (hφ : language_m φ = true) : language_m (schema_m φ) = true := by
  have h {Γ : SortContext signature_m} (X Y : Term signature_m Γ Δ .set)
      (hX : pure_term_m X = true) (hY : pure_term_m Y = true) : language_m (operation φ X Y) = true :=
    SecondOrderSetOperator.pure_m φ X Y _ hφ hX hY (fun _ => rfl)
  simp only [schema_m, total_m, iteration_m, language_m]
  rw [h (Γ := [.set, .set]) (.bvar (.there .here)) (.bvar .here) rfl rfl,
    h (Γ := [.set, .set, .set]) (.bvar (.there (.there .here))) (.bvar (.there .here)) rfl rfl,
    h (Γ := [.set, .set, .set]) (.bvar (.there (.there .here))) (.bvar .here) rfl rfl,
    h (Γ := [.set, .set, .num, .set, .set]) (.bvar (.there .here)) (.bvar .here) rfl rfl]
  rfl

def parameters_l {Δ : SortContext signature_m} (η : Env ℳ [] Δ) : Env ℳ [] Δ :=
  SecondOrderSetOperator.parameters_l η (fun v => .fvar v)

theorem total_l {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ) (η : Env ℳ [] Δ) :
    Formula.satisfies η (total_m φ) ↔
      (∀ X, ∃ Y, SecondOrderSetOperator.relation_l φ (parameters_l η) X Y) ∧
        ∀ X Y Z, SecondOrderSetOperator.relation_l φ (parameters_l η) X Y →
          SecondOrderSetOperator.relation_l φ (parameters_l η) X Z → ∀ a, mem_l a Y ↔ mem_l a Z := by
  simp only [total_m, Formula.satisfies, operation, SecondOrderSetOperator.formula_l]
  rfl

theorem iteration_l {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ) (η : Env ℳ [] Δ) :
    Formula.satisfies η (iteration_m φ) ↔
      ∀ A, ∃ G, SecondOrderSetIteration.spec_l (SecondOrderSetOperator.relation_l φ (parameters_l η)) G A := by
  simp only [iteration_m, Formula.satisfies, SecondOrderSections.formula_l,
    operation, SecondOrderSetOperator.formula_l]
  rfl

theorem models_l (hℳ : Theory.Models ℳ theory_m) {Δ : SortContext signature_m}
    (φ : Formula signature_m [.set, .set] Δ) (hφ : language_m φ = true) (η : Env ℳ [] Δ) :
    Formula.satisfies η (schema_m φ) := by
  change Formula.satisfies η (total_m φ) → Formula.satisfies η (iteration_m φ)
  rw [total_l, iteration_l]
  intro h A
  exact SecondOrderSetIteration.exists_l hℳ φ hφ (parameters_l η) A h.1
    (fun X Y Z hY hZ => ext_l hℳ Y Z (h.2 X Y Z hY hZ))

/-- 任意操作公式的完整参数闭方案，具有实际对象推导。 -/
theorem derives_m {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ)
    (hφ : language_m φ = true) : Derives theory_m [] (sentence_m φ) := by
  apply SecondOrderCompleteness.derives_m
  intro ℳ hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff (schema_m φ)).mpr
  exact models_l hℳ φ hφ

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSetIterationTheorem
