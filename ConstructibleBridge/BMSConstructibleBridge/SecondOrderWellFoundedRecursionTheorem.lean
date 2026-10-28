import BMSConstructibleBridge.SecondOrderWellFoundedRecursion
import YesMetaZFC.Automation.ModelClosure

/-! # 内部良基递归的原对象推导模式

每个实际操作公式及其参数实例得到原 Z₂ 中的正式推导。良基、传递、
非自返、全域和严格前驱局部性都是模式中的显式前提，不冒充无条件反射。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderWellFoundedRecursionTheorem

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderWellFoundedInduction (parameters_l parameters_pushBound_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private def operation {Γ Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ)
    (H U : Term signature_m Γ Δ .set) : Formula signature_m Γ Δ :=
  SecondOrderSetOperator.formula_m φ H U (fun v => .fvar v)

private theorem operation_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (φ : Formula signature_m [.set, .set] Δ) (H U : Term signature_m Γ Δ .set) :
    (operation φ H U).satisfies η ↔ SecondOrderSetOperator.relation_l φ (parameters_l η) (H.eval η) (U.eval η) :=
  SecondOrderSetOperator.formula_l η φ H U (fun v => .fvar v)

def wellFounded_m {Γ Δ : SortContext signature_m} (R : Term signature_m Γ Δ .set) : Formula signature_m Γ Δ :=
  .forallE .num (GraphTranslation.domain_m (R.weakenBound sort_m.num) (.bvar .here))

def transitive_m {Γ Δ : SortContext signature_m} (R : Term signature_m Γ Δ .set) : Formula signature_m Γ Δ :=
  let R' := R.weakenBound sort_m.num |>.weakenBound sort_m.num |>.weakenBound sort_m.num
  .forallE .num <| .forallE .num <| .forallE .num <| .imp
    (GraphSyntax.edge_m R' (.bvar (.there (.there .here))) (.bvar (.there .here))) <| .imp
      (GraphSyntax.edge_m R' (.bvar (.there .here)) (.bvar .here))
      (GraphSyntax.edge_m R' (.bvar (.there (.there .here))) (.bvar .here))

def irreflexive_m {Γ Δ : SortContext signature_m} (R : Term signature_m Γ Δ .set) : Formula signature_m Γ Δ :=
  .forallE .num (.neg (GraphSyntax.edge_m (R.weakenBound sort_m.num) (.bvar .here) (.bvar .here)))

def total_m {Γ Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ) : Formula signature_m Γ Δ :=
  .forallE .set <| .existsE .set <| operation φ (.bvar (.there .here)) (.bvar .here)

def fixed_m {Γ Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ) : Formula signature_m Γ Δ :=
  .existsE .set <| .conj (operation φ (.bvar .here) (.bvar .here)) <|
    .forallE .set <| .imp (operation φ (.bvar .here) (.bvar .here)) <|
      .forallE .num <| .iff
        (.rel .mem (.cons (.bvar .here) (.cons (.bvar (.there .here)) .nil)))
        (.rel .mem (.cons (.bvar .here) (.cons (.bvar (.there (.there .here))) .nil)))

def local_m {Γ Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ)
    (R : Term signature_m Γ Δ .set) : Formula signature_m Γ Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <| .forallE .set <| .forallE .num <|
    let H : Term signature_m (.num :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
      .bvar (.there (.there (.there (.there .here))))
    let K : Term signature_m (.num :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
      .bvar (.there (.there (.there .here)))
    let U : Term signature_m (.num :: .set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
    let V : Term signature_m (.num :: .set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let n : Term signature_m (.num :: .set :: .set :: .set :: .set :: Γ) Δ .num := .bvar .here
    let R' := R.weakenBound sort_m.set |>.weakenBound sort_m.set |>.weakenBound sort_m.set |>.weakenBound sort_m.set |>.weakenBound sort_m.num
    .imp (operation φ H U) <| .imp (operation φ K V) <| .imp
      (.forallE .num <| .imp (GraphSyntax.edge_m (R'.weakenBound sort_m.num) (.bvar .here) (n.weakenBound sort_m.num)) <|
        .forallE .num <| .iff
          (GraphSyntax.edge_m (H.weakenBound sort_m.num |>.weakenBound sort_m.num) (.bvar (.there .here)) (.bvar .here))
          (GraphSyntax.edge_m (K.weakenBound sort_m.num |>.weakenBound sort_m.num) (.bvar (.there .here)) (.bvar .here)))
      (.forallE .num <| .iff
        (GraphSyntax.edge_m (U.weakenBound sort_m.num) (n.weakenBound sort_m.num) (.bvar .here))
        (GraphSyntax.edge_m (V.weakenBound sort_m.num) (n.weakenBound sort_m.num) (.bvar .here)))

def schema_m {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ) : Formula signature_m [] Δ :=
  .forallE .set <| .imp (wellFounded_m (.bvar .here)) <| .imp (transitive_m (.bvar .here)) <|
    .imp (irreflexive_m (.bvar .here)) <| .imp (total_m φ) <|
      .imp (local_m φ (.bvar .here)) (fixed_m φ)

def sentence_m {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ) : Sentence signature_m :=
  Metatheory.Formula.forall_close (schema_m φ)

theorem wellFounded_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (R : Term signature_m Γ Δ .set) : (wellFounded_m R).satisfies η ↔
      ∀ n, SecondOrderDomain.wf_l (R.eval η) n := by
  simp only [wellFounded_m, Formula.satisfies, SecondOrderInterpretation.domain_l, Term.eval_weakenBound, Term.eval]
  rfl

theorem transitive_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (R : Term signature_m Γ Δ .set) : (transitive_m R).satisfies η ↔
      ∀ a b c, SecondOrderPairing.relation_l (R.eval η) a b →
        SecondOrderPairing.relation_l (R.eval η) b c → SecondOrderPairing.relation_l (R.eval η) a c := by
  simp only [transitive_m, Formula.satisfies, SecondOrderPairing.edge_l, Term.eval_weakenBound, Term.eval]
  rfl

theorem irreflexive_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (R : Term signature_m Γ Δ .set) : (irreflexive_m R).satisfies η ↔
      ∀ n, ¬SecondOrderPairing.relation_l (R.eval η) n n := by
  simp only [irreflexive_m, Formula.satisfies, SecondOrderPairing.edge_l, Term.eval_weakenBound, Term.eval]
  rfl

theorem total_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (φ : Formula signature_m [.set, .set] Δ) : (total_m φ).satisfies η ↔
      ∀ H, ∃ U, SecondOrderSetOperator.relation_l φ (parameters_l η) H U := by
  simp only [total_m, Formula.satisfies, operation_l, parameters_pushBound_l, Term.eval]
  rfl

theorem fixed_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (φ : Formula signature_m [.set, .set] Δ) : (fixed_m φ).satisfies η ↔
      ∃ S, SecondOrderSetOperator.relation_l φ (parameters_l η) S S ∧
        ∀ T, SecondOrderSetOperator.relation_l φ (parameters_l η) T T → ∀ a, mem_l a T ↔ mem_l a S := by
  simp only [fixed_m, Formula.satisfies, operation_l, parameters_pushBound_l, Term.eval]
  rfl

theorem local_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (φ : Formula signature_m [.set, .set] Δ) (R : Term signature_m Γ Δ .set) :
    (local_m φ R).satisfies η ↔
      SecondOrderWellFoundedAgreement.local_l (SecondOrderSetOperator.relation_l φ (parameters_l η)) (R.eval η) := by
  simp only [local_m, Formula.satisfies, operation_l, parameters_pushBound_l,
    SecondOrderPairing.edge_l, Term.eval_weakenBound, Term.eval]
  constructor
  · intro h H K U V hU hV n hn a
    exact h H K U V n hU hV hn a
  · intro h H K U V n hU hV hn a
    exact h H K U V hU hV n hn a

theorem models_l (hℳ : Theory.Models ℳ theory_m) {Δ : SortContext signature_m}
    (φ : Formula signature_m [.set, .set] Δ) (hφ : language_m φ = true) (η : Env ℳ [] Δ) :
    (schema_m φ).satisfies η := by
  intro R hWf hTrans hIrrefl hTotal hLocal
  apply (fixed_formula_l _ φ).mpr
  obtain ⟨S, hS, hUnique⟩ := SecondOrderWellFoundedRecursion.exists_l hℳ φ hφ (parameters_l (η.pushBound R)) R
    ((wellFounded_formula_l _ _).mp hWf) ((transitive_formula_l _ _).mp hTrans)
    ((irreflexive_formula_l _ _).mp hIrrefl) ((local_formula_l _ φ _).mp hLocal)
    ((total_formula_l _ φ).mp hTotal)
  exact ⟨S, hS, fun T hT a => (hUnique T hT) ▸ Iff.rfl⟩

theorem derives_m {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ)
    (hφ : language_m φ = true) : Derives theory_m [] (sentence_m φ) := by
  apply SecondOrderCompleteness.derives_m
  intro ℳ hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  exact models_l hℳ φ hφ η

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderWellFoundedRecursionTheorem
