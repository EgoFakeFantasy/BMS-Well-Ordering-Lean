import BMSConstructibleBridge.SecondOrderSourceEnvironment
import BMSConstructibleBridge.SecondOrderEvaluationLogic

/-!
# 全部上游纯集合公式的数码求值正确性

源结构由模型数域中的代表满射呈现，相等和成员由内部关系图正确表示。
证明复用上游语法和语义，允许非标准算术模型；不假定内部所有代码均外部有限。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSourceSatisfaction

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (value_l relation_l)
open SecondOrderAssignmentSyntax (valid_l)
open SecondOrderEvaluationEquations (spec_l)
open SecondOrderSourceEnvironment (represents_l)

set_option autoImplicit false

universe u v

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m} {𝒩 : FirstOrder.Structure.{0, 0, 0, v} ℒ}

def member_l (𝒩 : FirstOrder.Structure.{0, 0, 0, v} ℒ) (a b : 𝒩.Carrier .set) : Prop :=
  𝒩.relInterp .membership (.cons a (.cons b .nil))

theorem formula_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ} (hE : SecondOrderBinaryPowers.spec_l E)
    (D Q R T : set_l ℳ) (hT : spec_l E D Q R T) (f : num_l ℳ → 𝒩.Carrier .set)
    (hS : ∀ y, ∃ x, mem_l x D ∧ f x = y)
    (hQ : ∀ x y, mem_l x D → mem_l y D → (relation_l Q x y ↔ f x = f y))
    (hR : ∀ x y, mem_l x D → mem_l y D → (relation_l R x y ↔ member_l 𝒩 (f x) (f y)))
    {Γ Δ : SortContext ℒ} (φ : Formula ℒ Γ Δ) (η : Env 𝒩 Γ Δ) (l c : num_l ℳ)
    (hc : valid_l E c l) (hη : represents_l f η E D c) :
    relation_l T (SecondOrderFormulaCompilation.formula_l ℳ φ) (value_l l c) ↔ Formula.satisfies η φ := by
  classical
  match φ with
  | .falsum => exact ⟨fun h => SecondOrderEvaluationLogic.falsum_l hℳ E D Q R T hT _ h, False.elim⟩
  | .truth =>
      exact (SecondOrderEvaluationEquations.negation_l hℳ E D Q R T hT l c (zero_l ℳ) hc).trans
        ⟨fun _ => trivial, fun _ => SecondOrderEvaluationLogic.falsum_l hℳ E D Q R T hT _⟩
  | .rel .membership (.cons s (.cons t .nil)) =>
      exact (SecondOrderEvaluationEquations.membership_l hℳ E D Q R T hT l c _ _ hc).trans
        (SecondOrderSourceEnvironment.atom_l f η E D R c hη (member_l 𝒩) hR s t)
  | @Formula.equal _ _ _ .set s t =>
      exact (SecondOrderEvaluationEquations.equality_l hℳ E D Q R T hT l c _ _ hc).trans
        (SecondOrderSourceEnvironment.atom_l f η E D Q c hη (fun a b => a = b) hQ s t)
  | .neg φ =>
      exact (SecondOrderEvaluationEquations.negation_l hℳ E D Q R T hT l c _ hc).trans
        (not_congr (formula_l hℳ hE D Q R T hT f hS hQ hR φ η l c hc hη))
  | .conj φ ψ =>
      exact (SecondOrderEvaluationEquations.conjunction_l hℳ E D Q R T hT l c _ _ hc).trans
        (and_congr (formula_l hℳ hE D Q R T hT f hS hQ hR φ η l c hc hη)
          (formula_l hℳ hE D Q R T hT f hS hQ hR ψ η l c hc hη))
  | .disj φ ψ =>
      exact (SecondOrderEvaluationLogic.disjunction_l hℳ E D Q R T hT l c _ _ hc).trans
        (or_congr (formula_l hℳ hE D Q R T hT f hS hQ hR φ η l c hc hη)
          (formula_l hℳ hE D Q R T hT f hS hQ hR ψ η l c hc hη))
  | .imp φ ψ =>
      exact (SecondOrderEvaluationLogic.implication_l hℳ E D Q R T hT l c _ _ hc).trans
        (imp_congr (formula_l hℳ hE D Q R T hT f hS hQ hR φ η l c hc hη)
          (formula_l hℳ hE D Q R T hT f hS hQ hR ψ η l c hc hη))
  | .iff φ ψ =>
      exact (SecondOrderEvaluationLogic.biconditional_l hℳ E D Q R T hT l c _ _ hc).trans
        (iff_congr (formula_l hℳ hE D Q R T hT f hS hQ hR φ η l c hc hη)
          (formula_l hℳ hE D Q R T hT f hS hQ hR ψ η l c hc hη))
  | .forallE .set φ =>
      refine (SecondOrderEvaluationLogic.universal_l hℳ E D Q R T hT l c _ hc).trans ?_
      constructor
      · intro h y
        obtain ⟨x, hx, hxy⟩ := hS y
        obtain ⟨d, hd⟩ := SecondOrderAssignmentCongruence.extension_exists_l hℳ hE c l x hc
        have hφ := (formula_l hℳ hE D Q R T hT f hS hQ hR φ (η.pushBound (f x)) (succ_l l) d hd.1
          (SecondOrderSourceEnvironment.extend_l f η E D c l d x hη hd hx)).mp (h x hx d hd)
        exact hxy ▸ hφ
      · intro h x hx d hd
        exact (formula_l hℳ hE D Q R T hT f hS hQ hR φ (η.pushBound (f x)) (succ_l l) d hd.1
          (SecondOrderSourceEnvironment.extend_l f η E D c l d x hη hd hx)).mpr (h (f x))
  | .existsE .set φ =>
      refine (SecondOrderEvaluationEquations.existential_l hℳ E D Q R T hT l c _ hc).trans ?_
      constructor
      · rintro ⟨x, d, hx, hd, h⟩
        exact ⟨f x, (formula_l hℳ hE D Q R T hT f hS hQ hR φ (η.pushBound (f x)) (succ_l l) d hd.1
          (SecondOrderSourceEnvironment.extend_l f η E D c l d x hη hd hx)).mp h⟩
      · rintro ⟨y, hy⟩
        obtain ⟨x, hx, hxy⟩ := hS y
        obtain ⟨d, hd⟩ := SecondOrderAssignmentCongruence.extension_exists_l hℳ hE c l x hc
        exact ⟨x, d, hx, hd,
          (formula_l hℳ hE D Q R T hT f hS hQ hR φ (η.pushBound (f x)) (succ_l l) d hd.1
            (SecondOrderSourceEnvironment.extend_l f η E D c l d x hη hd hx)).mpr (hxy.symm ▸ hy)⟩
termination_by φ.size
decreasing_by all_goals simp only [Formula.size]; omega

theorem closed_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ} (hE : SecondOrderBinaryPowers.spec_l E)
    (D Q R T : set_l ℳ) (hT : spec_l E D Q R T) (f : num_l ℳ → 𝒩.Carrier .set)
    (hS : ∀ y, ∃ x, mem_l x D ∧ f x = y)
    (hQ : ∀ x y, mem_l x D → mem_l y D → (relation_l Q x y ↔ f x = f y))
    (hR : ∀ x y, mem_l x D → mem_l y D → (relation_l R x y ↔ member_l 𝒩 (f x) (f y)))
    (φ : Sentence ℒ) :
    relation_l T (SecondOrderFormulaCompilation.formula_l ℳ φ) (value_l (zero_l ℳ) (zero_l ℳ)) ↔
      φ.TrueIn 𝒩 :=
  formula_l hℳ hE D Q R T hT f hS hQ hR φ Env.empty (zero_l ℳ) (zero_l ℳ)
    ((SecondOrderAssignmentCongruence.valid_iff_l hE _ _).mpr (SecondOrderAssignment.empty_l hℳ hE))
    (SecondOrderSourceEnvironment.empty_l f E D (zero_l ℳ))

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSourceSatisfaction
