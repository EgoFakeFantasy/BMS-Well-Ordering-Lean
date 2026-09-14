import BMSConstructibleBridge.SecondOrderSourceSatisfaction

/-!
# 每个有限源环境的内部赋值存在性

先编入自由参数，再逐个前插绑定参数。存在性只使用有限上下文归纳及已证的
内部前插，不假定任意外部函数图属于模型的集合域。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSourceAssignment

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderSequenceSyntax (read_l)
open SecondOrderAssignmentSyntax (valid_l extension_l)
open SecondOrderSourceEnvironment (represents_l)
open SecondOrderFormulaCompilation (term_l)

set_option autoImplicit false

universe u v

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m} {𝒩 : FirstOrder.Structure.{0, 0, 0, v} ℒ}

theorem free_extend_l {Δ : SortContext ℒ} (f : num_l ℳ → 𝒩.Carrier .set)
    (η : Env 𝒩 [] Δ) (E D : set_l ℳ) (c l d x : num_l ℳ)
    (hη : represents_l f η E D c) (hd : extension_l E c l d x) (hx : mem_l x D) :
    represents_l f (η.pushFree (f x)) E D d := by
  intro t
  match t with
  | .bvar w => nomatch w
  | .fvar .here => exact ⟨x, (hd.2.1 x).mpr rfl, fun y hy => (hd.2.1 y).mp hy, hx, rfl⟩
  | .fvar (.there w) =>
      obtain ⟨y, hy, hU, hD, hf⟩ := hη (.fvar w)
      exact ⟨y, (hd.2.2 _ y).mpr hy, fun z hz => hU z ((hd.2.2 _ z).mp hz), hD, hf⟩
  | .app g _ => nomatch g

theorem free_exists_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
    (hE : SecondOrderBinaryPowers.spec_l E) (D : set_l ℳ) (f : num_l ℳ → 𝒩.Carrier .set)
    (hS : ∀ y, ∃ x, mem_l x D ∧ f x = y) {Δ : SortContext ℒ} (η : Env 𝒩 [] Δ) :
    ∃ l c, valid_l E c l ∧ represents_l f η E D c := by
  induction Δ with
  | nil =>
      have h : η = Env.empty := by
        apply Env.ext
        · intro s w
          nomatch w
        · intro s w
          nomatch w
      subst η
      exact ⟨zero_l ℳ, zero_l ℳ,
        (SecondOrderAssignmentCongruence.valid_iff_l hE _ _).mpr (SecondOrderAssignment.empty_l hℳ hE),
        SecondOrderSourceEnvironment.empty_l f E D _⟩
  | cons s Δ ih =>
      cases s
      let η₀ : Env 𝒩 [] Δ := { boundVal := (fun w => nomatch w), freeVal := fun w => η.freeVal (.there w) }
      obtain ⟨l, c, hc, hη⟩ := ih η₀
      obtain ⟨x, hx, hfx⟩ := hS (η.freeVal .here)
      obtain ⟨d, hd⟩ := SecondOrderAssignmentCongruence.extension_exists_l hℳ hE c l x hc
      have h : η₀.pushFree (f x) = η := by
        apply Env.ext
        · intro s w
          nomatch w
        · intro s w
          match w with
          | .here => exact hfx
          | .there w => rfl
      exact ⟨succ_l l, d, hd.1, h ▸ free_extend_l f η₀ E D c l d x hη hd hx⟩

theorem exists_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
    (hE : SecondOrderBinaryPowers.spec_l E) (D : set_l ℳ) (f : num_l ℳ → 𝒩.Carrier .set)
    (hS : ∀ y, ∃ x, mem_l x D ∧ f x = y) {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ) :
    ∃ l c, valid_l E c l ∧ represents_l f η E D c := by
  induction Γ with
  | nil => exact free_exists_l hℳ hE D f hS η
  | cons s Γ ih =>
      cases s
      let η₀ : Env 𝒩 Γ Δ := { boundVal := fun w => η.boundVal (.there w), freeVal := η.freeVal }
      obtain ⟨l, c, hc, hη⟩ := ih η₀
      obtain ⟨x, hx, hfx⟩ := hS (η.boundVal .here)
      obtain ⟨d, hd⟩ := SecondOrderAssignmentCongruence.extension_exists_l hℳ hE c l x hc
      have h : η₀.pushBound (f x) = η := by
        apply Env.ext
        · intro s w
          match w with
          | .here => exact hfx
          | .there w => rfl
        · intro s w
          rfl
      exact ⟨succ_l l, d, hd.1, h ▸ SecondOrderSourceEnvironment.extend_l f η₀ E D c l d x hη hd hx⟩

/-- 每个源环境都有实际赋值码，并对同一上下文的全部公式同时正确。 -/
theorem satisfaction_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
    (hE : SecondOrderBinaryPowers.spec_l E) (D Q R T : set_l ℳ)
    (hT : SecondOrderEvaluationEquations.spec_l E D Q R T) (f : num_l ℳ → 𝒩.Carrier .set)
    (hS : ∀ y, ∃ x, mem_l x D ∧ f x = y)
    (hQ : ∀ x y, mem_l x D → mem_l y D → (SecondOrderPairing.relation_l Q x y ↔ f x = f y))
    (hR : ∀ x y, mem_l x D → mem_l y D →
      (SecondOrderPairing.relation_l R x y ↔ SecondOrderSourceSatisfaction.member_l 𝒩 (f x) (f y)))
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ) :
    ∃ l c, valid_l E c l ∧ represents_l f η E D c ∧ ∀ φ : Formula ℒ Γ Δ,
      SecondOrderPairing.relation_l T (SecondOrderFormulaCompilation.formula_l ℳ φ) (SecondOrderPairing.value_l l c) ↔
        Formula.satisfies η φ := by
  obtain ⟨l, c, hc, hη⟩ := exists_l hℳ hE D f hS η
  exact ⟨l, c, hc, hη, fun φ => SecondOrderSourceSatisfaction.formula_l hℳ hE D Q R T hT f hS hQ hR φ η l c hc hη⟩

/-- 同一内部幂图与求值关系同时服务于全部有限源上下文及其环境。 -/
theorem model_l (hℳ : Theory.Models ℳ theory_m) (D Q R : set_l ℳ) (f : num_l ℳ → 𝒩.Carrier .set)
    (hS : ∀ y, ∃ x, mem_l x D ∧ f x = y)
    (hQ : ∀ x y, mem_l x D → mem_l y D → (SecondOrderPairing.relation_l Q x y ↔ f x = f y))
    (hR : ∀ x y, mem_l x D → mem_l y D →
      (SecondOrderPairing.relation_l R x y ↔ SecondOrderSourceSatisfaction.member_l 𝒩 (f x) (f y))) :
    ∃ E T, SecondOrderBinaryPowers.spec_l E ∧ SecondOrderEvaluationEquations.spec_l E D Q R T ∧
      ∀ (Γ Δ : SortContext ℒ) (η : Env 𝒩 Γ Δ), ∃ l c, valid_l E c l ∧ represents_l f η E D c ∧
        ∀ φ : Formula ℒ Γ Δ,
          SecondOrderPairing.relation_l T (SecondOrderFormulaCompilation.formula_l ℳ φ) (SecondOrderPairing.value_l l c) ↔
            Formula.satisfies η φ := by
  obtain ⟨E, hE⟩ := SecondOrderBinaryPowers.exists_l hℳ
  obtain ⟨T, hT, _⟩ := SecondOrderEvaluationFixedPoint.exists_l hℳ E D Q R
  exact ⟨E, T, hE, hT, fun _ _ η => satisfaction_l hℳ hE D Q R T hT f hS hQ hR η⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSourceAssignment
