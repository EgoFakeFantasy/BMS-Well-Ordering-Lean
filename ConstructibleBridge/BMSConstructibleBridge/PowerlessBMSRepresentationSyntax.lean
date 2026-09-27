import BMSConstructibleBridge.PowerlessBMSRepresentation
import BMSConstructibleBridge.PowerlessNumeralFormula

/-!
# 原标签表示的纯公式部件

原宽度、全部好标签、严格序和指定行的稳定层均保留实际参数。
这些部件供后续完整表示公式及模型内失败最小化使用，不代替展开保持证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSRepresentationSyntax

open Logic FirstOrder ThirdOrderSemantics PowerlessArithmeticTerms

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessArithmetic.structure_l

universe u

def width_m {Γ Δ : SortContext ℒ} (ω e x q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let τ : assignment_m [.num, .num] Γ Δ := fun v => match v with
    | .here => x
    | .there .here => q
  PowerlessArithmeticTranslation.formula_m ω e
    (fun {s} (v : Variable ([] : SortContext SecondOrderSyntax.signature_m) s) => nomatch v) τ
    (PrimitiveProgram.form_m SecondOrderProgramLength.length_m (.fvar .here) (.fvar (.there .here)))

def labels_m {Γ Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ c N f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (s : Term ℒ Γ Δ .set) :=
    (s.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .forallE .set (.forallE .set (.imp
    (SecondOrderObjectSyntax.value_m (w f) (.bvar (.there .here)) (.bvar .here))
    (PowerlessCodedDiagram.good_m (w ω) (w e) (w T) (w t₁) (w t₂) (w t₃) (w c) (w N) (.bvar .here))))

def order_m {Γ Δ : SortContext ℒ} (f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let g := (((f.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound
    SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .forallE .set (.forallE .set (.forallE .set (.forallE .set
    (.imp (SecondOrderObjectSyntax.member_m (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here))))
      (.imp (SecondOrderObjectSyntax.value_m g (.bvar (.there (.there (.there .here)))) (.bvar (.there .here)))
        (.imp (SecondOrderObjectSyntax.value_m g (.bvar (.there (.there .here))) (.bvar .here))
          (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (.bvar .here))))))))

def stable_m {Γ Δ : SortContext ℒ} (k : Nat)
    (ω e T t₁ t₂ t₃ a b : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (s : Term ℒ Γ Δ .set) := s.weakenBound SetTheory.SetSort.set
  .existsE .set (.conj
    (PowerlessNumeral.numeral_m k (w e) (.bvar .here))
    (PowerlessStageStability.stable_m (w ω) (w e) (w T) (w t₁) (w t₂) (w t₃) (.bvar .here) (w a) (w b)))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem labels_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ c N f : Term ℒ Γ Δ .set) :
    (labels_m ω e T t₁ t₂ t₃ c N f).satisfies η ↔
      ∀ i a, value_l (f.eval η) i a → PowerlessCodedDiagram.good_l
        (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (c.eval η) (N.eval η) a := by
  simp only [labels_m, Formula.satisfies, value_formula_l,
    PowerlessCodedDiagram.good_formula_l hℳ, Term.eval_weakenBound]
  rfl

theorem order_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (f : Term ℒ Γ Δ .set) :
    (order_m f).satisfies η ↔ PowerlessConcatenation.increasing_l (f.eval η) := by
  simp only [order_m, Formula.satisfies, value_formula_l, SecondOrderObjectSyntax.member_m,
    Arguments.eval, Term.eval_weakenBound]
  rfl

theorem stable_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (k : Nat) (ω e T t₁ t₂ t₃ a b : Term ℒ Γ Δ .set) :
    (stable_m k ω e T t₁ t₂ t₃ a b).satisfies η ↔
      ∃ m, PowerlessNumeral.numeral_l (e.eval η) k m ∧
        PowerlessStageStability.stable_l (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η)
          (t₃.eval η) m (a.eval η) (b.eval η) := by
  simp only [stable_m, Formula.satisfies, PowerlessNumeral.formula_l,
    PowerlessStageStability.stable_formula_l hℳ, Term.eval_weakenBound]
  rfl

variable {ω e : carrier_l ℳ} {he : PowerlessNatural.zero_l e} {h₀ : member_l ℳ e ω}
  {F : PowerlessArithmetic.operations_l ω e}

local notation "𝒩" => PowerlessArithmetic.structure_l he h₀ F

theorem width_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (w z a b : Term ℒ Γ Δ .set)
    (x q : PowerlessArithmetic.num_l ω) (hw : w.eval η = ω) (hz : z.eval η = e)
    (ha : a.eval η = x.val) (hb : b.eval η = q.val) :
    (width_m w z a b).satisfies η ↔ PowerlessBMSRepresentation.width_l (he := he) (h₀ := h₀) (F := F) x q := by
  let ξ : Env 𝒩 [] [.num, .num] :=
    (((Env.empty (M := 𝒩)).pushFree (σ := SecondOrderSyntax.signature_m) (sort := .num) q).pushFree
      (σ := SecondOrderSyntax.signature_m) (sort := .num) x)
  let τ : assignment_m [.num, .num] Γ Δ := fun v => match v with
    | .here => a
    | .there .here => b
  have hτ : agrees_l η τ ξ.freeVal := by
    intro s v
    match s, v with
    | .num, .here => exact ha
    | .num, .there .here => exact hb
  exact PowerlessArithmeticTranslation.formula_l hℳ hω ξ η w z
    (fun v => nomatch v) τ hw hz (fun v => nomatch v) hτ
    (PrimitiveProgram.form_m SecondOrderProgramLength.length_m (.fvar .here) (.fvar (.there .here)))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSRepresentationSyntax
