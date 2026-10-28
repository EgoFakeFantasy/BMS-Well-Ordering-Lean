import BMSConstructibleBridge.PowerlessFormulaValiditySpecification
import BMSConstructibleBridge.PowerlessSatisfactionSpecification
import BMSConstructibleBridge.PowerlessRelativeClassConstructorTotal
import BMSConstructibleBridge.PowerlessRelativeClassTriangularDerives
import YesMetaZFC.Automation.PrefixQuantification

/-! # 先固定合法性图的公共求值存在句

同一个空集、标签、三角图、有限证书集和合法性图先于所有求值域固定。
每个域只存在量化实际求值关系；编码见证及中间赋值集、求值图不成为对象
参数。此处仅给纯 ℒ 对象句与任意纯结构中的读数，不断言该句已可推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSatisfactionExistenceSyntax

open Logic FirstOrder ThirdOrderSemantics
open _root_.YesMetaZFC.Automation

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def static_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e t₁ t₂ t₃ T N F : carrier_l 𝒩) : Prop :=
  PowerlessEvaluationTags.tags_l e t₁ t₂ t₃ ∧ PowerlessTriangular.triangular_l ω e T ∧
    PowerlessRelativeClassConstructorTotal.functional_l ω e T ∧
      PowerlessFiniteSequencesSyntax.spec_l ω ω N ∧
        PowerlessFormulaValiditySpecification.spec_l ω e N T t₁ t₂ t₃ F

def static_m {Γ Δ : SortContext ℒ} (ω e t₁ t₂ t₃ T N F : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessEvaluationTags.tags_m e t₁ t₂ t₃) <|
    .conj (PowerlessRelativeClassTriangularDerives.body_m ω e T) <|
      .conj (PowerlessRelativeClassConstructorTotal.functional_m ω e T) <|
        .conj (PowerlessFiniteSequencesSyntax.spec_m ω ω N)
          (PowerlessFormulaValiditySpecification.spec_m ω e N T t₁ t₂ t₃ F)

theorem static_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e t₁ t₂ t₃ T N F : Term ℒ Γ Δ .set) :
    (static_m ω e t₁ t₂ t₃ T N F).satisfies η ↔
      static_l (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
        (T.eval η) (N.eval η) (F.eval η) := by
  simp only [static_m, static_l, Formula.satisfies, PowerlessEvaluationTags.tags_formula_l,
    PowerlessRelativeClassTriangularDerives.body_l, PowerlessRelativeClassConstructorTotal.functional_formula_l,
    PowerlessFiniteSequencesSyntax.spec_formula_l, PowerlessFormulaValiditySpecification.spec_formula_l]

/-- 静态参数全部先固定，随后才全称量化求值域。 -/
def body_m {Γ Δ : SortContext ℒ} (ω e t₁ t₂ t₃ T N F : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up t)
  .conj (static_m ω e t₁ t₂ t₃ T N F) <|
    .forallE .set <| .existsE .set <|
      PowerlessSatisfactionSpecification.spec_m (w ω) (.bvar (.there .here)) (w e)
        (w t₁) (w t₂) (w t₃) (w T) (w F) (.bvar .here)

theorem body_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e t₁ t₂ t₃ T N F : Term ℒ Γ Δ .set) :
    (body_m ω e t₁ t₂ t₃ T N F).satisfies η ↔
      static_l (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
        (T.eval η) (N.eval η) (F.eval η) ∧
      ∀ A, ∃ R, PowerlessSatisfactionSpecification.spec_l (ω.eval η) A (e.eval η)
        (t₁.eval η) (t₂.eval η) (t₃.eval η) (T.eval η) (F.eval η) R := by
  simp only [body_m, Formula.satisfies, static_formula_l, PowerlessSatisfactionSpecification.spec_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  rfl

def statement_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω : carrier_l 𝒩) : Prop :=
  ∃ e t₁ t₂ t₃ T N F, static_l ω e t₁ t₂ t₃ T N F ∧
    ∀ A, ∃ R, PowerlessSatisfactionSpecification.spec_l ω A e t₁ t₂ t₃ T F R

/-- 自由槽次序与外层存在量词次序相反：F、N、T、t₃、t₂、t₁、e。 -/
private abbrev witnesses_m : SortContext ℒ := [.set, .set, .set, .set, .set, .set, .set]

def existence_m {Γ Δ : SortContext ℒ} (ω : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let p (v : Variable witnesses_m .set) : Term ℒ Γ (witnesses_m ++ Δ) .set := PrefixQuantification.entry_m v
  PrefixQuantification.exists_m witnesses_m <|
    body_m (PrefixQuantification.weaken_m witnesses_m ω)
      (p (.there (.there (.there (.there (.there (.there .here)))))))
      (p (.there (.there (.there (.there (.there .here))))))
      (p (.there (.there (.there (.there .here)))))
      (p (.there (.there (.there .here)))) (p (.there (.there .here))) (p (.there .here)) (p .here)

theorem existence_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω : Term ℒ Γ Δ .set) :
    (existence_m ω).satisfies η ↔ statement_l (ω.eval η) := by
  rw [existence_m, PrefixQuantification.exists_formula_l]
  constructor
  · rintro ⟨xs, h⟩
    cases xs with
    | cons F xs =>
      cases xs with
      | cons N xs =>
        cases xs with
        | cons T xs =>
          cases xs with
          | cons t₃ xs =>
            cases xs with
            | cons t₂ xs =>
              cases xs with
              | cons t₁ xs =>
                cases xs with
                | cons e xs =>
                  cases xs with
                  | nil =>
                    refine ⟨e, t₁, t₂, t₃, T, N, F, ?_⟩
                    simpa only [body_formula_l, witnesses_m, PrefixQuantification.weaken_m,
                      PrefixQuantification.entry_m, PrefixQuantification.env_l, Term.eval_weakenFree,
                      Term.eval, Env.pushFree_here, Env.pushFree_there] using h
  · rintro ⟨e, t₁, t₂, t₃, T, N, F, h⟩
    refine ⟨.cons F (.cons N (.cons T (.cons t₃ (.cons t₂ (.cons t₁ (.cons e .nil)))))), ?_⟩
    simpa only [body_formula_l, witnesses_m, PrefixQuantification.weaken_m,
      PrefixQuantification.entry_m, PrefixQuantification.env_l, Term.eval_weakenFree,
      Term.eval, Env.pushFree_here, Env.pushFree_there] using h

def sentence_m : Sentence ℒ :=
  .forallE .set <| .imp (SecondOrderOmegaSyntax.omega_m (.bvar .here)) (existence_m (.bvar .here))

theorem sentence_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} :
    sentence_m.TrueIn 𝒩 ↔ ∀ ω : carrier_l 𝒩, omega_l (ℳ := 𝒩) ω → statement_l ω := by
  simp only [sentence_m, Formula.TrueIn, Formula.satisfies, omega_formula_l, existence_formula_l, Term.eval]
  rfl

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSatisfactionExistenceSyntax
