import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionFamilyWellOrder
import BMSConstructibleBridge.PowerlessSatisfactionDerives

/-! # 完整 Sat 与内部定义子集族良序的共同原 Z₂ 出口

先于所有母集固定同一合法性及构造编码。每个带实际良序的母集再存在
量化完整 Sat、全内部有限赋值集及其精确子集族良序。这同时证明 Sat
存在与族良序，不把给定任意关系的图构造当作完整求值。原五标签 Def
与此四标签表示族之间的全内部码桥仍是独立义务。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSatisfactionFamilyDerives

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassEnumerationWellOrder (wellOrder_m)
open _root_.YesMetaZFC.Automation

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private abbrev up₆ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  up (up (up (up (up (up t)))))

def body_m {Γ Δ : SortContext ℒ} (ω e t₁ t₂ t₃ T N F : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessSatisfactionExistenceSyntax.static_m ω e t₁ t₂ t₃ T N F) <|
    .forallE .set <| .forallE .set <|
      .imp (wellOrder_m (.bvar (.there .here)) (.bvar .here)) <|
        .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <|
          let A : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
            .bvar (.there (.there (.there (.there (.there .here)))))
          let R : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
            .bvar (.there (.there (.there .here)))
          .conj (PowerlessSatisfactionSpecification.spec_m (up₆ ω) A (up₆ e)
            (up₆ t₁) (up₆ t₂) (up₆ t₃) (up₆ T) (up₆ F) R)
            (PowerlessRelativeClassSatisfactionFamilyWellOrder.specification_m (up₆ ω) A (up₆ e) R
              (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))

def body_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e t₁ t₂ t₃ T N F : carrier_l ℳ₀) : Prop :=
  PowerlessSatisfactionExistenceSyntax.static_l ω e t₁ t₂ t₃ T N F ∧ ∀ A P,
    wellOrder_l A P → ∃ R S Y L, PowerlessSatisfactionSpecification.spec_l ω A e t₁ t₂ t₃ T F R ∧
      PowerlessFiniteSequencesSyntax.spec_l ω A S ∧
        PowerlessRelativeClassSatisfactionFamilyWellOrder.family_l ω A S e R Y ∧ wellOrder_l Y L

theorem body_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (ω e t₁ t₂ t₃ T N F : Term ℒ Γ Δ .set) :
    (body_m ω e t₁ t₂ t₃ T N F).satisfies η ↔
      body_l (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
        (T.eval η) (N.eval η) (F.eval η) := by
  simp only [body_m, body_l, Formula.satisfies,
    PowerlessSatisfactionExistenceSyntax.static_formula_l,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    PowerlessSatisfactionSpecification.spec_formula_l,
    PowerlessRelativeClassSatisfactionFamilyWellOrder.specification_formula_l,
    up₆, up, Term.eval_weakenBound, Term.eval]
  rfl

def statement_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω : carrier_l ℳ₀) : Prop :=
  ∃ e t₁ t₂ t₃ T N F, body_l ω e t₁ t₂ t₃ T N F

private abbrev witnesses_m : SortContext ℒ := [.set, .set, .set, .set, .set, .set, .set]

def existence_m {Γ Δ : SortContext ℒ} (ω : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let p (v : Variable witnesses_m .set) : Term ℒ Γ (witnesses_m ++ Δ) .set := PrefixQuantification.entry_m v
  PrefixQuantification.exists_m witnesses_m <|
    body_m (PrefixQuantification.weaken_m witnesses_m ω)
      (p (.there (.there (.there (.there (.there (.there .here)))))))
      (p (.there (.there (.there (.there (.there .here))))))
      (p (.there (.there (.there (.there .here)))))
      (p (.there (.there (.there .here)))) (p (.there (.there .here))) (p (.there .here)) (p .here)

theorem existence_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (ω : Term ℒ Γ Δ .set) :
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

def sentence_m : Sentence ℒ := .forallE .set <|
  .imp (SecondOrderOmegaSyntax.omega_m (.bvar .here)) (existence_m (.bvar .here))

theorem sentence_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} :
    sentence_m.TrueIn ℳ₀ ↔ ∀ ω : carrier_l ℳ₀, omega_l (ℳ := ℳ₀) ω → statement_l ω := by
  simp only [sentence_m, Formula.TrueIn, Formula.satisfies, omega_formula_l, existence_formula_l, Term.eval]
  rfl

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
    {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B} {ω : type_l hℳ B}
    (hω : omega_l (ℳ := structure_l hℳ B hBase) ω) :
    statement_l (ℳ₀ := structure_l hℳ B hBase) ω := by
  obtain ⟨e, t₁, t₂, t₃, T, N, F, hStatic, hDomains⟩ := PowerlessSatisfactionDerives.exists_l hω
  refine ⟨e, t₁, t₂, t₃, T, N, F, hStatic, ?_⟩
  intro A P hP
  obtain ⟨R, hSat⟩ := hDomains A
  obtain ⟨S, Y, L, hS, hFamily, hL⟩ :=
    PowerlessRelativeClassSatisfactionFamilyWellOrder.exists_l hω hP e R
  exact ⟨R, S, Y, L, hSat, hS, hFamily, hL⟩

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    sentence_m.TrueIn (structure_l hℳ B hBase) :=
  sentence_formula_l.mpr (fun _ hω => exists_l hω)

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m _ (fun _ h𝒩 B hBase => models_l h𝒩 B hBase)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSatisfactionFamilyDerives
