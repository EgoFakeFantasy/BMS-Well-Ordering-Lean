import BMSConstructibleBridge.PowerlessRelativeGlobalCanonicalOrder
import BMSConstructibleBridge.PowerlessBMSQuotientSubsetImageDerives
import BMSConstructibleBridge.PowerlessBoundContextClosure

/-! # 全局规范最小元模式的原 Z₂ 对象推导

每个外部有限原矩阵实例提供实际纯句及原 Derives 出口。固定编码包
先于全部基底取得，并同时保留原规范序总性／相容性证书；非空的可定义
Class 子类有唯一最小元。不假定该子类为 Class 集合，不声称其任意
集合族已有 Class 选择图，亦不替代有限闭包、凝聚或最终 BMS 定理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeGlobalLeastDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeGlobalCanonicalOrder (edge_m edge_l edge_formula_l)
open PowerlessBMSQuotientSubsetImageDerives
  (parameters_l parameters_pushBound_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)

private def insert_m {Γ Δ : SortContext ℒ} (y : Term ℒ Γ Δ .set) :
    VariableSubstitution ℒ (.set :: Δ) Γ Δ
  | _, .here => y
  | _, .there v => .fvar v

def at_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  φ.substitute (show Substitution ℒ [] (.set :: Δ) Γ Δ from
    .map (fun v => nomatch v) (insert_m y))

theorem at_formula_l {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) (η : Env 𝒱 Γ Δ) (y : Term ℒ Γ Δ .set) :
    (at_m φ y).satisfies η ↔ φ.satisfies ((parameters_l η).pushFree (y.eval η)) := by
  refine (Formula.satisfies_substitute η _ φ).trans ?_
  apply Iff.of_eq
  apply congrArg (fun η => φ.satisfies η)
  apply Env.ext
  · intro s v
    nomatch v
  · intro s v
    cases v <;> rfl

def least_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (ω e t₁ t₂ t₃ Pair Valid B P₀ y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessRelativeHierarchySyntax.class_m B y) <|
    .conj (at_m φ y) <| .forallE .set <|
      .imp (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here)) <|
        .imp (at_m φ (.bvar .here)) <|
          .neg (edge_m (up ω) (up e) (up t₁) (up t₂) (up t₃) (up Pair)
            (up Valid) (up B) (up P₀) (.bvar .here) (up y))

def property_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (ω e t₁ t₂ t₃ Pair Valid : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <|
    let B : Term ℒ (.set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let P₀ := .bvar .here
    .imp (SecondOrderCanonicalLevelDerives.guard_m B P₀) <|
      .imp (.existsE .set <|
        .conj (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here))
          (at_m φ (.bvar .here))) <|
        .existsE .set <|
          let y : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar .here
          let w (t : Term ℒ Γ Δ .set) := up (up₂ t)
          .conj (least_m φ (w ω) (w e) (w t₁) (w t₂) (w t₃) (w Pair)
            (w Valid) (up B) (up P₀) y) <|
            .forallE .set <|
              .imp (least_m φ (up (w ω)) (up (w e)) (up (w t₁)) (up (w t₂))
                (up (w t₃)) (up (w Pair)) (up (w Valid)) (up₂ B) (up₂ P₀) (.bvar .here))
                (.equal (.bvar .here) (up y))

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) : Sentence ℒ :=
  .forallE .set <| .imp (SecondOrderOmegaSyntax.omega_m (.bvar .here)) <|
    .existsE .set <| .existsE .set <| .existsE .set <|
      .existsE .set <| .existsE .set <| .existsE .set <|
        let ω : Term ℒ [.set, .set, .set, .set, .set, .set, .set] Δ .set :=
          .bvar (.there (.there (.there (.there (.there (.there .here))))))
        let e := .bvar (.there (.there (.there (.there (.there .here)))))
        let t₁ := .bvar (.there (.there (.there (.there .here))))
        let t₂ := .bvar (.there (.there (.there .here)))
        let t₃ := .bvar (.there (.there .here))
        let Pair := .bvar (.there .here)
        let Valid := .bvar .here
        PowerlessBoundContextClosure.formula_m <|
          .conj (SecondOrderCanonicalLevelDerives.mode_m ω e t₁ t₂ t₃ Pair Valid)
            (property_m φ ω e t₁ t₂ t₃ Pair Valid)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) : Sentence ℒ :=
  schema_m φ

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem least_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) (η : Env 𝒱 Γ Δ)
    (ω e t₁ t₂ t₃ Pair Valid B P₀ y : Term ℒ Γ Δ .set) :
    (least_m φ ω e t₁ t₂ t₃ Pair Valid B P₀ y).satisfies η ↔
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (y.eval η) ∧
        φ.satisfies ((parameters_l η).pushFree (y.eval η)) ∧
        ∀ z, PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) z →
          φ.satisfies ((parameters_l η).pushFree z) →
            ¬edge_l (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
              (Pair.eval η) (Valid.eval η) (B.eval η) (P₀.eval η) z (y.eval η) := by
  simp only [least_m, Formula.satisfies, PowerlessRelativeHierarchySemantics.class_formula_l K,
    at_formula_l, edge_formula_l K, parameters_pushBound_l, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here]
  rfl

set_option maxHeartbeats 1000000 in
theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) : (sentence_m φ).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K₀⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  simp only [sentence_m, schema_m, Formula.TrueIn, Formula.satisfies,
    omega_formula_l, Term.eval, Env.pushBound_bound_here]
  intro ω hω
  obtain ⟨K, e, t₁, t₂, t₃, Pair, Valid, hωEq, he, hCoding⟩ :=
    SecondOrderComparisonCoding.exists_l hω
  refine ⟨e, t₁, t₂, t₃, Pair, Valid, ?_⟩
  apply (PowerlessBoundContextClosure.formula_l _ _).mpr
  intro ρ
  let η : Env (SecondOrderQuotient.structure_l h𝒩) [] Δ := ⟨Assignment.empty, ρ⟩
  constructor
  · simp only [SecondOrderCanonicalLevelDerives.mode_m, Formula.satisfies,
      SecondOrderCanonicalLevelDerives.guard_formula_l,
      SecondOrderCanonicalLevelDerives.totality_formula_l K₀,
      SecondOrderCanonicalLevelDerives.coherence_formula_l K₀,
      Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
    intro B P₀ hSeed
    rw [hωEq, he]
    constructor
    · intro a X hX
      obtain ⟨P, hP, hUnique⟩ := SecondOrderCanonicalLevel.exists_unique_l K hCoding
        hSeed.1 (fun x hx y hy => hSeed.2.1 x y hx hy) hSeed.2.2.1 hSeed.2.2.2 hX
      exact ⟨P, hP, SecondOrderCanonicalLevel.order_l hP, hUnique⟩
    · intro a X P b Y Q hab hP hQ
      exact SecondOrderCanonicalLevel.extension_l K hCoding hab hP hQ
  · simp only [property_m, Formula.satisfies, SecondOrderCanonicalLevelDerives.guard_formula_l,
      PowerlessRelativeHierarchySemantics.class_formula_l K₀, at_formula_l,
      least_formula_l K₀, parameters_pushBound_l,
      up₂, up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
    intro B P₀ hSeed hSome
    rw [hωEq, he]
    exact PowerlessRelativeGlobalCanonicalOrder.least_l K hCoding hSeed φ η hSome

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 φ)

#print axioms at_formula_l
#print axioms least_formula_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeGlobalLeastDerives
