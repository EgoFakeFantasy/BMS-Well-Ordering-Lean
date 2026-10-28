import BMSConstructibleBridge.PowerlessDefinableFiniteTrace
import BMSConstructibleBridge.PowerlessMapBounded
import BMSConstructibleBridge.PowerlessSuccessorBounded
import BMSConstructibleBridge.SecondOrderOmegaSyntax

/-! # 可定义有限历史的有界检查式

历史仍是原模型内部长度的实际干净函数图。后继坐标限制到历史域，
状态限制到历史陪域；双向等价使用原内部自然数后继界，不将模型内
长度误当作宿主有限列表。正文为纯 Δ₀ 时，整个历史检查式也是纯 Δ₀。
这里只检查给定历史，不假定无限图、完整 Collection 或整个求值像。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessDefinableFiniteTraceBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessBMSQuotientSubsetImageDerives
  (at_m at_formula_l parameters_l parameters_pushBound_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₄ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up (up (up t)))

def step_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (n S D f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall n <|
    membershipLevyBound.boundedForall (up S) <|
      membershipLevyBound.boundedForall (up (up D)) <|
        membershipLevyBound.boundedForall (up (up (up D))) <|
          let i : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set :=
            .bvar (.there (.there (.there .here)))
          let j := .bvar (.there (.there .here))
          let x := .bvar (.there .here)
          let y := .bvar .here
          .imp (PowerlessSuccessorBounded.formula_m i j) <|
            .imp (PowerlessValueBounded.formula_m (up₄ f) i x) <|
              .imp (PowerlessValueBounded.formula_m (up₄ f) j y) (at_m φ x y)

def trace_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (e a n S D f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessSuccessorBounded.formula_m n S) <|
    .conj (PowerlessMapBounded.formula_m f S D) <|
      .conj (PowerlessValueBounded.formula_m f e a) (step_m φ n S D f)

private theorem at_delta_l {Γ Δ : SortContext ℒ}
    {φ : Formula ℒ [] (.set :: .set :: Δ)} (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (x y : Term ℒ Γ Δ .set) : Formula.IsDelta0 membershipLevyBound (at_m φ x y) := by
  unfold at_m
  exact Formula.IsDelta0.substituteMapped
    (boundSubstitution := fun {s} (v : Variable ([] : SortContext ℒ) s) => nomatch v)
    (freeSubstitution := _) hφ

theorem step_delta_l {Γ Δ : SortContext ℒ}
    {φ : Formula ℒ [] (.set :: .set :: Δ)} (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (n S D f : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (step_m φ n S D f) :=
  .bounded_forall n <| .bounded_forall (up S) <| .bounded_forall (up (up D)) <|
    .bounded_forall (up (up (up D))) <| .imp (PowerlessSuccessorBounded.delta_l _ _) <|
      .imp (PowerlessValueBounded.delta_l _ _ _) <|
        .imp (PowerlessValueBounded.delta_l _ _ _) (at_delta_l hφ _ _)

theorem trace_delta_l {Γ Δ : SortContext ℒ}
    {φ : Formula ℒ [] (.set :: .set :: Δ)} (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (e a n S D f : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (trace_m φ e a n S D f) :=
  .conj (PowerlessSuccessorBounded.delta_l _ _) <|
    .conj (PowerlessMapBounded.delta_l _ _ _) <|
      .conj (PowerlessValueBounded.delta_l _ _ _) (step_delta_l hφ _ _ _ _)

def trace_l {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (e a n S D f : carrier_l 𝒱) : Prop :=
  PowerlessNatural.successor_l n S ∧ map_l f S D ∧ value_l f e a ∧
    ∀ i, member_l 𝒱 i n → ∀ j, member_l 𝒱 j S →
      ∀ x, member_l 𝒱 x D → ∀ y, member_l 𝒱 y D →
        PowerlessNatural.successor_l i j → value_l f i x → value_l f j y →
          φ.satisfies ((η.pushFree x).pushFree y)

theorem trace_formula_l {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (e a n S D f : Term ℒ Γ Δ .set) :
    (trace_m φ e a n S D f).satisfies η ↔
      trace_l φ (parameters_l η) (e.eval η) (a.eval η) (n.eval η)
        (S.eval η) (D.eval η) (f.eval η) := by
  simp only [trace_m, step_m, trace_l, Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessSuccessorBounded.formula_l, PowerlessMapBounded.formula_l,
    PowerlessValueBounded.formula_l, at_formula_l, parameters_pushBound_l,
    Arguments.eval, up₄, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem equiv_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    {e a n S D f : type_l hℳ} (hn : mem_l hℳ n K.omega) :
    trace_l φ η e a n S D f ↔ PowerlessDefinableFiniteTrace.trace_l φ η e a n S D f := by
  constructor
  · rintro ⟨hS, hf, h₀, hStep⟩
    refine ⟨hS, hf, h₀, ?_⟩
    intro i j x y hi hij hx hy
    exact hStep i hi j (PowerlessDefinableFiniteTrace.step_bound_l K hn hi hij hS)
      x (SecondOrderFunctionProperties.value_mem_l hℳ hf hx).2
      y (SecondOrderFunctionProperties.value_mem_l hℳ hf hy).2 hij hx hy
  · rintro ⟨hS, hf, h₀, hStep⟩
    exact ⟨hS, hf, h₀, fun i hi j _ x _ y _ hij hx hy => hStep i j x y hi hij hx hy⟩

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω e a n S D f : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .imp (SecondOrderObjectSyntax.member_m n ω) <|
      .iff (trace_m φ e a n S D f) (PowerlessDefinableFiniteTrace.trace_m φ e a n S D f)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω e a n S D f : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ ω e a n S D f)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (ω e a n S D f : Term ℒ [] Δ .set) :
    (sentence_m φ ω e a n S D f).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, SecondOrderOmegaSyntax.omega_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, trace_formula_l,
    PowerlessDefinableFiniteTrace.trace_formula_l]
  intro η hω hn
  have hωEq := SecondOrderOmega.unique_l h𝒩 hω K.omega_spec
  exact equiv_l K φ (parameters_l η) (hωEq ▸ hn)

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω e a n S D f : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ ω e a n S D f)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 φ ω e a n S D f)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessDefinableFiniteTraceBounded
