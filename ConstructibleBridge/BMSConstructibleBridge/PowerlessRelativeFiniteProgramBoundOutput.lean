import BMSConstructibleBridge.PowerlessRelativeFiniteProgramDomain
import BMSConstructibleBridge.PowerlessSourceRebinding

/-! # 带绑定参数的原程序输出矩阵

解码所得程序词、长度和坐标可以是绑定变量。开放它们只增加原
公式的参数槽，不改变二元算子；语义读数仍是原算子与实际内部历史。
所有转换使用原 AST，不抽取 Type 见证。有效坐标的真实执行另有存在证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramBoundOutput

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_l parameters_empty_l)
open PowerlessRelativeFiniteProgramInstruction (functional_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

def prefix_m {Δ : SortContext ℒ} (n : Nat) (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [] (.set :: .set :: (List.replicate n .set ++ Δ)) :=
  match n with
  | 0 => φ
  | n + 1 => PowerlessDefinableFiniteTrace.lift_m (prefix_m n φ)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem prefix_formula_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 Γ Δ) (x y : type_l hℳ) :
    (prefix_m Γ.length φ).satisfies
      (((PowerlessSourceOpening.env_l η).pushFree x).pushFree y) ↔
        φ.satisfies (((parameters_l η).pushFree x).pushFree y) := by
  induction Γ with
  | nil =>
    have hη : PowerlessSourceOpening.env_l η = parameters_l η := by
      apply Env.ext
      · intro s v; nomatch v
      · intro s v; rfl
    change φ.satisfies (((PowerlessSourceOpening.env_l η).pushFree x).pushFree y) ↔ _
    rw [hη]
  | cons s Γ ih =>
    cases s
    change (PowerlessDefinableFiniteTrace.lift_m (prefix_m Γ.length φ)).satisfies
      ((((PowerlessSourceOpening.env_l (PowerlessSourceOpening.tail_l η)).pushFree
        (η.boundVal .here)).pushFree x).pushFree y) ↔ _
    rw [PowerlessDefinableFiniteTrace.lift_formula_l]
    exact ih (PowerlessSourceOpening.tail_l η)

def step_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w e t₀ t₁ t₂ : Term ℒ Γ Δ .set) :
    Formula ℒ [] (.set :: .set :: (List.replicate Γ.length .set ++ Δ)) :=
  let t := @PowerlessSourceRebinding.term_m Γ Δ
  PowerlessRelativeFiniteProgramExecution.relation_m (prefix_m Γ.length φ)
    (t B) (t C) (t ω) (t w) (t e) (t t₀) (t t₁) (t t₂)

theorem step_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B C ω w e t₀ t₁ t₂ : Term ℒ Γ Δ .set) (x y : type_l hℳ) :
    (step_m φ B C ω w e t₀ t₁ t₂).satisfies
      (((PowerlessSourceOpening.env_l η).pushFree x).pushFree y) ↔
      PowerlessRelativeFiniteProgramStep.step_l φ (parameters_l η)
        (B.eval η) (C.eval η) (ω.eval η) (w.eval η) (e.eval η)
          (t₀.eval η) (t₁.eval η) (t₂.eval η) x y := by
  simp only [step_m, PowerlessRelativeFiniteProgramExecution.relation_formula_l K,
    PowerlessSourceRebinding.term_l, PowerlessRelativeFiniteProgramStep.step_l,
    PowerlessRelativeFiniteProgramStep.good_l, PowerlessRelativeFiniteProgramStore.store_l,
    PowerlessRelativeFiniteProgramInstruction.computed_l,
    PowerlessRelativeFiniteProgramInstruction.good_l, prefix_formula_l]

def run_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (B C ω w e t₀ t₁ t₂ a n k y : type_l hℳ) : Prop :=
  ∃ S D F s E g, PowerlessRelativeClassCorrespondence.member_l hℳ B D ∧
    PowerlessRelativeClassCorrespondence.member_l hℳ B F ∧
      (PowerlessNatural.successor_l (ℳ := 𝒱) n S ∧ map_l (ℳ := 𝒱) F S D ∧
        value_l (ℳ := 𝒱) F e a ∧ ∀ i j x z, mem_l hℳ i n →
          PowerlessNatural.successor_l (ℳ := 𝒱) i j → value_l (ℳ := 𝒱) F i x →
            value_l (ℳ := 𝒱) F j z →
              PowerlessRelativeFiniteProgramStep.step_l φ η B C ω w e t₀ t₁ t₂ x z) ∧
      value_l (ℳ := 𝒱) F n s ∧ PowerlessRelativeFiniteProgramStep.valid_l B ω n E g s ∧
        value_l (ℳ := 𝒱) g k y

/-- 开放固定绑定参数保持完整执行历史，包括每一步的存储与算子读数。 -/
theorem prefix_run_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 Γ Δ) (B C ω w e t₀ t₁ t₂ a n k y : type_l hℳ) :
    run_l (prefix_m Γ.length φ) (PowerlessSourceOpening.env_l η)
      B C ω w e t₀ t₁ t₂ a n k y ↔
        run_l φ (parameters_l η) B C ω w e t₀ t₁ t₂ a n k y := by
  simp only [run_l, PowerlessRelativeFiniteProgramStep.step_l,
    PowerlessRelativeFiniteProgramStep.good_l, PowerlessRelativeFiniteProgramStore.store_l,
    PowerlessRelativeFiniteProgramInstruction.computed_l,
    PowerlessRelativeFiniteProgramInstruction.good_l, prefix_formula_l]

def output_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (B C ω w e t₀ t₁ t₂ a n k y : type_l hℳ) : Prop :=
  PowerlessRelativeClassCorrespondence.member_l hℳ B y ∧
    (run_l φ η B C ω w e t₀ t₁ t₂ a n k y ∨
      ((¬∃ z, run_l φ η B C ω w e t₀ t₁ t₂ a n k z) ∧ y = B))

def output_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w e t₀ t₁ t₂ a n k y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let t := @PowerlessSourceRebinding.term_m Γ Δ
  PowerlessSourceRebinding.formula_m <|
    PowerlessRelativeFiniteProgramOutput.output_m (step_m φ B C ω w e t₀ t₁ t₂)
      (t B) (t ω) (t e) (t a) (t n) (t k) (t y)

theorem run_open_l {Γ Δ : SortContext ℒ} (K : source_coding_l hℳ)
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B C ω w e t₀ t₁ t₂ a n k : Term ℒ Γ Δ .set) (y : type_l hℳ) :
    PowerlessRelativeFiniteProgramOutput.run_l (step_m φ B C ω w e t₀ t₁ t₂)
      (PowerlessSourceOpening.env_l η) (B.eval η) (ω.eval η) (e.eval η)
        (a.eval η) (n.eval η) (k.eval η) y ↔
      run_l φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η) (w.eval η)
        (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (n.eval η) (k.eval η) y := by
  simp only [PowerlessRelativeFiniteProgramOutput.run_l, run_l,
    PowerlessDefinableFiniteTrace.trace_l, step_formula_l K]
  rfl

theorem output_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B C ω w e t₀ t₁ t₂ a n k y : Term ℒ Γ Δ .set) :
    (output_m φ B C ω w e t₀ t₁ t₂ a n k y).satisfies η ↔
      output_l φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η) (w.eval η)
        (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (n.eval η) (k.eval η) (y.eval η) := by
  simp only [output_m, PowerlessSourceRebinding.formula_l,
    PowerlessRelativeFiniteProgramOutput.output_formula_l K, parameters_empty_l,
    PowerlessSourceRebinding.term_l, PowerlessRelativeFiniteProgramOutput.output_l,
    output_l, run_open_l K]

theorem result_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B C ω w Q e t₀ t₁ t₂ a n k : Term ℒ Γ Δ .set)
    (hBase : ∀ x, mem_l hℳ x (B.eval η) → ∀ z, mem_l hℳ z x → mem_l hℳ z (B.eval η))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η))
    (hω : SecondOrderOmega.omega_l hℳ (ω.eval η)) (he : ∀ x, ¬mem_l hℳ x (e.eval η))
    (hInitial : PowerlessRelativeFiniteProgramStep.record_l (e.eval η) (e.eval η) (e.eval η) (a.eval η))
    (hw : map_l (ℳ := 𝒱) (w.eval η) (n.eval η) (Q.eval η))
    (hTags : t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η)
    (hFunctional : functional_l φ (parameters_l η) (B.eval η))
    (hn : mem_l hℳ (n.eval η) (ω.eval η)) :
    (∃! y, output_l φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η) (w.eval η)
      (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (n.eval η) (k.eval η) y) ∧
    (mem_l hℳ (k.eval η) (n.eval η) → ∃ y, run_l φ (parameters_l η)
      (B.eval η) (C.eval η) (ω.eval η) (w.eval η) (e.eval η) (t₀.eval η) (t₁.eval η)
        (t₂.eval η) (a.eval η) (n.eval η) (k.eval η) y) := by
  let ξ := PowerlessSourceOpening.env_l η
  let t := @PowerlessSourceRebinding.term_m Γ Δ
  let ψ := step_m φ B C ω w e t₀ t₁ t₂
  have ht (v : Term ℒ Γ Δ .set) : (t v).eval ξ = v.eval η :=
    PowerlessSourceRebinding.term_l v η
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  have heEq : e.eval η = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val :=
    SecondOrderQuotient.ext_l hℳ _ _ (fun x =>
      iff_of_false (he x) (PowerlessBMSQuotientSuccessor.zero_l K x))
  have hUnique : ∀ x y z, ψ.satisfies ((ξ.pushFree x).pushFree y) →
      ψ.satisfies ((ξ.pushFree x).pushFree z) → y = z := by
    intro x y z hy hz
    obtain ⟨v, _, hv⟩ := PowerlessRelativeFiniteProgramStep.exists_unique_l
      φ (parameters_l η) hBase hC hw hTags hFunctional x
    exact (hv y ((step_formula_l K φ η B C ω w e t₀ t₁ t₂ x y).mp hy)).trans
      (hv z ((step_formula_l K φ η B C ω w e t₀ t₁ t₂ x z).mp hz)).symm
  constructor
  · have h := PowerlessRelativeFiniteProgramOutput.output_exists_unique_l K ψ ξ
      (ω := ω.eval η) (a := a.eval η) (k := k.eval η)
      hBase (hωEq ▸ hn) heEq hUnique
    simpa only [ψ, ξ, PowerlessRelativeFiniteProgramOutput.output_l, output_l,
      run_open_l K] using h
  · intro hk
    have hFunctional' : functional_l (prefix_m Γ.length φ) ξ (B.eval η) := by
      simpa only [ξ, functional_l, prefix_formula_l] using hFunctional
    have h := PowerlessRelativeFiniteProgramOutput.run_exists_l K (prefix_m Γ.length φ) ξ
      (t B) (t C) (t ω) (t w) (t n) (t Q) (t e) (t t₀) (t t₁) (t t₂) (t a) (t n) (t k)
      (by simpa only [ht] using hBase) (by simpa only [ht] using hC)
      (by simpa only [ht] using hω) (by simpa only [ht] using he)
      (by simpa only [ht] using hInitial) (by simpa only [ht] using hw)
      (by simpa only [ht] using hTags) (by simpa only [ht] using hFunctional')
      (by simpa only [ht] using hn) (by simpa only [ht] using hk)
    obtain ⟨y, hy⟩ := h
    refine ⟨y, (run_open_l K φ η B C ω w e t₀ t₁ t₂ a n k y).mp ?_⟩
    simpa only [step_m, ξ, t, PowerlessSourceRebinding.term_l] using hy

#print axioms prefix_formula_l
#print axioms output_formula_l
#print axioms result_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramBoundOutput
