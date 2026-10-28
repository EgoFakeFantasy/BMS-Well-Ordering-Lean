import BMSConstructibleBridge.PowerlessRelativeFiniteProgramBoundClosure
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramImageRealization

/-! # 原程序可定义全像的真实闭包

纯隶属语言、原 Z₂。虚拟域仅以原求值公式的存在码定义，不预供全像集合。
种子常量有真实程序代表；B∈C 时，包含全部缺省分支的原全像等于实际
执行像。配对和调用通过原程序拼接产生同一码域中的新代表。
绑定装配参数通过既有 SourceOpening 读取，原算子及其自由参数不替换。
公开终点是原推导核中的对象模式。这里不预称全像、坍缩或阶段界属于 Class。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramVirtualClosure

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeFiniteProgramInstruction (functional_l functional_m tags_m)
open PowerlessRelativeFiniteProgramEvaluation (matrix_m matrix_l matrix_formula_l)
open PowerlessBMSQuotientSubsetImageDerives
  (parameters_l parameters_pushBound_l parameters_empty_l at_m at_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)
private abbrev up₄ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up₂ (up₂ t)
private abbrev up₆ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up₂ (up₄ t)

def image_m {Γ Δ : SortContext ℒ} (actual : Bool)
    (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a P x : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists P <|
    matrix_m actual φ (up B) (up C) (up ω) (up Q) (up e)
      (up t₀) (up t₁) (up t₂) (up a) (.bvar .here) (up x)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def image_l {Δ : SortContext ℒ} (actual : Bool)
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B C ω Q e t₀ t₁ t₂ a P x : type_l hℳ) : Prop :=
  ∃ p, mem_l hℳ p P ∧ matrix_l actual φ η B C ω Q e t₀ t₁ t₂ a p x

/-- 原总化正文已含 Class 守卫，不额外假设输出属于相对类。 -/
theorem class_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {B C ω Q e t₀ t₁ t₂ a P x : type_l hℳ}
    (h : image_l false φ η B C ω Q e t₀ t₁ t₂ a P x) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B x := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hx, _⟩ := h
  exact hx

theorem image_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (actual : Bool) (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B C ω Q e t₀ t₁ t₂ a P x : Term ℒ Γ Δ .set) :
    (image_m actual φ B C ω Q e t₀ t₁ t₂ a P x).satisfies η ↔
      image_l actual φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η)
        (Q.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (P.eval η) (x.eval η) := by
  simp only [image_m, image_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, matrix_formula_l K, parameters_pushBound_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here]
  rfl

/-- 开放绑定槽保持整张原求值图，包括无执行时的缺省分支。 -/
theorem prefix_matrix_l {Γ Δ : SortContext ℒ} (actual : Bool)
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B C ω Q e t₀ t₁ t₂ a p y : type_l hℳ) :
    matrix_l actual (PowerlessRelativeFiniteProgramBoundOutput.prefix_m Γ.length φ)
      (PowerlessSourceOpening.env_l η) B C ω Q e t₀ t₁ t₂ a p y ↔
        matrix_l actual φ (parameters_l η) B C ω Q e t₀ t₁ t₂ a p y := by
  cases actual <;> simp only [matrix_l, Bool.false_eq_true, if_false, if_true,
    PowerlessRelativeFiniteProgramBoundOutput.output_l,
    PowerlessRelativeFiniteProgramBoundOutput.prefix_run_l]

section Program

include hℳ

variable (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
  (φ : Formula ℒ [] (.set :: .set :: Δ))
  (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ)
  (B C ω Q e t₀ t₁ t₂ a S P : Term ℒ Γ Δ .set)
  (hB : ∀ u, mem_l hℳ u (B.eval η) → ∀ v, mem_l hℳ v u → mem_l hℳ v (B.eval η))
  (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η))
  (hω : SecondOrderOmega.omega_l hℳ (ω.eval η))
  (hωC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (ω.eval η))
  (hQ : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (Q.eval η))
  (he : ∀ u, ¬mem_l hℳ u (e.eval η))
  (ha : PowerlessRelativeFiniteProgramStep.record_l (e.eval η) (e.eval η) (e.eval η) (a.eval η))
  (ht : t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η)
  (hφ : functional_l φ (parameters_l η) (B.eval η))
  (hAlphabet : ∀ q, mem_l hℳ q (Q.eval η) ↔
    PowerlessRelativeFiniteProgramAlphabet.instruction_l (C.eval η) (ω.eval η)
      (t₀.eval η) (t₁.eval η) (t₂.eval η) q)
  (hDomain : PowerlessRelativeFiniteProgramDomain.domain_l
    (B.eval η) (ω.eval η) (Q.eval η) (S.eval η) (P.eval η))

local notation "I₀" => image_l false φ (parameters_l η) (B.eval η) (C.eval η)
  (ω.eval η) (Q.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (P.eval η)
local notation "I₁" => image_l true φ (parameters_l η) (B.eval η) (C.eval η)
  (ω.eval η) (Q.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (P.eval η)

include K hB hC hω hQ he ha ht hφ hAlphabet hDomain in
/-- 同一码域中的种子常量代表；绑定槽不成为新的算子参数。 -/
theorem constant_l (y : Term ℒ Γ Δ .set) (hy : mem_l hℳ (y.eval η) (C.eval η)) :
    I₁ (y.eval η) := by
  let ξ := PowerlessSourceOpening.env_l η
  let t := @PowerlessSourceRebinding.term_m Γ Δ
  have hu (v : Term ℒ Γ Δ .set) : (t v).eval ξ = v.eval η :=
    PowerlessSourceRebinding.term_l v η
  obtain ⟨p, hp, hRun⟩ := PowerlessRelativeFiniteProgramImageRealization.constant_l K
    (PowerlessRelativeFiniteProgramBoundOutput.prefix_m Γ.length φ) ξ
    (t B) (t C) (t ω) (t Q) (t e) (t t₀) (t t₁) (t t₂) (t a) (t S) (t P) (t y)
    (by simpa only [hu] using hB) (by simpa only [hu] using hC)
    (by simpa only [hu] using hω) (by simpa only [hu] using he)
    (by simpa only [hu] using ha) (by simpa only [hu] using hQ)
    (by simpa only [hu] using ht)
    (by simpa only [functional_l, ξ, hu,
      PowerlessRelativeFiniteProgramBoundOutput.prefix_formula_l] using hφ)
    (by simpa only [hu] using hAlphabet) (by simpa only [hu] using hDomain)
    (by simpa only [hu] using hy)
  exact ⟨p, (by simpa only [hu] using hp),
    (by simpa only [hu, ξ, prefix_matrix_l] using hRun)⟩

include hB in
theorem actual_l (x : type_l hℳ) (hx : I₁ x) : I₀ x := by
  obtain ⟨p, hp, hRun⟩ := hx
  exact ⟨p, hp, PowerlessRelativeFiniteProgramImageRealization.actual_l φ (parameters_l η) hB hRun⟩

include K hB hC hω hQ he ha ht hφ hAlphabet hDomain in
/-- 缺省值由 B 的真实常量程序代表，不删除原无效代码。 -/
theorem normal_l (hBC : mem_l hℳ (B.eval η) (C.eval η)) (x : type_l hℳ) : I₀ x ↔ I₁ x := by
  have hDefault := constant_l K φ η B C ω Q e t₀ t₁ t₂ a S P
    hB hC hω hQ he ha ht hφ hAlphabet hDomain B hBC
  constructor
  · rintro ⟨p, hp, w, k, n, hCode, hk, hn, hw, _, hOutput⟩
    rcases hOutput with hRun | ⟨_, hEq⟩
    · exact ⟨p, hp, w, k, n, hCode, hk, hn, hw, hRun⟩
    · exact hEq.symm ▸ hDefault
  · exact actual_l φ η B C ω Q e t₀ t₁ t₂ a P hB x

include K hB hC hω hωC hQ he ha ht hφ hAlphabet hDomain in
theorem pair_l (x y : Term ℒ Γ Δ .set) (hx : I₁ (x.eval η)) (hy : I₁ (y.eval η)) :
    ∃ p, I₁ p ∧ ordered_l (ℳ := 𝒱) (x.eval η) (y.eval η) p := by
  obtain ⟨_, _, w, k, n, _, _, hn, hw, hx⟩ := hx
  obtain ⟨_, _, z, l, m, _, _, hm, hz, hy⟩ := hy
  let ξ : Env 𝒱 (.set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ :=
    (((((η.pushBound w).pushBound k).pushBound n).pushBound z).pushBound l).pushBound m
  let ν : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
    .bvar (.there (.there (.there (.there (.there .here)))))
  let κ : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
    .bvar (.there (.there (.there (.there .here))))
  let σ : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
    .bvar (.there (.there (.there .here)))
  let ζ : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
    .bvar (.there (.there .here))
  let ι : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
  let μ : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set := .bvar .here
  have hν : ν.eval ξ = w := rfl
  have hκ : κ.eval ξ = k := rfl
  have hσ : σ.eval ξ = n := rfl
  have hζ : ζ.eval ξ = z := rfl
  have hι : ι.eval ξ = l := rfl
  have hμ : μ.eval ξ = m := rfl
  have hu (t : Term ℒ Γ Δ .set) : (up₆ t).eval ξ = t.eval η := by
    simp only [up₆, up₄, up₂, up, Term.eval_weakenBound, ξ]
  have hParams : parameters_l ξ = parameters_l η := by simp only [ξ, parameters_pushBound_l]
  obtain ⟨N, v, i, p, hxy, hN, hi, _, _, hv, hp⟩ :=
    PowerlessRelativeFiniteProgramBoundClosure.pair_l K φ ξ
      (up₆ B) (up₆ C) (up₆ ω) (up₆ e) (up₆ t₀) (up₆ t₁) (up₆ t₂) (up₆ a)
        σ ν μ ζ (up₆ Q) κ (up₆ x) ι (up₆ y)
      (by simpa only [hu] using hB) (by simpa only [hu] using hC)
      (by simpa only [hu] using hω) (by simpa only [hu] using hωC)
      (by simpa only [hu] using hQ) (by simpa only [hu] using he)
      (by simpa only [hu] using ha) (by simpa only [hu] using ht)
      (by simpa only [hu, hParams] using hφ) (by simpa only [hu] using hAlphabet)
      (by simpa only [hu, hσ] using hn) (by simpa only [hu, hμ] using hm)
      (by simpa only [hu, hν, hσ] using hw) (by simpa only [hu, hζ, hμ] using hz)
      (by simpa only [hu, hParams, hν, hσ, hκ, if_true] using hx)
      (by simpa only [hu, hParams, hζ, hμ, hι, if_true] using hy)
  have hN' : mem_l hℳ N (ω.eval η) := by simpa only [hu] using hN
  have hiω := SecondOrderOmegaTransitive.member_l hℳ hω hN' hi
  have hv' : map_l (ℳ := 𝒱) v N (Q.eval η) := by simpa only [hu] using hv
  have hp' : PowerlessRelativeFiniteProgramBoundOutput.run_l φ (parameters_l η)
      (B.eval η) (C.eval η) (ω.eval η) v (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η)
        (a.eval η) N i p := by simpa only [hu, hParams] using hp
  obtain ⟨q, hq⟩ := SecondOrderPairObjects.ordered_exists_l hℳ v i
  have hqP := (hDomain.2.2.2 q).mpr
    ⟨v, i, (hDomain.2.1 v).mpr ⟨N, hN', hv'⟩, hiω, hq⟩
  exact ⟨p, ⟨q, hqP, v, i, N, hq, hiω, hN', hv', hp'⟩,
    (by simpa only [hu] using hxy)⟩

include K hB hC hω hQ he ha ht hφ hAlphabet hDomain in
theorem call_l (x y : Term ℒ Γ Δ .set) (hx : I₁ (x.eval η))
    (hyC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (y.eval η))
    (hy : φ.satisfies (((parameters_l η).pushFree (x.eval η)).pushFree (y.eval η))) :
    I₁ (y.eval η) := by
  obtain ⟨_, _, w, k, n, _, _, hn, hw, hx⟩ := hx
  have hwC := PowerlessRelativeClassCorrespondence.transitive_l hℳ hB hDomain.1
    ((hDomain.2.1 w).mpr ⟨n, hn, hw⟩)
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  let ξ : Env 𝒱 (.set :: .set :: .set :: Γ) Δ := ((η.pushBound w).pushBound k).pushBound n
  let ν : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
  let κ : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
  let σ : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar .here
  have hν : ν.eval ξ = w := rfl
  have hκ : κ.eval ξ = k := rfl
  have hσ : σ.eval ξ = n := rfl
  have hu (t : Term ℒ Γ Δ .set) : (up₃ t).eval ξ = t.eval η := by
    simp only [up₃, up₂, up, Term.eval_weakenBound, ξ]
  have hParams : parameters_l ξ = parameters_l η := by simp only [ξ, parameters_pushBound_l]
  obtain ⟨N, v, q, _, hAppend, hRun⟩ := PowerlessRelativeFiniteProgramBoundClosure.call_l K φ ξ
    (up₃ B) (up₃ C) (up₃ ω) ν σ (up₃ Q) (up₃ e) (up₃ t₀) (up₃ t₁) (up₃ t₂)
      (up₃ a) κ (up₃ x) (up₃ y)
    (by simpa only [hu] using hB) (by simpa only [hu] using hC)
    (by simpa only [hu] using hωEq) (by simpa only [hu] using he)
    (by simpa only [hu] using ha) (by simpa only [hu, hν] using hwC)
    (by simpa only [hu] using hQ) (by simpa only [hu, hν, hσ] using hw)
    (by simpa only [hu] using ht) (by simpa only [hu, hParams] using hφ)
    (by simpa only [hσ] using (hωEq ▸ hn)) (by simpa only [hu] using hAlphabet)
    (by simpa only [hu, hParams, hν, hσ, hκ, if_true] using hx)
    (by simpa only [hu] using hyC) (by simpa only [hu, hParams] using hy)
  have hAppend' : PowerlessRelativeFiniteProgramWordAppend.append_l
      (B.eval η) w n (Q.eval η) q N v := by simpa only [hu, hν, hσ] using hAppend
  have hRun' : PowerlessRelativeFiniteProgramBoundOutput.run_l φ (parameters_l η)
      (B.eval η) (C.eval η) (ω.eval η) v (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η)
        (a.eval η) N n (y.eval η) := by simpa only [hu, hParams, hσ] using hRun
  -- 后继长度来自内部算术；这里只消去 Prop 中的数码见证。
  obtain ⟨j, hj⟩ := numberCode_surjective_l K ⟨n, hωEq ▸ hn⟩
  have hj' : (numberCode_l K j).val = n := congrArg Subtype.val hj
  have hSuc : PowerlessNatural.successor_l (ℳ := 𝒱) n
      (numberCode_l K (SecondOrderModel.succ_l j)).val :=
    hj' ▸ PowerlessBMSQuotientSuccessor.successor_l K j
  have hN : N = (numberCode_l K (SecondOrderModel.succ_l j)).val :=
    SecondOrderQuotient.ext_l hℳ _ _ (fun z => (hAppend'.2.2.1 z).trans (hSuc z).symm)
  have hNω : mem_l hℳ N (ω.eval η) :=
    hωEq.symm ▸ hN.symm ▸ (numberCode_l K (SecondOrderModel.succ_l j)).property
  obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ v n
  have hv : map_l (ℳ := 𝒱) v N (Q.eval η) := hAppend'.2.2.2.1
  have hpP := (hDomain.2.2.2 p).mpr
    ⟨v, n, (hDomain.2.1 v).mpr ⟨N, hNω, hv⟩, hn, hp⟩
  exact ⟨p, hpP, v, n, N, hp, hn, hNω, hv, hRun'⟩

include K hB hC hω hωC hQ he ha ht hφ hAlphabet hDomain in
theorem closure_l (hBC : mem_l hℳ (B.eval η) (C.eval η)) :
    (∀ x, mem_l hℳ x (C.eval η) → I₀ x) ∧
    (∀ x, I₀ x ↔ I₁ x) ∧
    (∀ x y, I₀ x → I₀ y → ∃ p, I₀ p ∧ ordered_l (ℳ := 𝒱) x y p) ∧
    (∀ x y, I₀ x → PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) y →
      φ.satisfies (((parameters_l η).pushFree x).pushFree y) → I₀ y) := by
  have hNormal := normal_l K φ η B C ω Q e t₀ t₁ t₂ a S P
    hB hC hω hQ he ha ht hφ hAlphabet hDomain hBC
  have hAt (x y : type_l hℳ) :
      (mem_l hℳ x (C.eval η) → I₀ x) ∧
      (I₀ x → I₀ y → ∃ p, I₀ p ∧ ordered_l (ℳ := 𝒱) x y p) ∧
      (I₀ x → PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) y →
        φ.satisfies (((parameters_l η).pushFree x).pushFree y) → I₀ y) := by
    let ξ : Env 𝒱 (.set :: .set :: Γ) Δ := (η.pushBound x).pushBound y
    let X : Term ℒ (.set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let Y : Term ℒ (.set :: .set :: Γ) Δ .set := .bvar .here
    have hX : X.eval ξ = x := rfl
    have hY : Y.eval ξ = y := rfl
    have hu (t : Term ℒ Γ Δ .set) : (up₂ t).eval ξ = t.eval η := by
      simp only [ξ, up₂, up, Term.eval_weakenBound]
    have hParams : parameters_l ξ = parameters_l η := by simp only [ξ, parameters_pushBound_l]
    refine ⟨?_, ?_, ?_⟩
    · intro hx
      have h := constant_l K φ ξ (up₂ B) (up₂ C) (up₂ ω) (up₂ Q) (up₂ e)
        (up₂ t₀) (up₂ t₁) (up₂ t₂) (up₂ a) (up₂ S) (up₂ P)
        (by simpa only [hu] using hB) (by simpa only [hu] using hC)
        (by simpa only [hu] using hω) (by simpa only [hu] using hQ)
        (by simpa only [hu] using he) (by simpa only [hu] using ha)
        (by simpa only [hu] using ht) (by simpa only [hu, hParams] using hφ)
        (by simpa only [hu] using hAlphabet) (by simpa only [hu] using hDomain) X
        (by simpa only [hu, hX] using hx)
      apply (hNormal x).mpr
      simpa only [image_l, hu, hParams, hX] using h
    · intro hx hy
      have h := pair_l K φ ξ (up₂ B) (up₂ C) (up₂ ω) (up₂ Q) (up₂ e)
        (up₂ t₀) (up₂ t₁) (up₂ t₂) (up₂ a) (up₂ S) (up₂ P)
        (by simpa only [hu] using hB) (by simpa only [hu] using hC)
        (by simpa only [hu] using hω) (by simpa only [hu] using hωC)
        (by simpa only [hu] using hQ) (by simpa only [hu] using he)
        (by simpa only [hu] using ha) (by simpa only [hu] using ht)
        (by simpa only [hu, hParams] using hφ) (by simpa only [hu] using hAlphabet)
        (by simpa only [hu] using hDomain) X Y
        (by simpa only [image_l, hu, hParams, hX] using (hNormal x).mp hx)
        (by simpa only [image_l, hu, hParams, hY] using (hNormal y).mp hy)
      have h' : ∃ p, I₁ p ∧ ordered_l (ℳ := 𝒱) x y p := by
        simpa only [image_l, hu, hParams, hX, hY] using h
      obtain ⟨p, hp, hxy⟩ := h'
      exact ⟨p, (hNormal p).mpr hp, hxy⟩
    · intro hx hyC hy
      have h := call_l K φ ξ (up₂ B) (up₂ C) (up₂ ω) (up₂ Q) (up₂ e)
        (up₂ t₀) (up₂ t₁) (up₂ t₂) (up₂ a) (up₂ S) (up₂ P)
        (by simpa only [hu] using hB) (by simpa only [hu] using hC)
        (by simpa only [hu] using hω) (by simpa only [hu] using hQ)
        (by simpa only [hu] using he) (by simpa only [hu] using ha)
        (by simpa only [hu] using ht) (by simpa only [hu, hParams] using hφ)
        (by simpa only [hu] using hAlphabet) (by simpa only [hu] using hDomain) X Y
        (by simpa only [image_l, hu, hParams, hX] using (hNormal x).mp hx)
        (by simpa only [hu, hY] using hyC) (by simpa only [hParams, hX, hY] using hy)
      apply (hNormal y).mpr
      simpa only [image_l, hu, hParams, hY] using h
  exact ⟨fun x => (hAt x x).1, hNormal, fun x y => (hAt x y).2.1, fun x y => (hAt x y).2.2⟩

end Program

def conclusion_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a P : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (.forallE .set <| .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (up C))
      (image_m false φ (up B) (up C) (up ω) (up Q) (up e)
        (up t₀) (up t₁) (up t₂) (up a) (up P) (.bvar .here))) <|
    .conj (.forallE .set <| .iff
      (image_m false φ (up B) (up C) (up ω) (up Q) (up e)
        (up t₀) (up t₁) (up t₂) (up a) (up P) (.bvar .here))
      (image_m true φ (up B) (up C) (up ω) (up Q) (up e)
        (up t₀) (up t₁) (up t₂) (up a) (up P) (.bvar .here))) <|
      .conj (.forallE .set <| .forallE .set <| .imp
        (image_m false φ (up₂ B) (up₂ C) (up₂ ω) (up₂ Q) (up₂ e)
          (up₂ t₀) (up₂ t₁) (up₂ t₂) (up₂ a) (up₂ P) (.bvar (.there .here))) <|
        .imp (image_m false φ (up₂ B) (up₂ C) (up₂ ω) (up₂ Q) (up₂ e)
          (up₂ t₀) (up₂ t₁) (up₂ t₂) (up₂ a) (up₂ P) (.bvar .here)) <|
          .existsE .set <| .conj
            (image_m false φ (up₃ B) (up₃ C) (up₃ ω) (up₃ Q) (up₃ e)
              (up₃ t₀) (up₃ t₁) (up₃ t₂) (up₃ a) (up₃ P) (.bvar .here))
            (SecondOrderObjectSyntax.ordered_m (.bvar (.there (.there .here)))
              (.bvar (.there .here)) (.bvar .here)))
        (.forallE .set <| .forallE .set <| .imp
          (image_m false φ (up₂ B) (up₂ C) (up₂ ω) (up₂ Q) (up₂ e)
            (up₂ t₀) (up₂ t₁) (up₂ t₂) (up₂ a) (up₂ P) (.bvar (.there .here))) <|
          .imp (PowerlessRelativeHierarchySyntax.class_m (up₂ B) (.bvar .here)) <|
            .imp (at_m φ (.bvar (.there .here)) (.bvar .here))
              (image_m false φ (up₂ B) (up₂ C) (up₂ ω) (up₂ Q) (up₂ e)
                (up₂ t₀) (up₂ t₁) (up₂ t₂) (up₂ a) (up₂ P) (.bvar .here)))

theorem conclusion_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B C ω Q e t₀ t₁ t₂ a P : Term ℒ Γ Δ .set) :
    let I (b : Bool) := image_l b φ (parameters_l η) (B.eval η) (C.eval η)
      (ω.eval η) (Q.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (P.eval η)
    (conclusion_m φ B C ω Q e t₀ t₁ t₂ a P).satisfies η ↔
      (∀ x, mem_l hℳ x (C.eval η) → I false x) ∧
      (∀ x, I false x ↔ I true x) ∧
      (∀ x y, I false x → I false y → ∃ p, I false p ∧ ordered_l (ℳ := 𝒱) x y p) ∧
      (∀ x y, I false x → PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) y →
        φ.satisfies (((parameters_l η).pushFree x).pushFree y) → I false y) := by
  simp only [conclusion_m, Formula.satisfies, image_formula_l K,
    PowerlessRelativeHierarchySemantics.class_formula_l K, ordered_formula_l, at_formula_l,
    parameters_pushBound_l, SecondOrderObjectSyntax.member_m, Arguments.eval,
    up₃, up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  rfl

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a S P : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B C) <|
      .imp (SecondOrderOmegaSyntax.omega_m ω) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B ω) <|
          .imp (PowerlessRelativeHierarchySyntax.class_m B Q) <|
            .imp (PowerlessDefinableFiniteTraceDerives.zero_m e) <|
              .imp (PowerlessRelativeFiniteProgramStep.record_m e e e a) <|
                .imp (tags_m t₀ t₁ t₂) <| .imp (functional_m φ B) <|
                  .imp (PowerlessRelativeFiniteProgramAlphabet.alphabet_m C ω t₀ t₁ t₂ Q) <|
                    .imp (PowerlessRelativeFiniteProgramDomain.domain_m B ω Q S P) <|
                      .imp (SecondOrderObjectSyntax.member_m B C)
                        (conclusion_m φ B C ω Q e t₀ t₁ t₂ a P)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a S P : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B C ω Q e t₀ t₁ t₂ a S P)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (B C ω Q e t₀ t₁ t₂ a S P : Term ℒ [] Δ .set) :
    (sentence_m φ B C ω Q e t₀ t₁ t₂ a S P).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, tags_m,
    PowerlessRelativeFiniteProgramInstruction.functional_formula_l K,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderOmegaSyntax.omega_l,
    PowerlessDefinableFiniteTraceDerives.zero_formula_l,
    PowerlessRelativeFiniteProgramStep.record_formula_l,
    PowerlessRelativeFiniteProgramAlphabet.alphabet_formula_l,
    PowerlessRelativeFiniteProgramDomain.domain_formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval, parameters_empty_l]
  intro η hB hC hω hωC hQ he ha ht hφ hAlphabet hDomain hBC
  apply (conclusion_formula_l K φ η B C ω Q e t₀ t₁ t₂ a P).mpr
  simpa only [parameters_empty_l] using closure_l K φ η B C ω Q e t₀ t₁ t₂ a S P
    hB hC hω hωC hQ he ha ht (by simpa only [parameters_empty_l] using hφ)
      hAlphabet hDomain hBC

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a S P : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B C ω Q e t₀ t₁ t₂ a S P)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 φ B C ω Q e t₀ t₁ t₂ a S P)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramVirtualClosure
