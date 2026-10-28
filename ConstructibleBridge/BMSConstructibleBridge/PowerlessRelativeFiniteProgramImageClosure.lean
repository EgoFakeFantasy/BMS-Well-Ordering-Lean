import BMSConstructibleBridge.PowerlessRelativeFiniteProgramBoundClosure
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramImageRealization

/-! # 同一原程序求值像的实际闭包

从精确实际执行像取得成员的原程序代表，构造配对或调用的新程序，
再把其代码放回同一 Seq(Q)×ω。输出仍属于同一个 I，不另造闭包集合。
算子调用保留原 Class 输出守卫；主路线须另证明所用算子输出均合法。
公开终点为原 Z₂ 推导核中的对象闭包句，模型语义只是其证明中间层。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramImageClosure

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeFiniteProgramInstruction (functional_l functional_m tags_m)
open PowerlessRelativeFiniteProgramEvaluation (matrix_l)
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

def pair_m {Γ Δ : SortContext ℒ} (I : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <|
    .imp (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (up₂ I)) <|
      .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (up₂ I)) <|
        .existsE .set <| .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up₃ I))
          (SecondOrderObjectSyntax.ordered_m (.bvar (.there (.there .here)))
            (.bvar (.there .here)) (.bvar .here))

def call_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B I : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <|
    .imp (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (up₂ I)) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m (up₂ B) (.bvar .here)) <|
        .imp (at_m φ (.bvar (.there .here)) (.bvar .here))
          (SecondOrderObjectSyntax.member_m (.bvar .here) (up₂ I))

def closure_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B I : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (pair_m I) (call_m φ B I)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem closure_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ) (B I : Term ℒ Γ Δ .set) :
    (closure_m φ B I).satisfies η ↔
      (∀ x y, mem_l hℳ x (I.eval η) → mem_l hℳ y (I.eval η) →
        ∃ p, mem_l hℳ p (I.eval η) ∧ ordered_l (ℳ := 𝒱) x y p) ∧
      ∀ x y, mem_l hℳ x (I.eval η) →
        PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) y →
          φ.satisfies (((parameters_l η).pushFree x).pushFree y) → mem_l hℳ y (I.eval η) := by
  simp only [closure_m, pair_m, call_m, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.class_formula_l K, ordered_formula_l, at_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, parameters_pushBound_l,
    up₃, up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  rfl

theorem pair_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B C ω Q e t₀ t₁ t₂ a S P x y : Term ℒ Γ Δ .set) (I : type_l hℳ)
    (hB : ∀ u, mem_l hℳ u (B.eval η) → ∀ v, mem_l hℳ v u → mem_l hℳ v (B.eval η))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η))
    (hω : SecondOrderOmega.omega_l hℳ (ω.eval η))
    (hωC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (ω.eval η))
    (hQ : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (Q.eval η))
    (he : ∀ u, ¬mem_l hℳ u (e.eval η))
    (ha : PowerlessRelativeFiniteProgramStep.record_l
      (e.eval η) (e.eval η) (e.eval η) (a.eval η))
    (ht : t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η)
    (hφ : functional_l φ (parameters_l η) (B.eval η))
    (hAlphabet : ∀ q, mem_l hℳ q (Q.eval η) ↔
      PowerlessRelativeFiniteProgramAlphabet.instruction_l (C.eval η) (ω.eval η)
        (t₀.eval η) (t₁.eval η) (t₂.eval η) q)
    (hDomain : PowerlessRelativeFiniteProgramDomain.domain_l
      (B.eval η) (ω.eval η) (Q.eval η) (S.eval η) (P.eval η))
    (hImage : ∀ z, mem_l hℳ z I ↔ ∃ p, mem_l hℳ p (P.eval η) ∧
      matrix_l true φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η) (Q.eval η)
        (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) p z)
    (hx : mem_l hℳ (x.eval η) I) (hy : mem_l hℳ (y.eval η) I) :
    ∃ p, mem_l hℳ p I ∧ ordered_l (ℳ := 𝒱) (x.eval η) (y.eval η) p := by
  obtain ⟨_, _, w, k, n, _, _, hn, hw, hx⟩ := (hImage (x.eval η)).mp hx
  obtain ⟨_, _, z, l, m, _, _, hm, hz, hy⟩ := (hImage (y.eval η)).mp hy
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
  have hParams : parameters_l ξ = parameters_l η := by
    simp only [ξ, parameters_pushBound_l]
  obtain ⟨N, v, i, p, hxy, hN, hi, _, _, hv, hp⟩ :=
    PowerlessRelativeFiniteProgramBoundClosure.pair_l K φ ξ
      (up₆ B) (up₆ C) (up₆ ω) (up₆ e) (up₆ t₀) (up₆ t₁) (up₆ t₂) (up₆ a)
        σ ν μ ζ (up₆ Q) κ (up₆ x) ι (up₆ y)
      (by simpa only [hu] using hB) (by simpa only [hu] using hC)
      (by simpa only [hu] using hω) (by simpa only [hu] using hωC)
      (by simpa only [hu] using hQ) (by simpa only [hu] using he)
      (by simpa only [hu] using ha) (by simpa only [hu] using ht)
      (by simpa only [hu, hParams] using hφ) (by simpa only [hu] using hAlphabet)
      (by simpa only [hu, hσ] using hn)
      (by simpa only [hu, hμ] using hm)
      (by simpa only [hu, hν, hσ] using hw)
      (by simpa only [hu, hζ, hμ] using hz)
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
  refine ⟨p, (hImage p).mpr ⟨q, hqP, v, i, N, hq, hiω, hN', hv', hp'⟩, ?_⟩
  simpa only [hu] using hxy

theorem call_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B C ω Q e t₀ t₁ t₂ a S P x y : Term ℒ Γ Δ .set) (I : type_l hℳ)
    (hB : ∀ u, mem_l hℳ u (B.eval η) → ∀ v, mem_l hℳ v u → mem_l hℳ v (B.eval η))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η))
    (hω : SecondOrderOmega.omega_l hℳ (ω.eval η))
    (hQ : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (Q.eval η))
    (he : ∀ u, ¬mem_l hℳ u (e.eval η))
    (ha : PowerlessRelativeFiniteProgramStep.record_l
      (e.eval η) (e.eval η) (e.eval η) (a.eval η))
    (ht : t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η)
    (hφ : functional_l φ (parameters_l η) (B.eval η))
    (hAlphabet : ∀ q, mem_l hℳ q (Q.eval η) ↔
      PowerlessRelativeFiniteProgramAlphabet.instruction_l (C.eval η) (ω.eval η)
        (t₀.eval η) (t₁.eval η) (t₂.eval η) q)
    (hDomain : PowerlessRelativeFiniteProgramDomain.domain_l
      (B.eval η) (ω.eval η) (Q.eval η) (S.eval η) (P.eval η))
    (hImage : ∀ z, mem_l hℳ z I ↔ ∃ p, mem_l hℳ p (P.eval η) ∧
      matrix_l true φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η) (Q.eval η)
        (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) p z)
    (hx : mem_l hℳ (x.eval η) I)
    (hyC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (y.eval η))
    (hy : φ.satisfies (((parameters_l η).pushFree (x.eval η)).pushFree (y.eval η))) :
    mem_l hℳ (y.eval η) I := by
  obtain ⟨_, _, w, k, n, _, _, hn, hw, hx⟩ := (hImage (x.eval η)).mp hx
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
    (by simpa only [hσ] using (hωEq ▸ hn))
    (by simpa only [hu] using hAlphabet)
    (by simpa only [hu, hParams, hν, hσ, hκ, if_true] using hx)
    (by simpa only [hu] using hyC) (by simpa only [hu, hParams] using hy)
  have hAppend' : PowerlessRelativeFiniteProgramWordAppend.append_l
      (B.eval η) w n (Q.eval η) q N v := by
    simpa only [hu, hν, hσ] using hAppend
  have hRun' : PowerlessRelativeFiniteProgramBoundOutput.run_l φ (parameters_l η)
      (B.eval η) (C.eval η) (ω.eval η) v (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η)
        (a.eval η) N n (y.eval η) := by
    simpa only [hu, hParams, hσ] using hRun
  -- 新长度为内部后继；不以外部自然数归纳替代模型内部算术。
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
  exact (hImage (y.eval η)).mpr ⟨p, hpP, v, n, N, hp, hn, hNω, hv, hRun'⟩

theorem closure_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B C ω Q e t₀ t₁ t₂ a S P : Term ℒ [] Δ .set) (I : type_l hℳ)
    (hB : ∀ u, mem_l hℳ u (B.eval η) → ∀ v, mem_l hℳ v u → mem_l hℳ v (B.eval η))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η))
    (hω : SecondOrderOmega.omega_l hℳ (ω.eval η))
    (hωC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (ω.eval η))
    (hQ : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (Q.eval η))
    (he : ∀ u, ¬mem_l hℳ u (e.eval η))
    (ha : PowerlessRelativeFiniteProgramStep.record_l
      (e.eval η) (e.eval η) (e.eval η) (a.eval η))
    (ht : t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η)
    (hφ : functional_l φ η (B.eval η))
    (hAlphabet : ∀ q, mem_l hℳ q (Q.eval η) ↔
      PowerlessRelativeFiniteProgramAlphabet.instruction_l (C.eval η) (ω.eval η)
        (t₀.eval η) (t₁.eval η) (t₂.eval η) q)
    (hDomain : PowerlessRelativeFiniteProgramDomain.domain_l
      (B.eval η) (ω.eval η) (Q.eval η) (S.eval η) (P.eval η))
    (hImage : ∀ z, mem_l hℳ z I ↔ ∃ p, mem_l hℳ p (P.eval η) ∧
      matrix_l true φ η (B.eval η) (C.eval η) (ω.eval η) (Q.eval η)
        (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) p z) :
    (∀ x y, mem_l hℳ x I → mem_l hℳ y I →
      ∃ p, mem_l hℳ p I ∧ ordered_l (ℳ := 𝒱) x y p) ∧
    (∀ x y, mem_l hℳ x I → PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) y →
      φ.satisfies ((η.pushFree x).pushFree y) → mem_l hℳ y I) := by
  have hAt (x y : type_l hℳ) :
      (mem_l hℳ x I → mem_l hℳ y I →
        ∃ p, mem_l hℳ p I ∧
          ordered_l (ℳ := SecondOrderQuotient.structure_l hℳ) x y p) ∧
      (mem_l hℳ x I →
        PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) y →
          φ.satisfies ((η.pushFree x).pushFree y) → mem_l hℳ y I) := by
    let ξ : Env (SecondOrderQuotient.structure_l hℳ) [.set, .set] Δ := (η.pushBound x).pushBound y
    let X : Term ℒ [.set, .set] Δ .set := .bvar (.there .here)
    let Y : Term ℒ [.set, .set] Δ .set := .bvar .here
    have hX : X.eval ξ = x := rfl
    have hY : Y.eval ξ = y := rfl
    have hu (t : Term ℒ [] Δ .set) : (up₂ t).eval ξ = t.eval η := by
      simp only [ξ, up₂, up, Term.eval_weakenBound]
    have hParams : parameters_l ξ = η := by
      simp only [ξ, parameters_pushBound_l, parameters_empty_l]
    constructor
    · intro hx hy
      have h := pair_l K φ ξ (up₂ B) (up₂ C) (up₂ ω) (up₂ Q) (up₂ e)
        (up₂ t₀) (up₂ t₁) (up₂ t₂) (up₂ a) (up₂ S) (up₂ P) X Y I
        (by simpa only [hu] using hB) (by simpa only [hu] using hC)
        (by simpa only [hu] using hω) (by simpa only [hu] using hωC)
        (by simpa only [hu] using hQ) (by simpa only [hu] using he)
        (by simpa only [hu] using ha) (by simpa only [hu] using ht)
        (by simpa only [hu, hParams] using hφ) (by simpa only [hu] using hAlphabet)
        (by simpa only [hu] using hDomain) (by simpa only [hu, hParams] using hImage) hx hy
      simpa only [hX, hY] using h
    · intro hx hyC hy
      exact call_l K φ ξ (up₂ B) (up₂ C) (up₂ ω) (up₂ Q) (up₂ e)
        (up₂ t₀) (up₂ t₁) (up₂ t₂) (up₂ a) (up₂ S) (up₂ P) X Y I
        (by simpa only [hu] using hB) (by simpa only [hu] using hC)
        (by simpa only [hu] using hω) (by simpa only [hu] using hQ)
        (by simpa only [hu] using he) (by simpa only [hu] using ha)
        (by simpa only [hu] using ht) (by simpa only [hu, hParams] using hφ)
        (by simpa only [hu] using hAlphabet) (by simpa only [hu] using hDomain)
        (by simpa only [hu, hParams] using hImage) hx
        (by simpa only [hu, hY] using hyC)
        (by simpa only [hParams, hX, hY] using hy)
  exact ⟨fun x y => (hAt x y).1, fun x y => (hAt x y).2⟩

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a S P I : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
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
                      .imp (PowerlessRelativeFiniteProgramImageRealization.image_m
                        φ B C ω Q e t₀ t₁ t₂ a P I) (closure_m φ B I)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a S P I : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B C ω Q e t₀ t₁ t₂ a S P I)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a S P I : Term ℒ [] Δ .set) :
    (sentence_m φ B C ω Q e t₀ t₁ t₂ a S P I).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
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
    PowerlessRelativeFiniteProgramImageRealization.image_formula_l K, closure_formula_l K,
    parameters_empty_l]
  intro η hB hC hω hωC hQ he ha ht hφ hAlphabet hDomain hImage
  exact closure_l K φ η B C ω Q e t₀ t₁ t₂ a S P (I.eval η)
    hB hC hω hωC hQ he ha ht hφ hAlphabet hDomain hImage

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a S P I : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B C ω Q e t₀ t₁ t₂ a S P I)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ h𝒩 => models_l h𝒩 φ B C ω Q e t₀ t₁ t₂ a S P I)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramImageClosure
