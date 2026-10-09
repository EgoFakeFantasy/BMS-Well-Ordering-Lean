import BMSConstructibleBridge.PowerlessRelativeCutoffCoveredCondensation
import BMSConstructibleBridge.PowerlessRelativeCoveredCondensation
import BMSConstructibleBridge.PowerlessRelativeDefSeparation

/-! # 实际完整覆盖壳给出的首截断层分离

原 Z₂、原纯隶属公式。将分离矩阵与三个原凝聚子族放入同一个有限族，
真正构造完整低层覆盖壳及其严格坍缩。在同一 T 中取实际 Def 切片，
全部原参数与 x∈X 都由传递 D 固定，故切片读取原 W 中同一公式。
严格高度界将实际切片放回 W；不预供壳、坍缩、切片或完整分离。

正式模式仍保留原构造来源守卫。后续须在原候选内消去数码、初始帧、
基底枚举等守卫并接回原源公理族；Collection 和 BMS 终局未由此完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffSeparation

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l

universe u

private abbrev up {Γ Θ : SortContext ℒ} (t : Term ℒ Γ Θ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev free {Θ : SortContext ℒ} (t : Term ℒ [] Θ .set) :=
  t.weakenFree SetTheory.SetSort.set
private abbrev free₃ {Θ : SortContext ℒ} (t : Term ℒ [] Θ .set) := free (free (free t))

def family_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    PowerlessRelativeFiniteElementarity.family_m Δ :=
  PowerlessRelativeFiniteHullCodedCoverage.family_m Δ ++
    (PowerlessRelativeFiniteHullExtensionality.family_m Δ ++
      (PowerlessRelativeFiniteHullClosure.family_m Δ ++
        [⟨([SetTheory.SetSort.set] : SortContext ℒ), φ.abstractFreeTop⟩]))

private def insert_m {Δ Θ : SortContext ℒ} (W : Term ℒ [] Θ .set)
    (τ : Variable Δ .set → Term ℒ [] Θ .set) :
    VariableSubstitution ℒ (.set :: .set :: Δ) [.set, .set] Θ
  | _, .here => up (up W)
  | _, .there .here => .bvar .here
  | _, .there (.there v) => up (up (τ v))

private def body_m {Δ Θ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (W : Term ℒ [] Θ .set) (τ : Variable Δ .set → Term ℒ [] Θ .set) :
    Formula ℒ [.set, .set] Θ :=
  (PowerlessRelativization.formula_m φ).substitute
    (.map (fun {s} (v : Variable ([] : SortContext ℒ) s) => nomatch v) (insert_m W τ))

private def env_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ Θ : SortContext ℒ}
    (η : Env 𝒩 [] Θ) (τ : Variable Δ .set → Term ℒ [] Θ .set) : Env 𝒩 [] Δ where
  boundVal := fun v => nomatch v
  freeVal := fun {s} v => match s with | .set => (τ v).eval η

def conclusion_m {Δ Θ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (W X : Term ℒ [] Θ .set) (τ : Variable Δ .set → Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  .existsE .set <| .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up W)) <|
    .forallE .set <| .iff (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there .here)))
      (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up (up X))) (body_m φ W τ))

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) (η : Env 𝒩 [] Θ) (W X : Term ℒ [] Θ .set)
    (τ : Variable Δ .set → Term ℒ [] Θ .set) :
    (conclusion_m φ W X τ).satisfies η ↔
      ∃ Y, member_l 𝒩 Y (W.eval η) ∧ ∀ x,
        member_l 𝒩 x Y ↔ member_l 𝒩 x (X.eval η) ∧
          (PowerlessRelativization.formula_m φ).satisfies
            (((env_l η τ).pushFree x).pushFree (W.eval η)) := by
  let ξ := env_l η τ
  have hBody (Y x : 𝒩.Carrier .set) :
      (body_m φ W τ).satisfies ((η.pushBound Y).pushBound x) ↔
        (PowerlessRelativization.formula_m φ).satisfies ((ξ.pushFree x).pushFree (W.eval η)) := by
    rw [body_m, Formula.satisfies_substitute]
    apply Iff.of_eq
    apply congrArg (fun η => (PowerlessRelativization.formula_m φ).satisfies η)
    apply Env.ext
    · intro _ v; nomatch v
    · intro s v
      cases s
      cases v with
      | here =>
        change (up (up W)).eval ((η.pushBound Y).pushBound x) = W.eval η
        simp only [up, Term.eval_weakenBound]
      | there v =>
        cases v with
        | here => rfl
        | there v =>
          change (up (up (τ v))).eval ((η.pushBound Y).pushBound x) = (τ v).eval η
          simp only [up, Term.eval_weakenBound]
  simp only [conclusion_m, Formula.satisfies, SecondOrderObjectSyntax.member_m,
    Arguments.eval, up, Term.eval_weakenBound]
  change (∃ Y, member_l 𝒩 Y (W.eval η) ∧ ∀ x,
    member_l 𝒩 x Y ↔ member_l 𝒩 x (X.eval η) ∧
      (body_m φ W τ).satisfies ((η.pushBound Y).pushBound x)) ↔ _
  constructor
  · rintro ⟨Y, hY, h⟩
    exact ⟨Y, hY, fun x => (h x).trans (and_congr Iff.rfl (hBody Y x))⟩
  · rintro ⟨Y, hY, h⟩
    exact ⟨Y, hY, fun x => (h x).trans (and_congr Iff.rfl (hBody Y x).symm)⟩

private theorem abstract_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) (η : Env 𝒩 [] Δ)
    (A x : 𝒩.Carrier .set) (hx : member_l 𝒩 x A)
    (hParams : ∀ s (v : Variable Δ s), member_l 𝒩 (η.freeVal v) A) :
    (PowerlessRelativization.formula_m φ.abstractFreeTop).satisfies ((η.pushBound x).pushFree A) ↔
      (PowerlessRelativization.formula_m φ).satisfies ((η.pushFree x).pushFree A) := by
  let ξ : Env (PowerlessMemberStructure.structure_l A ⟨x, hx⟩) [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with | .set => ⟨η.freeVal v, hParams .set v⟩ }
  have hEnv : PowerlessRelativization.env_l (ξ.pushBound (sort := SetTheory.SetSort.set) ⟨x, hx⟩) =
      η.pushBound (sort := SetTheory.SetSort.set) x := by
    apply Env.ext
    · intro s v; cases s; cases v with
      | here => rfl
      | there v => nomatch v
    · intro s v; cases s; rfl
  have hEnv₀ : PowerlessRelativization.env_l (ξ.pushFree (sort := SetTheory.SetSort.set) ⟨x, hx⟩) =
      η.pushFree (sort := SetTheory.SetSort.set) x := by
    apply Env.ext
    · intro _ v; nomatch v
    · intro s v; cases s; cases v <;> rfl
  have h₀ := PowerlessRelativization.formula_l φ.abstractFreeTop
    (ξ.pushBound (sort := SetTheory.SetSort.set) ⟨x, hx⟩)
  rw [hEnv] at h₀
  have h₁ := PowerlessRelativization.formula_l φ (ξ.pushFree (sort := SetTheory.SetSort.set) ⟨x, hx⟩)
  rw [hEnv₀] at h₁
  exact h₀.trans ((Formula.satisfies_abstractFreeTop ξ ⟨x, hx⟩ φ).trans h₁.symm)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

/-- 消费实际联合构造，取得属于原 W 的切片；不另择壳或坍缩。 -/
theorem read_l (K : source_coding_l hℳ) {Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hφ : (⟨([SetTheory.SetSort.set] : SortContext ℒ), φ.abstractFreeTop⟩ :
      Σ Γ : SortContext ℒ, Formula ℒ Γ Δ) ∈ Φ)
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] Θ)
    (B ω Ω W X : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set)
    (hBase : ∀ x, mem_l hℳ x (B.eval η) → ∀ y, mem_l hℳ y x → mem_l hℳ y (B.eval η))
    (hω : SecondOrderOmega.omega_l hℳ (ω.eval η))
    (h : (PowerlessRelativeCutoffCoveredCondensation.conclusion_m Φ B ω Ω W X τ).satisfies η) :
    (conclusion_m φ W X (PowerlessRelativeSourceFamilyCandidateCondensation.original_m Φ τ)).satisfies η := by
  simp only [PowerlessRelativeCutoffCoveredCondensation.conclusion_m, Formula.satisfies_existsFreeTop] at h
  obtain ⟨γ, D, I, h⟩ := h
  let ζ : Env (SecondOrderQuotient.structure_l hℳ) [] (.set :: .set :: .set :: Θ) :=
    ((η.pushFree γ).pushFree D).pushFree I
  let i : Term ℒ [] (.set :: .set :: .set :: Θ) .set := .fvar .here
  let d : Term ℒ [] (.set :: .set :: .set :: Θ) .set := .fvar (.there .here)
  let g : Term ℒ [] (.set :: .set :: .set :: Θ) .set := .fvar (.there (.there .here))
  let ν := PowerlessRelativeSourceFamilyCandidateCondensation.original_m Φ τ
  let ξ : Env (SecondOrderQuotient.structure_l hℳ) [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with | .set => (ν v).eval η }
  have hv (t : Term ℒ [] Θ .set) : (free₃ t).eval ζ = t.eval η := by
    simp only [free₃, free, ζ, Term.eval_weakenFree]
  change (PowerlessRelativeCutoffCoveredCondensation.payload_m Φ B ω Ω W X τ).satisfies ζ at h
  simp only [PowerlessRelativeCutoffCoveredCondensation.payload_m,
    PowerlessRelativeCutoffCoveredElementaryImage.payload_m, Formula.satisfies] at h
  obtain ⟨⟨_hγ, hD, hDW, hXD, hParamsD, _hI, _hCount, _hIW, hDI,
    _hD, _hBI, _hB, _hωSub, _hωI, hElem⟩, hStrict⟩ := h
  have hD₀ := (PowerlessRelativeHierarchySemantics.level_formula_l K ζ (free₃ B) g d).mp hD
  rw [hv] at hD₀
  change PowerlessRelativeHierarchySemantics.level_l hℳ (B.eval η) γ D at hD₀
  have hTransD := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hD₀
  have hDI₀ := (subset_formula_l ζ d i).mp hDI
  change ∀ x, mem_l hℳ x D → mem_l hℳ x I at hDI₀
  change mem_l hℳ ((free₃ X).eval ζ) D at hXD
  rw [hv] at hXD
  change mem_l hℳ D ((free₃ W).eval ζ) at hDW
  rw [hv] at hDW
  have hParamsD₀ := (parameters_formula_l Δ ζ d (fun {s} v => match s with | .set => free₃ (ν v))).mp hParamsD
  have hFree : ∀ s (v : Variable Δ s), mem_l hℳ (ξ.freeVal v) D := by
    intro s v; cases s
    have h := hParamsD₀ .set v
    change mem_l hℳ ((free₃ (ν v)).eval ζ) D at h
    rw [hv] at h
    exact h
  obtain ⟨T, H, J, Ω₀, hH, _hS, _hJ, _hOrd, _hLimitJ, hJT, _hT, hΩ, hW,
    _hTW, hJΩ, _hHC, _hCountT⟩ :=
      (PowerlessRelativeStrictCondensation.conclusion_formula_l K ζ i (free₃ B) (free₃ W) (free₃ ω)).mp hStrict
  simp only [hv] at hW hJT hΩ
  change PowerlessRelativeHierarchySemantics.level_l hℳ (B.eval η) Ω₀ (W.eval η) at hW
  change PowerlessRelativeHierarchySemantics.level_l hℳ (B.eval η) J T at hJT
  change PowerlessRelativeOrdinalCutoff.first_l (B.eval η) (ω.eval η) Ω₀ at hΩ
  have hFixed := PowerlessRelativeMembershipCollapseBase.fixed_l hℳ D I T H hTransD hDI₀ hH.2.1 hH.2.2.2.1
  have hDT : ∀ x, mem_l hℳ x D → mem_l hℳ x T :=
    fun x hx => (SecondOrderFunctionProperties.value_mem_l hℳ hH.2.1 (hFixed x hx)).2
  have hTransW := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hW
  have hParamsT : ∀ s (v : Variable Δ s), mem_l hℳ (ξ.freeVal v) T :=
    fun s v => hDT _ (hFree s v)
  have hParamsW : ∀ s (v : Variable Δ s), mem_l hℳ (ξ.freeVal v) (W.eval η) :=
    fun s v => hTransW D hDW _ (hFree s v)
  have hMatrix := PowerlessRelativeFiniteElementarity.subfamily_formula_l
    [⟨([SetTheory.SetSort.set] : SortContext ℒ), φ.abstractFreeTop⟩] Φ
    (by intro p hp; simp only [List.mem_singleton] at hp; subst p; exact hφ)
    ζ i (free₃ W) (fun v => free₃ (ν v)) hElem
  have hEntry : (PowerlessRelativeFiniteElementarity.entry_m φ.abstractFreeTop i (free₃ W)
      (fun v => free₃ (ν v))).satisfies ζ := hMatrix.1
  have hEq (x : type_l hℳ) (hx : mem_l hℳ x (X.eval η)) :
      (PowerlessRelativization.formula_m φ).satisfies ((ξ.pushFree x).pushFree (W.eval η)) ↔
        (PowerlessRelativization.formula_m φ).satisfies ((ξ.pushFree x).pushFree T) := by
    have hxD := hTransD _ hXD x hx
    have hBound : ∀ v : Variable [.set] .set, mem_l hℳ ((ξ.pushBound x).boundVal v) D := by
      intro v
      cases v with
      | here => exact hxD
      | there v => nomatch v
    have hWT := PowerlessRelativeCoveredCondensation.formula_l hℳ φ.abstractFreeTop ζ i (free₃ W)
      (fun v => free₃ (ν v)) hTransD hDI₀ hH hEntry (ξ.pushBound x) (fun v => hv (ν v)) hBound (fun v => hFree .set v)
    simp only [hv] at hWT
    exact (abstract_formula_l φ ξ (W.eval η) x (hTransW D hDW x hxD) hParamsW).symm.trans
      (hWT.trans (abstract_formula_l φ ξ T x (hDT x hxD) hParamsT))
  obtain ⟨δ, E, hδ, hE, hDef⟩ := PowerlessRelativeLimitClosure.def_bound_l hℳ hBase
    (PowerlessRelativeCutoffLimit.limit_l K hBase hω hΩ) hW hJΩ hJT
  obtain ⟨Y, hY, hRead⟩ := PowerlessRelativeDefSeparation.exists_l hH.1 hDef φ ξ (hDT _ hXD) hParamsT
  apply (formula_l φ η W X ν).mpr
  refine ⟨Y, (PowerlessRelativeLimitClosure.value_l hℳ hBase
    (PowerlessRelativeCutoffLimit.limit_l K hBase hω hΩ) hW Y).mpr ⟨δ, E, hδ, hE, hY⟩, ?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨hxX, hφ⟩ := (hRead x).mp hx
    exact ⟨hxX, (hEq x hxX).mpr hφ⟩
  · rintro ⟨hxX, hφ⟩
    exact (hRead x).mpr ⟨hxX, (hEq x hxX).mp hφ⟩

def schema_m {Δ Θ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B ω Ω W G X e t₀ t₁ t₂ a R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  PowerlessRelativeCutoffCoveredElementaryImage.guarded_m Φ B ω Ω W G X e t₀ t₁ t₂ a R τ
    (conclusion_m φ W X (PowerlessRelativeSourceFamilyCandidateCondensation.original_m Φ τ))

def sentence_m {Δ Θ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B ω Ω W G X e t₀ t₁ t₂ a R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ Φ B ω Ω W G X e t₀ t₁ t₂ a R τ)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hφ : (⟨([SetTheory.SetSort.set] : SortContext ℒ), φ.abstractFreeTop⟩ :
      Σ Γ : SortContext ℒ, Formula ℒ Γ Δ) ∈ Φ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (hΦ₀ : ∀ p ∈ PowerlessRelativeFiniteHullExtensionality.family_m Δ, p ∈ Φ)
    (hΦ₁ : ∀ p ∈ PowerlessRelativeFiniteHullClosure.family_m Δ, p ∈ Φ)
    (B ω Ω W G X e t₀ t₁ t₂ a R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) :
    (sentence_m φ Φ B ω Ω W G X e t₀ t₁ t₂ a R τ).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hHull := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
    (PowerlessRelativeCutoffCoveredCondensation.models_l hℳ Φ hΦ hΦ₀ hΦ₁ B ω Ω W G X e t₀ t₁ t₂ a R τ)
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hClass hBase hω hΩ hW hBW hωB hG hOnto hX hParams hDistinct h₀ h₁ h₂ he ha ht hR
  exact read_l K φ Φ hφ η B ω Ω W X τ
    ((PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ η B).mp hBase)
    ((SecondOrderOmegaSyntax.omega_l hℳ η ω).mp hω)
    (hHull η hClass hBase hω hΩ hW hBW hωB hG hOnto hX hParams hDistinct h₀ h₁ h₂ he ha ht hR)

theorem derives_m {Δ Θ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hφ : (⟨([SetTheory.SetSort.set] : SortContext ℒ), φ.abstractFreeTop⟩ :
      Σ Γ : SortContext ℒ, Formula ℒ Γ Δ) ∈ Φ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (hΦ₀ : ∀ p ∈ PowerlessRelativeFiniteHullExtensionality.family_m Δ, p ∈ Φ)
    (hΦ₁ : ∀ p ∈ PowerlessRelativeFiniteHullClosure.family_m Δ, p ∈ Φ)
    (B ω Ω W G X e t₀ t₁ t₂ a R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) : Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ Φ B ω Ω W G X e t₀ t₁ t₂ a R τ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ φ Φ hφ hΦ hΦ₀ hΦ₁ B ω Ω W G X e t₀ t₁ t₂ a R τ)

/-- 实际合并族的每个原公式实例；四个包含证据均在此证明内提供。 -/
theorem derives_formula_m {Δ Θ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (B ω Ω W G X e t₀ t₁ t₂ a R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m (family_m φ)) .set →
      Term ℒ [] Θ .set) : Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ (family_m φ) B ω Ω W G X e t₀ t₁ t₂ a R τ)) :=
  derives_m φ (family_m φ) (by simp [family_m])
    (by intro p hp; simp only [family_m, List.mem_append]; exact Or.inl hp)
    (by intro p hp; simp only [family_m, List.mem_append]; exact Or.inr (Or.inl hp))
    (by intro p hp; simp only [family_m, List.mem_append]; exact Or.inr (Or.inr (Or.inl hp)))
    B ω Ω W G X e t₀ t₁ t₂ a R τ

#print axioms read_l
#print axioms derives_m
#print axioms derives_formula_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffSeparation
