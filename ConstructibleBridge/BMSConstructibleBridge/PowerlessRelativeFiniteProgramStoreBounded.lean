import BMSConstructibleBridge.PowerlessRelativeFiniteProgramInstructionBounded

/-! # 精确单点存储更新的同母界 Δ₀ 正文

adjoin 直接用成员包含与反向有界检查表达，仍约束全部原对象。
两张图和新增坐标、值属于 W 时，图读数的全对象方程等价于
W 内方程：任一界外读数都被实际 Kuratowski 坐标界排除。
原 Class 守卫由同层成员性取得；没有额外收集或隐藏图成员。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramStoreBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_l parameters_pushBound_l parameters_empty_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)

def adjoin_m {Γ Δ : SortContext ℒ} (A c S : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (SecondOrderObjectSyntax.member_m c S) <|
    .conj (membershipLevyBound.boundedForall A (SecondOrderObjectSyntax.member_m (.bvar .here) (up S)))
      (membershipLevyBound.boundedForall S <|
        .disj (SecondOrderObjectSyntax.member_m (.bvar .here) (up A)) (.equal (.bvar .here) (up c)))

theorem adjoin_delta_l {Γ Δ : SortContext ℒ} (A c S : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (adjoin_m A c S) :=
  .conj (.rel _ _) (.conj (.bounded_forall A (.rel _ _))
    (.bounded_forall S (.disj (.rel _ _) (.equal _ _))))

theorem adjoin_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (A c S : Term ℒ Γ Δ .set) :
    (adjoin_m A c S).satisfies η ↔
      ∀ x, member_l 𝒩 x (S.eval η) ↔ member_l 𝒩 x (A.eval η) ∨ x = c.eval η := by
  have h : (adjoin_m A c S).satisfies η ↔ member_l 𝒩 (c.eval η) (S.eval η) ∧
      (∀ x, member_l 𝒩 x (A.eval η) → member_l 𝒩 x (S.eval η)) ∧
        ∀ x, member_l 𝒩 x (S.eval η) → member_l 𝒩 x (A.eval η) ∨ x = c.eval η := by
    simp only [adjoin_m, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
      membershipLevyBound, Formula.satisfies, SecondOrderObjectSyntax.member_m,
      Arguments.eval, up, Term.eval_weakenBound, Term.eval]
    rfl
  rw [h]
  constructor
  · rintro ⟨hc, hA, hS⟩ x
    exact ⟨hS x, fun hx => hx.elim (hA x) (fun he => he.symm ▸ hc)⟩
  · intro h
    exact ⟨(h _).mpr (Or.inr rfl), fun x hx => (h x).mpr (Or.inl hx), fun x => (h x).mp⟩

def reading_m {Γ Δ : SortContext ℒ} (W f c y g : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall W <| membershipLevyBound.boundedForall (up W) <|
    .iff (PowerlessValueBounded.formula_m (up₂ g) (.bvar (.there .here)) (.bvar .here))
      (.disj (PowerlessValueBounded.formula_m (up₂ f) (.bvar (.there .here)) (.bvar .here))
        (.conj (.equal (.bvar (.there .here)) (up₂ c)) (.equal (.bvar .here) (up₂ y))))

theorem reading_delta_l {Γ Δ : SortContext ℒ} (W f c y g : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (reading_m W f c y g) :=
  .bounded_forall W (.bounded_forall (up W) (.iff (PowerlessValueBounded.delta_l _ _ _)
    (.disj (PowerlessValueBounded.delta_l _ _ _) (.conj (.equal _ _) (.equal _ _)))))

theorem reading_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (W f c y g : Term ℒ Γ Δ .set) :
    (reading_m W f c y g).satisfies η ↔
      ∀ x, member_l 𝒩 x (W.eval η) → ∀ z, member_l 𝒩 z (W.eval η) →
        (value_l (ℳ := 𝒩) (g.eval η) x z ↔
          value_l (ℳ := 𝒩) (f.eval η) x z ∨ x = c.eval η ∧ z = y.eval η) := by
  simp only [reading_m, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessValueBounded.formula_l,
    Arguments.eval, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

def store_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C W A D f c t₀ t₁ t₂ q S E g : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists W <|
    .conj (PowerlessRelativeFiniteProgramInstructionBounded.computed_m φ
      (up B) (up C) (up W) (up f) (up t₀) (up t₁) (up t₂) (up q) (.bvar .here)) <|
      .conj (adjoin_m (up A) (up c) (up S)) <|
        .conj (adjoin_m (up D) (.bvar .here) (up E)) <|
          .conj (PowerlessMapBounded.formula_m (up g) (up S) (up E))
            (reading_m (up W) (up f) (up c) (.bvar .here) (up g))

theorem store_delta_l {Γ Δ : SortContext ℒ}
    {φ : Formula ℒ [] (.set :: .set :: Δ)} (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (B C W A D f c t₀ t₁ t₂ q S E g : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (store_m φ B C W A D f c t₀ t₁ t₂ q S E g) :=
  .bounded_exists W <|
    .conj (PowerlessRelativeFiniteProgramInstructionBounded.computed_delta_l hφ _ _ _ _ _ _ _ _ _) <|
      .conj (adjoin_delta_l _ _ _) <| .conj (adjoin_delta_l _ _ _) <|
        .conj (PowerlessMapBounded.delta_l _ _ _) (reading_delta_l _ _ _ _ _)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem reading_iff_l {W f c y g : type_l hℳ}
    (hW : ∀ a, mem_l hℳ a W → ∀ b, mem_l hℳ b a → mem_l hℳ b W)
    (hf : mem_l hℳ f W) (hg : mem_l hℳ g W) (hc : mem_l hℳ c W) (hy : mem_l hℳ y W) :
    (∀ x, mem_l hℳ x W → ∀ z, mem_l hℳ z W →
      (value_l (ℳ := 𝒱) g x z ↔ value_l (ℳ := 𝒱) f x z ∨ x = c ∧ z = y)) ↔
      ∀ x z, value_l (ℳ := 𝒱) g x z ↔ value_l (ℳ := 𝒱) f x z ∨ x = c ∧ z = y := by
  have hCoords {F x z : type_l hℳ} (hF : mem_l hℳ F W) (hxz : value_l (ℳ := 𝒱) F x z) :
      mem_l hℳ x W ∧ mem_l hℳ z W := by
    obtain ⟨p, hp, hxz⟩ := hxz
    exact PowerlessRelativeFiniteProgramLimitStep.coordinates_l hW (hW F hF p hp) hxz
  constructor
  · intro h x z
    constructor
    · intro hxz
      obtain ⟨hx, hz⟩ := hCoords hg hxz
      exact (h x hx z hz).mp hxz
    · intro hxz
      have hBound : mem_l hℳ x W ∧ mem_l hℳ z W := by
        rcases hxz with hxz | ⟨rfl, rfl⟩
        · exact hCoords hf hxz
        · exact ⟨hc, hy⟩
      exact (h x hBound.1 z hBound.2).mpr hxz
  · intro h x _ z _
    exact h x z

theorem store_formula_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 Γ Δ) (B β C W A D f c t₀ t₁ t₂ q S E g : Term ℒ Γ Δ .set)
    (hB : ∀ x, mem_l hℳ x (B.eval η) → ∀ z, mem_l hℳ z x → mem_l hℳ z (B.eval η))
    (hβ : limit_l hℳ (β.eval η)) (hW : level_l hℳ (B.eval η) (β.eval η) (W.eval η))
    (hBW : mem_l hℳ (B.eval η) (W.eval η))
    (hC : ∀ x, mem_l hℳ x (C.eval η) → mem_l hℳ x (W.eval η))
    (hf : mem_l hℳ (f.eval η) (W.eval η)) (hc : mem_l hℳ (c.eval η) (W.eval η))
    (hq : mem_l hℳ (q.eval η) (W.eval η)) (hS : mem_l hℳ (S.eval η) (W.eval η))
    (hE : mem_l hℳ (E.eval η) (W.eval η)) (hg : mem_l hℳ (g.eval η) (W.eval η))
    (hφ : PowerlessRelativeFiniteProgramLimitStep.closed_l φ (parameters_l η) (B.eval η) (W.eval η)) :
    (store_m φ B C W A D f c t₀ t₁ t₂ q S E g).satisfies η ↔
      PowerlessRelativeFiniteProgramStore.store_l φ (parameters_l η) (B.eval η) (C.eval η)
        (A.eval η) (D.eval η) (f.eval η) (c.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η)
          (q.eval η) (S.eval η) (E.eval η) (g.eval η) := by
  have hComputed (y : type_l hℳ) :=
    PowerlessRelativeFiniteProgramInstructionBounded.computed_formula_l φ (η.pushBound y)
      (up B) (up β) (up C) (up W) (up f) (up t₀) (up t₁) (up t₂) (up q) (.bvar .here)
        (by simpa only [up, Term.eval_weakenBound] using hB)
        (by simpa only [up, Term.eval_weakenBound] using hβ)
        (by simpa only [up, Term.eval_weakenBound] using hW)
        (by simpa only [up, Term.eval_weakenBound] using hBW)
        (by simpa only [up, Term.eval_weakenBound] using hC)
        (by simpa only [up, Term.eval_weakenBound] using hf)
        (by simpa only [up, Term.eval_weakenBound] using hq)
        (by simpa only [up, Term.eval_weakenBound, parameters_pushBound_l] using hφ)
  have hSat : (store_m φ B C W A D f c t₀ t₁ t₂ q S E g).satisfies η ↔
      ∃ y, mem_l hℳ y (W.eval η) ∧
        PowerlessRelativeFiniteProgramInstruction.computed_l φ (parameters_l η)
          (B.eval η) (C.eval η) (f.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (q.eval η) y ∧
        (∀ x, mem_l hℳ x (S.eval η) ↔ mem_l hℳ x (A.eval η) ∨ x = c.eval η) ∧
        (∀ z, mem_l hℳ z (E.eval η) ↔ mem_l hℳ z (D.eval η) ∨ z = y) ∧
        map_l (ℳ := 𝒱) (g.eval η) (S.eval η) (E.eval η) ∧
        ∀ x, mem_l hℳ x (W.eval η) → ∀ z, mem_l hℳ z (W.eval η) →
          (value_l (ℳ := 𝒱) (g.eval η) x z ↔
            value_l (ℳ := 𝒱) (f.eval η) x z ∨ x = c.eval η ∧ z = y) := by
    simp only [store_m, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
      membershipLevyBound, Formula.satisfies, hComputed, adjoin_formula_l,
      PowerlessMapBounded.formula_l, reading_formula_l, parameters_pushBound_l,
      Arguments.eval, up, Term.eval_weakenBound, Term.eval]
    rfl
  rw [hSat]
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hB hW
  constructor
  · rintro ⟨y, hy, hComputed, hA, hD, hMap, hRead⟩
    exact ⟨y, hComputed, ⟨β.eval η, W.eval η, hW, hS⟩, ⟨β.eval η, W.eval η, hW, hE⟩,
      ⟨β.eval η, W.eval η, hW, hg⟩, hA, hD, hMap, (reading_iff_l hTrans hf hg hc hy).mp hRead⟩
  · rintro ⟨y, hComputed, _, _, _, hA, hD, hMap, hRead⟩
    have hy := PowerlessRelativeFiniteProgramLimitStep.computed_l φ (parameters_l η)
      hB hβ hW hBW hC hf hφ hComputed
    exact ⟨y, hy, hComputed, hA, hD, hMap, (reading_iff_l hTrans hf hg hc hy).mpr hRead⟩

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β C W A D f c t₀ t₁ t₂ q S E g : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.limit_m β) <|
      .imp (PowerlessRelativeHierarchySyntax.level_m B β W) <|
        .imp (SecondOrderObjectSyntax.member_m B W) <|
          .imp (ThirdOrderTheory.subset_m C W) <|
            .imp (SecondOrderObjectSyntax.member_m f W) <|
              .imp (SecondOrderObjectSyntax.member_m c W) <|
                .imp (SecondOrderObjectSyntax.member_m q W) <|
                  .imp (SecondOrderObjectSyntax.member_m S W) <|
                    .imp (SecondOrderObjectSyntax.member_m E W) <|
                      .imp (SecondOrderObjectSyntax.member_m g W) <|
                        .imp (PowerlessRelativeFiniteProgramLimitStep.closed_m φ B W) <|
                          .iff (store_m φ B C W A D f c t₀ t₁ t₂ q S E g)
                            (PowerlessRelativeFiniteProgramStore.store_m φ B C A D f c t₀ t₁ t₂ q S E g)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β C W A D f c t₀ t₁ t₂ q S E g : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B β C W A D f c t₀ t₁ t₂ q S E g)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (B β C W A D f c t₀ t₁ t₂ q S E g : Term ℒ [] Δ .set) :
    (sentence_m φ B β C W A D f c t₀ t₁ t₂ q S E g).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.limit_formula_l, PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeFiniteProgramLimitStep.closed_formula_l K, subset_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  intro η hB hβ hW hBW hC hf hc hq hS hE hg hφ
  exact (store_formula_l φ η B β C W A D f c t₀ t₁ t₂ q S E g
    hB hβ hW hBW hC hf hc hq hS hE hg hφ).trans
      (PowerlessRelativeFiniteProgramStore.store_formula_l K φ η B C A D f c t₀ t₁ t₂ q S E g).symm

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β C W A D f c t₀ t₁ t₂ q S E g : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B β C W A D f c t₀ t₁ t₂ q S E g)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ h𝒩 => models_l h𝒩 φ B β C W A D f c t₀ t₁ t₂ q S E g)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramStoreBounded
