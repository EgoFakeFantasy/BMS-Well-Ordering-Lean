import BMSConstructibleBridge.PowerlessRelativeFiniteProgramStoreBounded

/-! # 实际程序状态和当前指令的纯有界检查

状态的嵌套 Kuratowski 坐标由状态留层给界，实际 valid 的 Class
守卫因此冗余。当前指令不存在读数的分支仍与原 raw 检查等价，
只借助词图的坐标界，不假定当前指令必定存在或合法。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramStateBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l)
open PowerlessRelativeFiniteProgramLimitStep (coordinates_l reading_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def record_m {Γ Δ : SortContext ℒ} (W i D f s : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists W <|
    .conj (PowerlessPairBounded.ordered_m (up D) (up f) (.bvar .here))
      (PowerlessPairBounded.ordered_m (up i) (.bvar .here) (up s))

def current_m {Γ Δ : SortContext ℒ} (W w e i q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (PowerlessValueBounded.formula_m w i q) <| .conj
    (.neg (membershipLevyBound.boundedExists W <|
      PowerlessValueBounded.formula_m (up w) (up i) (.bvar .here))) (.equal q e)

def valid_m {Γ Δ : SortContext ℒ} (W ω i D f s : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (record_m W i D f s) <| .conj (SecondOrderObjectSyntax.member_m i ω)
    (PowerlessMapBounded.formula_m f i D)

theorem record_delta_l {Γ Δ : SortContext ℒ} (W i D f s : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (record_m W i D f s) :=
  .bounded_exists W (.conj (PowerlessPairBounded.ordered_delta_l _ _ _)
    (PowerlessPairBounded.ordered_delta_l _ _ _))

theorem current_delta_l {Γ Δ : SortContext ℒ} (W w e i q : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (current_m W w e i q) :=
  .disj (PowerlessValueBounded.delta_l _ _ _)
    (.conj (.neg (.bounded_exists W (PowerlessValueBounded.delta_l _ _ _))) (.equal _ _))

theorem valid_delta_l {Γ Δ : SortContext ℒ} (W ω i D f s : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (valid_m W ω i D f s) :=
  .conj (record_delta_l _ _ _ _ _) (.conj (.rel _ _) (PowerlessMapBounded.delta_l _ _ _))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem record_members_l {W i D f s : type_l hℳ}
    (hW : ∀ a, mem_l hℳ a W → ∀ b, mem_l hℳ b a → mem_l hℳ b W)
    (hs : mem_l hℳ s W) (h : PowerlessRelativeFiniteProgramStep.record_l i D f s) :
    mem_l hℳ i W ∧ mem_l hℳ D W ∧ mem_l hℳ f W := by
  obtain ⟨p, hDf, hip⟩ := h
  obtain ⟨hi, hp⟩ := coordinates_l hW hs hip
  exact ⟨hi, coordinates_l hW hp hDf⟩

theorem record_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (W i D f s : Term ℒ Γ Δ .set)
    (hW : ∀ a, mem_l hℳ a (W.eval η) → ∀ b, mem_l hℳ b a → mem_l hℳ b (W.eval η))
    (hs : mem_l hℳ (s.eval η) (W.eval η)) :
    (record_m W i D f s).satisfies η ↔
      PowerlessRelativeFiniteProgramStep.record_l (i.eval η) (D.eval η) (f.eval η) (s.eval η) := by
  have hSat : (record_m W i D f s).satisfies η ↔
      ∃ p, mem_l hℳ p (W.eval η) ∧ ordered_l (ℳ := 𝒱) (D.eval η) (f.eval η) p ∧
        ordered_l (ℳ := 𝒱) (i.eval η) p (s.eval η) := by
    simp only [record_m, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
      membershipLevyBound, Formula.satisfies, PowerlessPairBounded.ordered_formula_l,
      Arguments.eval, up, Term.eval_weakenBound, Term.eval]
    rfl
  rw [hSat]
  exact ⟨fun ⟨p, _, hDf, hip⟩ => ⟨p, hDf, hip⟩,
    fun ⟨p, hDf, hip⟩ => ⟨p, (coordinates_l hW hs hip).2, hDf, hip⟩⟩

theorem current_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (W w e i q : Term ℒ Γ Δ .set)
    (hW : ∀ a, mem_l hℳ a (W.eval η) → ∀ b, mem_l hℳ b a → mem_l hℳ b (W.eval η))
    (hw : mem_l hℳ (w.eval η) (W.eval η)) :
    (current_m W w e i q).satisfies η ↔
      PowerlessRelativeFiniteProgramStep.current_l (w.eval η) (e.eval η) (i.eval η) (q.eval η) := by
  have hSome : (∃ z, mem_l hℳ z (W.eval η) ∧ value_l (ℳ := 𝒱) (w.eval η) (i.eval η) z) ↔
      ∃ z, value_l (ℳ := 𝒱) (w.eval η) (i.eval η) z :=
    ⟨fun ⟨z, _, hz⟩ => ⟨z, hz⟩, fun ⟨z, hz⟩ => ⟨z, reading_l hW hw hz, hz⟩⟩
  simp only [current_m, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessValueBounded.formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  change (value_l (ℳ := 𝒱) (w.eval η) (i.eval η) (q.eval η) ∨
    ((¬∃ z, mem_l hℳ z (W.eval η) ∧ value_l (ℳ := 𝒱) (w.eval η) (i.eval η) z) ∧
      q.eval η = e.eval η)) ↔ _
  rw [hSome]
  rfl

theorem current_member_l {W w e i q : type_l hℳ}
    (hW : ∀ a, mem_l hℳ a W → ∀ b, mem_l hℳ b a → mem_l hℳ b W)
    (hw : mem_l hℳ w W) (he : mem_l hℳ e W)
    (hq : PowerlessRelativeFiniteProgramStep.current_l w e i q) : mem_l hℳ q W := by
  rcases hq with hq | ⟨_, rfl⟩
  · exact reading_l hW hw hq
  · exact he

theorem valid_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (B β W ω i D f s : Term ℒ Γ Δ .set)
    (hB : ∀ x, mem_l hℳ x (B.eval η) → ∀ z, mem_l hℳ z x → mem_l hℳ z (B.eval η))
    (hW : level_l hℳ (B.eval η) (β.eval η) (W.eval η)) (hs : mem_l hℳ (s.eval η) (W.eval η)) :
    (valid_m W ω i D f s).satisfies η ↔
      PowerlessRelativeFiniteProgramStep.valid_l (B.eval η) (ω.eval η) (i.eval η) (D.eval η) (f.eval η) (s.eval η) := by
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hB hW
  rw [valid_m, Formula.satisfies, record_formula_l η W i D f s hTrans hs]
  have hMap := PowerlessMapBounded.formula_l η f i D
  change (PowerlessRelativeFiniteProgramStep.record_l (i.eval η) (D.eval η) (f.eval η) (s.eval η) ∧
    mem_l hℳ (i.eval η) (ω.eval η) ∧ (PowerlessMapBounded.formula_m f i D).satisfies η) ↔ _
  rw [hMap]
  constructor
  · rintro ⟨hRecord, hiω, hf⟩
    obtain ⟨hi, hD, hF⟩ := record_members_l hTrans hs hRecord
    exact ⟨hRecord, hiω, ⟨β.eval η, W.eval η, hW, hi⟩,
      ⟨β.eval η, W.eval η, hW, hD⟩, ⟨β.eval η, W.eval η, hW, hF⟩, hf⟩
  · rintro ⟨hRecord, hiω, _, _, _, hf⟩
    exact ⟨hRecord, hiω, hf⟩

def schema_m {Δ : SortContext ℒ} (B β W ω w e i D f q s : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.level_m B β W) <|
      .imp (SecondOrderObjectSyntax.member_m w W) <|
        .imp (SecondOrderObjectSyntax.member_m s W) <|
          .conj (.iff (record_m W i D f s) (PowerlessRelativeFiniteProgramStep.record_m i D f s)) <|
            .conj (.iff (valid_m W ω i D f s) (PowerlessRelativeFiniteProgramStep.valid_m B ω i D f s))
              (.iff (current_m W w e i q) (PowerlessRelativeFiniteProgramStep.current_m w e i q))

def sentence_m {Δ : SortContext ℒ} (B β W ω w e i D f q s : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B β W ω w e i D f q s)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B β W ω w e i D f q s : Term ℒ [] Δ .set) :
    (sentence_m B β W ω w e i D f q s).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  intro η hB hW hw hs
  have hTrans := PowerlessRelativeLevelClosure.transitive_l h𝒩 hB hW
  exact ⟨(record_formula_l η W i D f s hTrans hs).trans
      (PowerlessRelativeFiniteProgramStep.record_formula_l η i D f s).symm,
    (valid_formula_l η B β W ω i D f s hB hW hs).trans
      (PowerlessRelativeFiniteProgramStep.valid_formula_l K η B ω i D f s).symm,
    (current_formula_l η W w e i q hTrans hw).trans
      (PowerlessRelativeFiniteProgramStep.current_formula_l η w e i q).symm⟩

theorem derives_m {Δ : SortContext ℒ} (B β W ω w e i D f q s : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m B β W ω w e i D f q s)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 B β W ω w e i D f q s)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramStateBounded
