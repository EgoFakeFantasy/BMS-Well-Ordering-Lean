import BMSConstructibleBridge.PowerlessRelativeFiniteProgramStateBounded

/-! # 实际程序单步的同母界 Δ₀ 表达

七个中间见证由旧状态、当前指令和新状态的实际坐标界回收。
原 good 转移的每个输出都留层，所以否定存在分支可以限制到 W，
仍精确包含非法状态返回 B。算子为纯 Δ₀ 时得到纯 Δ₀ 单步正文；
不预设任意模型内部长度外部标准，也不假定整体求值图存在。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramStepBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_l parameters_pushBound_l parameters_empty_l)
open PowerlessRelativeFiniteProgramStateBounded (record_members_l current_member_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up (up t))
private abbrev up₇ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₃ (up₃ t))

def body_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C W ω w e t₀ t₁ t₂ i D f q S E g s t : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessRelativeFiniteProgramStateBounded.valid_m W ω i D f s) <|
    .conj (PowerlessRelativeFiniteProgramStateBounded.current_m W w e i q) <|
      .conj (PowerlessRelativeFiniteProgramStoreBounded.store_m φ B C W i D f i t₀ t₁ t₂ q S E g)
        (PowerlessRelativeFiniteProgramStateBounded.record_m W S E g t)

def good_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C W ω w e t₀ t₁ t₂ s t : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists W <| membershipLevyBound.boundedExists (up W) <|
    membershipLevyBound.boundedExists (up (up W)) <|
      membershipLevyBound.boundedExists (up₃ W) <|
        membershipLevyBound.boundedExists (up (up₃ W)) <|
          membershipLevyBound.boundedExists (up (up (up₃ W))) <|
            membershipLevyBound.boundedExists (up₃ (up₃ W)) <|
              body_m φ (up₇ B) (up₇ C) (up₇ W) (up₇ ω) (up₇ w) (up₇ e)
                (up₇ t₀) (up₇ t₁) (up₇ t₂)
                (.bvar (.there (.there (.there (.there (.there (.there .here)))))))
                (.bvar (.there (.there (.there (.there (.there .here))))))
                (.bvar (.there (.there (.there (.there .here)))))
                (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here)))
                (.bvar (.there .here)) (.bvar .here) (up₇ s) (up₇ t)

def step_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C W ω w e t₀ t₁ t₂ s t : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (SecondOrderObjectSyntax.member_m t W) <| .disj
    (good_m φ B C W ω w e t₀ t₁ t₂ s t) <| .conj
      (.neg (membershipLevyBound.boundedExists W <|
        good_m φ (up B) (up C) (up W) (up ω) (up w) (up e)
          (up t₀) (up t₁) (up t₂) (up s) (.bvar .here))) (.equal t B)

theorem body_delta_l {Γ Δ : SortContext ℒ}
    {φ : Formula ℒ [] (.set :: .set :: Δ)} (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (B C W ω w e t₀ t₁ t₂ i D f q S E g s t : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (body_m φ B C W ω w e t₀ t₁ t₂ i D f q S E g s t) :=
  .conj (PowerlessRelativeFiniteProgramStateBounded.valid_delta_l _ _ _ _ _ _) <|
    .conj (PowerlessRelativeFiniteProgramStateBounded.current_delta_l _ _ _ _ _) <|
      .conj (PowerlessRelativeFiniteProgramStoreBounded.store_delta_l hφ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
        (PowerlessRelativeFiniteProgramStateBounded.record_delta_l _ _ _ _ _)

theorem good_delta_l {Γ Δ : SortContext ℒ}
    {φ : Formula ℒ [] (.set :: .set :: Δ)} (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (B C W ω w e t₀ t₁ t₂ s t : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (good_m φ B C W ω w e t₀ t₁ t₂ s t) :=
  .bounded_exists W <| .bounded_exists (up W) <| .bounded_exists (up (up W)) <|
    .bounded_exists (up₃ W) <| .bounded_exists (up (up₃ W)) <|
      .bounded_exists (up (up (up₃ W))) <| .bounded_exists (up₃ (up₃ W)) <|
        body_delta_l hφ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem step_delta_l {Γ Δ : SortContext ℒ}
    {φ : Formula ℒ [] (.set :: .set :: Δ)} (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (B C W ω w e t₀ t₁ t₂ s t : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (step_m φ B C W ω w e t₀ t₁ t₂ s t) :=
  .conj (.rel _ _) (.disj (good_delta_l hφ _ _ _ _ _ _ _ _ _ _ _)
    (.conj (.neg (.bounded_exists W (good_delta_l hφ _ _ _ _ _ _ _ _ _ _ _))) (.equal _ _)))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem body_formula_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 Γ Δ) (B β C W ω w e t₀ t₁ t₂ i D f q S E g s t : Term ℒ Γ Δ .set)
    (hB : ∀ x, mem_l hℳ x (B.eval η) → ∀ z, mem_l hℳ z x → mem_l hℳ z (B.eval η))
    (hβ : limit_l hℳ (β.eval η)) (hW : level_l hℳ (B.eval η) (β.eval η) (W.eval η))
    (hBW : mem_l hℳ (B.eval η) (W.eval η))
    (hC : ∀ x, mem_l hℳ x (C.eval η) → mem_l hℳ x (W.eval η))
    (hw : mem_l hℳ (w.eval η) (W.eval η)) (hi : mem_l hℳ (i.eval η) (W.eval η))
    (hf : mem_l hℳ (f.eval η) (W.eval η)) (hq : mem_l hℳ (q.eval η) (W.eval η))
    (hS : mem_l hℳ (S.eval η) (W.eval η)) (hE : mem_l hℳ (E.eval η) (W.eval η))
    (hg : mem_l hℳ (g.eval η) (W.eval η)) (hs : mem_l hℳ (s.eval η) (W.eval η))
    (ht : mem_l hℳ (t.eval η) (W.eval η))
    (hφ : PowerlessRelativeFiniteProgramLimitStep.closed_l φ (parameters_l η) (B.eval η) (W.eval η)) :
    (body_m φ B C W ω w e t₀ t₁ t₂ i D f q S E g s t).satisfies η ↔
      PowerlessRelativeFiniteProgramStep.valid_l (B.eval η) (ω.eval η) (i.eval η) (D.eval η) (f.eval η) (s.eval η) ∧
        PowerlessRelativeFiniteProgramStep.current_l (w.eval η) (e.eval η) (i.eval η) (q.eval η) ∧
          PowerlessRelativeFiniteProgramStore.store_l φ (parameters_l η) (B.eval η) (C.eval η)
            (i.eval η) (D.eval η) (f.eval η) (i.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η)
              (q.eval η) (S.eval η) (E.eval η) (g.eval η) ∧
            PowerlessRelativeFiniteProgramStep.record_l (S.eval η) (E.eval η) (g.eval η) (t.eval η) := by
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hB hW
  exact and_congr (PowerlessRelativeFiniteProgramStateBounded.valid_formula_l η B β W ω i D f s hB hW hs)
    (and_congr (PowerlessRelativeFiniteProgramStateBounded.current_formula_l η W w e i q hTrans hw)
      (and_congr (PowerlessRelativeFiniteProgramStoreBounded.store_formula_l φ η B β C W i D f i
        t₀ t₁ t₂ q S E g hB hβ hW hBW hC hf hi hq hS hE hg hφ)
        (PowerlessRelativeFiniteProgramStateBounded.record_formula_l η W S E g t hTrans ht)))

theorem good_formula_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 Γ Δ) (B β C W ω w e t₀ t₁ t₂ s t : Term ℒ Γ Δ .set)
    (hB : ∀ x, mem_l hℳ x (B.eval η) → ∀ z, mem_l hℳ z x → mem_l hℳ z (B.eval η))
    (hβ : limit_l hℳ (β.eval η)) (hW : level_l hℳ (B.eval η) (β.eval η) (W.eval η))
    (hBW : mem_l hℳ (B.eval η) (W.eval η))
    (hC : ∀ x, mem_l hℳ x (C.eval η) → mem_l hℳ x (W.eval η))
    (hw : mem_l hℳ (w.eval η) (W.eval η)) (he : mem_l hℳ (e.eval η) (W.eval η))
    (hs : mem_l hℳ (s.eval η) (W.eval η)) (ht : mem_l hℳ (t.eval η) (W.eval η))
    (hφ : PowerlessRelativeFiniteProgramLimitStep.closed_l φ (parameters_l η) (B.eval η) (W.eval η)) :
    (good_m φ B C W ω w e t₀ t₁ t₂ s t).satisfies η ↔
      PowerlessRelativeFiniteProgramStep.good_l φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η)
        (w.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (s.eval η) (t.eval η) := by
  let I : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
    .bvar (.there (.there (.there (.there (.there (.there .here))))))
  let D : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
    .bvar (.there (.there (.there (.there (.there .here)))))
  let f : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
    .bvar (.there (.there (.there (.there .here))))
  let q : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
    .bvar (.there (.there (.there .here)))
  let S : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
    .bvar (.there (.there .here))
  let E : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
    .bvar (.there .here)
  let g : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
    .bvar .here
  have hBody (i d F r T A G : type_l hℳ)
      (hi : mem_l hℳ i (W.eval η)) (hF : mem_l hℳ F (W.eval η))
      (hr : mem_l hℳ r (W.eval η)) (hT : mem_l hℳ T (W.eval η))
      (hA : mem_l hℳ A (W.eval η)) (hG : mem_l hℳ G (W.eval η)) :
      (body_m φ (up₇ B) (up₇ C) (up₇ W) (up₇ ω) (up₇ w) (up₇ e)
        (up₇ t₀) (up₇ t₁) (up₇ t₂) I D f q S E g (up₇ s) (up₇ t)).satisfies
          (((((((η.pushBound i).pushBound d).pushBound F).pushBound r).pushBound T).pushBound A).pushBound G) ↔
        PowerlessRelativeFiniteProgramStep.valid_l (B.eval η) (ω.eval η) i d F (s.eval η) ∧
          PowerlessRelativeFiniteProgramStep.current_l (w.eval η) (e.eval η) i r ∧
            PowerlessRelativeFiniteProgramStore.store_l φ (parameters_l η) (B.eval η) (C.eval η)
              i d F i (t₀.eval η) (t₁.eval η) (t₂.eval η) r T A G ∧
                PowerlessRelativeFiniteProgramStep.record_l T A G (t.eval η) := by
    let ξ : Env 𝒱 (.set :: .set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ :=
      ((((((η.pushBound i).pushBound d).pushBound F).pushBound r).pushBound T).pushBound A).pushBound G
    have hEval (v : Term ℒ Γ Δ .set) : (up₇ v).eval ξ = v.eval η := by
      simp only [ξ, up₇, up₃, up, Term.eval_weakenBound]
    simpa only [hEval, ξ, I, D, f, q, S, E, g, parameters_pushBound_l,
      Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there] using
      body_formula_l φ ξ (up₇ B) (up₇ β) (up₇ C) (up₇ W) (up₇ ω) (up₇ w) (up₇ e)
        (up₇ t₀) (up₇ t₁) (up₇ t₂) I D f q S E g (up₇ s) (up₇ t)
        (by simpa only [hEval] using hB) (by simpa only [hEval] using hβ)
        (by simpa only [hEval] using hW) (by simpa only [hEval] using hBW)
        (by simpa only [hEval] using hC) (by simpa only [hEval] using hw)
        (by simpa only [hEval, ξ, I, Term.eval, Env.pushBound_bound_here,
          Env.pushBound_bound_there] using hi)
        (by simpa only [hEval, ξ, f, Term.eval, Env.pushBound_bound_here,
          Env.pushBound_bound_there] using hF)
        (by simpa only [hEval, ξ, q, Term.eval, Env.pushBound_bound_here,
          Env.pushBound_bound_there] using hr)
        (by simpa only [hEval, ξ, S, Term.eval, Env.pushBound_bound_here,
          Env.pushBound_bound_there] using hT)
        (by simpa only [hEval, ξ, E, Term.eval, Env.pushBound_bound_here,
          Env.pushBound_bound_there] using hA)
        (by simpa only [hEval, ξ, g, Term.eval, Env.pushBound_bound_here,
          Env.pushBound_bound_there] using hG)
        (by simpa only [hEval] using hs) (by simpa only [hEval] using ht)
        (by simpa only [hEval, ξ, parameters_pushBound_l] using hφ)
  have hSat : (good_m φ B C W ω w e t₀ t₁ t₂ s t).satisfies η ↔
      ∃ i, mem_l hℳ i (W.eval η) ∧ ∃ d, mem_l hℳ d (W.eval η) ∧
        ∃ F, mem_l hℳ F (W.eval η) ∧ ∃ r, mem_l hℳ r (W.eval η) ∧
          ∃ T, mem_l hℳ T (W.eval η) ∧ ∃ A, mem_l hℳ A (W.eval η) ∧
            ∃ G, mem_l hℳ G (W.eval η) ∧
              (body_m φ (up₇ B) (up₇ C) (up₇ W) (up₇ ω) (up₇ w) (up₇ e)
                (up₇ t₀) (up₇ t₁) (up₇ t₂) I D f q S E g (up₇ s) (up₇ t)).satisfies
                  (((((((η.pushBound i).pushBound d).pushBound F).pushBound r).pushBound T).pushBound A).pushBound G) := by
    simp only [good_m, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
      membershipLevyBound, Formula.satisfies, Arguments.eval, up₇, up₃, up, Term.eval_weakenBound,
      Term.eval, I, D, f, q, S, E, g]
    rfl
  rw [hSat]
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hB hW
  constructor
  · rintro ⟨i, hi, d, _, F, hF, r, hr, T, hT, A, hA, G, hG, h⟩
    exact ⟨i, d, F, r, T, A, G, (hBody i d F r T A G hi hF hr hT hA hG).mp h⟩
  · rintro ⟨i, d, F, r, T, A, G, hValid, hCurrent, hStore, hRecord⟩
    obtain ⟨hi, hd, hF⟩ := record_members_l hTrans hs hValid.1
    obtain ⟨hT, hA, hG⟩ := record_members_l hTrans ht hRecord
    have hr := current_member_l hTrans hw he hCurrent
    exact ⟨i, hi, d, hd, F, hF, r, hr, T, hT, A, hA, G, hG,
      (hBody i d F r T A G hi hF hr hT hA hG).mpr ⟨hValid, hCurrent, hStore, hRecord⟩⟩

theorem step_formula_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 Γ Δ) (B β C W ω w e t₀ t₁ t₂ s t : Term ℒ Γ Δ .set)
    (hB : ∀ x, mem_l hℳ x (B.eval η) → ∀ z, mem_l hℳ z x → mem_l hℳ z (B.eval η))
    (hβ : limit_l hℳ (β.eval η)) (hW : level_l hℳ (B.eval η) (β.eval η) (W.eval η))
    (hBW : mem_l hℳ (B.eval η) (W.eval η))
    (hC : ∀ x, mem_l hℳ x (C.eval η) → mem_l hℳ x (W.eval η))
    (hw : mem_l hℳ (w.eval η) (W.eval η)) (he : mem_l hℳ (e.eval η) (W.eval η))
    (hs : mem_l hℳ (s.eval η) (W.eval η))
    (hφ : PowerlessRelativeFiniteProgramLimitStep.closed_l φ (parameters_l η) (B.eval η) (W.eval η)) :
    (step_m φ B C W ω w e t₀ t₁ t₂ s t).satisfies η ↔
      PowerlessRelativeFiniteProgramStep.step_l φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η)
        (w.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (s.eval η) (t.eval η) := by
  have hGood (z : type_l hℳ) (hz : mem_l hℳ z (W.eval η)) :
      (good_m φ (up B) (up C) (up W) (up ω) (up w) (up e)
        (up t₀) (up t₁) (up t₂) (up s) (.bvar .here)).satisfies (η.pushBound z) ↔
        PowerlessRelativeFiniteProgramStep.good_l φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η)
          (w.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (s.eval η) z := by
    simpa only [up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, parameters_pushBound_l] using
      good_formula_l φ (η.pushBound z) (up B) (up β) (up C) (up W) (up ω) (up w) (up e)
        (up t₀) (up t₁) (up t₂) (up s) (.bvar .here)
        (by simpa only [up, Term.eval_weakenBound] using hB)
        (by simpa only [up, Term.eval_weakenBound] using hβ)
        (by simpa only [up, Term.eval_weakenBound] using hW)
        (by simpa only [up, Term.eval_weakenBound] using hBW)
        (by simpa only [up, Term.eval_weakenBound] using hC)
        (by simpa only [up, Term.eval_weakenBound] using hw)
        (by simpa only [up, Term.eval_weakenBound] using he)
        (by simpa only [up, Term.eval_weakenBound] using hs)
        (by simpa only [up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here] using hz)
        (by simpa only [up, Term.eval_weakenBound, parameters_pushBound_l] using hφ)
  have hSome : (∃ z, mem_l hℳ z (W.eval η) ∧
      (good_m φ (up B) (up C) (up W) (up ω) (up w) (up e)
        (up t₀) (up t₁) (up t₂) (up s) (.bvar .here)).satisfies (η.pushBound z)) ↔
        ∃ z, PowerlessRelativeFiniteProgramStep.good_l φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η)
          (w.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (s.eval η) z := by
    constructor
    · rintro ⟨z, hz, h⟩
      exact ⟨z, (hGood z hz).mp h⟩
    · rintro ⟨z, h⟩
      have hz := PowerlessRelativeFiniteProgramLimitStep.step_l φ (parameters_l η) hB hβ hW hBW hC hφ hs
        ⟨PowerlessRelativeFiniteProgramStep.good_class_l φ (parameters_l η) hB h, Or.inl h⟩
      exact ⟨z, hz, (hGood z hz).mpr h⟩
  simp only [step_m, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, SecondOrderObjectSyntax.member_m,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  change (mem_l hℳ (t.eval η) (W.eval η) ∧
    ((good_m φ B C W ω w e t₀ t₁ t₂ s t).satisfies η ∨
      ((¬∃ z, mem_l hℳ z (W.eval η) ∧
        (good_m φ (up B) (up C) (up W) (up ω) (up w) (up e)
          (up t₀) (up t₁) (up t₂) (up s) (.bvar .here)).satisfies (η.pushBound z)) ∧
          t.eval η = B.eval η))) ↔ _
  rw [hSome]
  constructor
  · rintro ⟨ht, h⟩
    exact ⟨⟨β.eval η, W.eval η, hW, ht⟩,
      (or_congr (good_formula_l φ η B β C W ω w e t₀ t₁ t₂ s t hB hβ hW hBW hC hw he hs ht hφ) Iff.rfl).mp h⟩
  · intro h
    have ht := PowerlessRelativeFiniteProgramLimitStep.step_l φ (parameters_l η) hB hβ hW hBW hC hφ hs h
    exact ⟨ht,
      (or_congr (good_formula_l φ η B β C W ω w e t₀ t₁ t₂ s t hB hβ hW hBW hC hw he hs ht hφ) Iff.rfl).mpr h.2⟩

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β C W ω w e t₀ t₁ t₂ s t : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.limit_m β) <|
      .imp (PowerlessRelativeHierarchySyntax.level_m B β W) <|
        .imp (SecondOrderObjectSyntax.member_m B W) <|
          .imp (ThirdOrderTheory.subset_m C W) <|
            .imp (SecondOrderObjectSyntax.member_m w W) <|
              .imp (SecondOrderObjectSyntax.member_m e W) <|
                .imp (SecondOrderObjectSyntax.member_m s W) <|
                  .imp (PowerlessRelativeFiniteProgramLimitStep.closed_m φ B W) <|
                    .iff (step_m φ B C W ω w e t₀ t₁ t₂ s t)
                      (PowerlessRelativeFiniteProgramStep.step_m φ B C ω w e t₀ t₁ t₂ s t)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β C W ω w e t₀ t₁ t₂ s t : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B β C W ω w e t₀ t₁ t₂ s t)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (B β C W ω w e t₀ t₁ t₂ s t : Term ℒ [] Δ .set) :
    (sentence_m φ B β C W ω w e t₀ t₁ t₂ s t).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.limit_formula_l, PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeFiniteProgramLimitStep.closed_formula_l K, subset_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  intro η hB hβ hW hBW hC hw he hs hφ
  exact (step_formula_l φ η B β C W ω w e t₀ t₁ t₂ s t hB hβ hW hBW hC hw he hs hφ).trans
    (PowerlessRelativeFiniteProgramStep.step_formula_l K φ η B C ω w e t₀ t₁ t₂ s t).symm

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β C W ω w e t₀ t₁ t₂ s t : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B β C W ω w e t₀ t₁ t₂ s t)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 φ B β C W ω w e t₀ t₁ t₂ s t)

#print axioms step_delta_l
#print axioms good_formula_l
#print axioms step_formula_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramStepBounded
