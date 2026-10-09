import BMSConstructibleBridge.PowerlessRelativeFiniteProgramRunBounded

/-! # 原真实读数和总化输出的同母界表达

原 LimitRun 的 refine／forget 消去历史见证有界性的额外要求。
不存在任何原 run 精确等价为不存在 W 内的有界 run，因此缺省 B
也被保留。以下守卫均是已使用的原有限程序和层规格，不是新公理。
算子为纯 Δ₀ 时输出正文为纯 Δ₀；整个求值图仍须另行构造。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramOutputBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)
open PowerlessBMSQuotientSubsetImageDerives
  (parameters_l parameters_pushBound_l parameters_empty_l)
open PowerlessRelativeFiniteProgramInstruction (functional_l functional_m tags_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private def binding_m {Γ Δ : SortContext ℒ} : Substitution ℒ [] Δ Γ Δ :=
  .map (fun v => nomatch v) (fun v => .fvar v)
private def embed_m {Γ Δ : SortContext ℒ} (t : Term ℒ [] Δ .set) : Term ℒ Γ Δ .set :=
  t.substitute binding_m

def output_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C W ω w e t₀ t₁ t₂ a n k : Term ℒ [] Δ .set) (y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (SecondOrderObjectSyntax.member_m y (embed_m W)) <| .disj
    (PowerlessRelativeFiniteProgramRunBounded.run_m φ B C W ω w e t₀ t₁ t₂ a n k y) <|
      .conj (.neg (membershipLevyBound.boundedExists (embed_m W) <|
        PowerlessRelativeFiniteProgramRunBounded.run_m φ B C W ω w e t₀ t₁ t₂ a n k (.bvar .here)))
          (.equal y (embed_m B))

theorem output_delta_l {Γ Δ : SortContext ℒ}
    {φ : Formula ℒ [] (.set :: .set :: Δ)} (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (B C W ω w e t₀ t₁ t₂ a n k : Term ℒ [] Δ .set) (y : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (output_m φ B C W ω w e t₀ t₁ t₂ a n k y) :=
  .conj (.rel _ _) <| .disj
    (PowerlessRelativeFiniteProgramRunBounded.run_delta_l hφ _ _ _ _ _ _ _ _ _ _ _ _ _) <|
      .conj (.neg (.bounded_exists (embed_m W)
        (PowerlessRelativeFiniteProgramRunBounded.run_delta_l hφ _ _ _ _ _ _ _ _ _ _ _ _ _))) (.equal _ _)

def guard_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β C W ω w N Q e t₀ t₁ t₂ a n : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .conj (PowerlessRelativeHierarchySyntax.limit_m β) <|
      .conj (PowerlessRelativeHierarchySyntax.level_m B β W) <|
        .conj (SecondOrderObjectSyntax.member_m B W) <|
          .conj (PowerlessRelativeHierarchySyntax.class_m B C) <|
            .conj (ThirdOrderTheory.subset_m C W) <|
              .conj (SecondOrderOmegaSyntax.omega_m ω) <|
                .conj (SecondOrderObjectSyntax.member_m ω W) <|
                  .conj (SecondOrderObjectSyntax.member_m w W) <|
                    .conj (PowerlessDefinableFiniteTraceDerives.zero_m e) <|
                      .conj (PowerlessRelativeFiniteProgramStep.record_m e e e a) <|
                        .conj (SecondOrderObjectSyntax.map_m w N Q) <|
                          .conj (tags_m t₀ t₁ t₂) <| .conj (functional_m φ B) <|
                            .conj (PowerlessRelativeFiniteProgramLimitStep.closed_m φ B W)
                              (SecondOrderObjectSyntax.member_m n ω)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def guard_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (B β C W ω w N Q e t₀ t₁ t₂ a n : type_l hℳ) : Prop :=
  (∀ x, mem_l hℳ x B → ∀ z, mem_l hℳ z x → mem_l hℳ z B) ∧ limit_l hℳ β ∧
    level_l hℳ B β W ∧ mem_l hℳ B W ∧ PowerlessRelativeClassCorrespondence.member_l hℳ B C ∧
    (∀ x, mem_l hℳ x C → mem_l hℳ x W) ∧ SecondOrderOmega.omega_l hℳ ω ∧
    mem_l hℳ ω W ∧ mem_l hℳ w W ∧ (∀ x, ¬mem_l hℳ x e) ∧
    PowerlessRelativeFiniteProgramStep.record_l e e e a ∧ map_l (ℳ := 𝒱) w N Q ∧
    (t₀ ≠ t₁ ∧ t₀ ≠ t₂ ∧ t₁ ≠ t₂) ∧ functional_l φ η B ∧
    PowerlessRelativeFiniteProgramLimitStep.closed_l φ η B W ∧ mem_l hℳ n ω

theorem guard_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B β C W ω w N Q e t₀ t₁ t₂ a n : Term ℒ Γ Δ .set) :
    (guard_m φ B β C W ω w N Q e t₀ t₁ t₂ a n).satisfies η ↔
      guard_l φ (parameters_l η) (B.eval η) (β.eval η) (C.eval η) (W.eval η) (ω.eval η)
        (w.eval η) (N.eval η) (Q.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η)
        (a.eval η) (n.eval η) := by
  simp only [guard_m, guard_l, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ,
    PowerlessRelativeHierarchySemantics.limit_formula_l, PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeHierarchySemantics.class_formula_l K, subset_formula_l, SecondOrderOmegaSyntax.omega_l,
    PowerlessDefinableFiniteTraceDerives.zero_formula_l, PowerlessRelativeFiniteProgramStep.record_formula_l,
    map_formula_l, tags_m, PowerlessRelativeFiniteProgramInstruction.functional_formula_l K,
    PowerlessRelativeFiniteProgramLimitStep.closed_formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  rfl

private theorem embed_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ) (t : Term ℒ [] Δ .set) :
    (embed_m t).eval η = t.eval (parameters_l η) := by
  rw [embed_m, Term.eval_substitute]
  apply congrArg (fun ξ => t.eval ξ)
  apply Env.ext
  · intro s v; nomatch v
  · intro s v; rfl

/-- 输出正文自身包含成员守卫；此方向无需程序合法性或层闭包。 -/
theorem output_member_l {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B C W ω w e t₀ t₁ t₂ a n k : Term ℒ [] Δ .set) (y : Term ℒ Γ Δ .set)
    (h : (output_m φ B C W ω w e t₀ t₁ t₂ a n k y).satisfies η) :
    mem_l hℳ (y.eval η) (W.eval (parameters_l η)) := by
  simpa only [SecondOrderObjectSyntax.member_m, Formula.satisfies, Arguments.eval,
    embed_l, Term.eval, SecondOrderQuotient.structure_l] using h.1

theorem run_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B β C W ω w N Q e t₀ t₁ t₂ a n k : Term ℒ [] Δ .set) (y : Term ℒ Γ Δ .set)
    (h : guard_l φ (parameters_l η) (B.eval (parameters_l η)) (β.eval (parameters_l η))
      (C.eval (parameters_l η)) (W.eval (parameters_l η)) (ω.eval (parameters_l η))
      (w.eval (parameters_l η)) (N.eval (parameters_l η)) (Q.eval (parameters_l η))
      (e.eval (parameters_l η)) (t₀.eval (parameters_l η)) (t₁.eval (parameters_l η))
      (t₂.eval (parameters_l η)) (a.eval (parameters_l η)) (n.eval (parameters_l η))) :
    (PowerlessRelativeFiniteProgramRunBounded.run_m φ B C W ω w e t₀ t₁ t₂ a n k y).satisfies η ↔
      PowerlessRelativeFiniteProgramOutput.run_l
        (PowerlessRelativeFiniteProgramExecution.relation_m φ B C ω w e t₀ t₁ t₂) (parameters_l η)
        (B.eval (parameters_l η)) (ω.eval (parameters_l η)) (e.eval (parameters_l η))
        (a.eval (parameters_l η)) (n.eval (parameters_l η)) (k.eval (parameters_l η)) (y.eval η) := by
  obtain ⟨hB, hβ, hW, hBW, hC, hCW, hω, hωW, hwW, he, ha, hw, ht, hφ, hφW, hn⟩ := h
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  have heEq : e.eval (parameters_l η) = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val :=
    SecondOrderQuotient.ext_l hℳ _ _ (fun x => iff_of_false (he x) (PowerlessBMSQuotientSuccessor.zero_l K x))
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hB hW
  have heω : mem_l hℳ (e.eval (parameters_l η)) (ω.eval (parameters_l η)) := by
    rw [heEq, hωEq]
    exact (numberCode_l K (SecondOrderModel.zero_l ℳ)).property
  have heW := hTrans _ hωW _ heω
  rw [PowerlessRelativeFiniteProgramRunBounded.run_formula_l K φ η B β C W ω w e t₀ t₁ t₂ a n k y
    hB hβ hW hBW hCW hwW heW (hωEq ▸ hn) hφW]
  constructor
  · exact PowerlessRelativeFiniteProgramLimitRun.forget_l _ (parameters_l η) hW
  · intro hy
    exact (PowerlessRelativeFiniteProgramLimitRun.refine_l K φ (parameters_l η)
      B β W C ω w N Q e t₀ t₁ t₂ a n k hB hβ hW hBW hC hCW hω hωW he ha hw ht hφ hφW hn hy).2

theorem output_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B β C W ω w N Q e t₀ t₁ t₂ a n k : Term ℒ [] Δ .set) (y : Term ℒ Γ Δ .set)
    (h : guard_l φ (parameters_l η) (B.eval (parameters_l η)) (β.eval (parameters_l η))
      (C.eval (parameters_l η)) (W.eval (parameters_l η)) (ω.eval (parameters_l η))
      (w.eval (parameters_l η)) (N.eval (parameters_l η)) (Q.eval (parameters_l η))
      (e.eval (parameters_l η)) (t₀.eval (parameters_l η)) (t₁.eval (parameters_l η))
      (t₂.eval (parameters_l η)) (a.eval (parameters_l η)) (n.eval (parameters_l η))) :
    (output_m φ B C W ω w e t₀ t₁ t₂ a n k y).satisfies η ↔
      PowerlessRelativeFiniteProgramOutput.output_l
        (PowerlessRelativeFiniteProgramExecution.relation_m φ B C ω w e t₀ t₁ t₂) (parameters_l η)
        (B.eval (parameters_l η)) (ω.eval (parameters_l η)) (e.eval (parameters_l η))
        (a.eval (parameters_l η)) (n.eval (parameters_l η)) (k.eval (parameters_l η)) (y.eval η) := by
  let ψ := PowerlessRelativeFiniteProgramExecution.relation_m φ B C ω w e t₀ t₁ t₂
  have hRun := run_formula_l K φ η B β C W ω w N Q e t₀ t₁ t₂ a n k y h
  have hAt (z : type_l hℳ) := run_formula_l K φ (η.pushBound z)
    B β C W ω w N Q e t₀ t₁ t₂ a n k (.bvar .here)
    (by simpa only [parameters_pushBound_l] using h)
  obtain ⟨hB, hβ, hW, hBW, hC, hCW, hω, hωW, hwW, he, ha, hw, ht, hφ, hφW, hn⟩ := h
  have hBound (z : type_l hℳ)
      (hz : PowerlessRelativeFiniteProgramOutput.run_l ψ (parameters_l η)
        (B.eval (parameters_l η)) (ω.eval (parameters_l η)) (e.eval (parameters_l η))
        (a.eval (parameters_l η)) (n.eval (parameters_l η)) (k.eval (parameters_l η)) z) :
      mem_l hℳ z (W.eval (parameters_l η)) :=
    (PowerlessRelativeFiniteProgramLimitRun.refine_l K φ (parameters_l η)
      B β W C ω w N Q e t₀ t₁ t₂ a n k hB hβ hW hBW hC hCW hω hωW he ha hw ht hφ hφW hn hz).1
  have hSome : (∃ z, mem_l hℳ z (W.eval (parameters_l η)) ∧
      (PowerlessRelativeFiniteProgramRunBounded.run_m φ B C W ω w e t₀ t₁ t₂ a n k
        (.bvar .here)).satisfies (η.pushBound z)) ↔
      ∃ z, PowerlessRelativeFiniteProgramOutput.run_l ψ (parameters_l η)
        (B.eval (parameters_l η)) (ω.eval (parameters_l η)) (e.eval (parameters_l η))
        (a.eval (parameters_l η)) (n.eval (parameters_l η)) (k.eval (parameters_l η)) z := by
    constructor
    · rintro ⟨z, _, hz⟩
      exact ⟨z, (hAt z).mp hz⟩
    · rintro ⟨z, hz⟩
      exact ⟨z, hBound z hz, (hAt z).mpr hz⟩
  simp only [output_m, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, SecondOrderObjectSyntax.member_m,
    Arguments.eval, Term.eval_weakenBound, embed_l, Term.eval]
  change (mem_l hℳ (y.eval η) (W.eval (parameters_l η)) ∧
    ((PowerlessRelativeFiniteProgramRunBounded.run_m φ B C W ω w e t₀ t₁ t₂ a n k y).satisfies η ∨
      ((¬∃ z, mem_l hℳ z (W.eval (parameters_l η)) ∧
        (PowerlessRelativeFiniteProgramRunBounded.run_m φ B C W ω w e t₀ t₁ t₂ a n k
          (.bvar .here)).satisfies (η.pushBound z)) ∧ y.eval η = B.eval (parameters_l η)))) ↔ _
  rw [hRun, hSome]
  constructor
  · rintro ⟨hy, hz⟩
    exact ⟨⟨β.eval (parameters_l η), W.eval (parameters_l η), hW, hy⟩, hz⟩
  · rintro ⟨_, hz⟩
    refine ⟨?_, hz⟩
    rcases hz with hz | ⟨_, hz⟩
    · exact hBound _ hz
    · exact hz.symm ▸ hBW

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β C W ω w N Q e t₀ t₁ t₂ a n k y : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  let ψ := PowerlessRelativeFiniteProgramExecution.relation_m φ B C ω w e t₀ t₁ t₂
  .imp (guard_m φ B β C W ω w N Q e t₀ t₁ t₂ a n) <|
    .conj (.iff (PowerlessRelativeFiniteProgramRunBounded.run_m φ B C W ω w e t₀ t₁ t₂ a n k y)
      (PowerlessRelativeFiniteProgramOutput.run_m ψ B ω e a n k y)) <|
        .iff (output_m φ B C W ω w e t₀ t₁ t₂ a n k y)
          (PowerlessRelativeFiniteProgramOutput.output_m ψ B ω e a n k y)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β C W ω w N Q e t₀ t₁ t₂ a n k y : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B β C W ω w N Q e t₀ t₁ t₂ a n k y)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (B β C W ω w N Q e t₀ t₁ t₂ a n k y : Term ℒ [] Δ .set) :
    (sentence_m φ B β C W ω w N Q e t₀ t₁ t₂ a n k y).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, guard_formula_l K,
    PowerlessRelativeFiniteProgramOutput.run_formula_l K, PowerlessRelativeFiniteProgramOutput.output_formula_l K]
  intro η h
  have h' : guard_l φ (parameters_l η) (B.eval (parameters_l η)) (β.eval (parameters_l η))
      (C.eval (parameters_l η)) (W.eval (parameters_l η)) (ω.eval (parameters_l η))
      (w.eval (parameters_l η)) (N.eval (parameters_l η)) (Q.eval (parameters_l η))
      (e.eval (parameters_l η)) (t₀.eval (parameters_l η)) (t₁.eval (parameters_l η))
      (t₂.eval (parameters_l η)) (a.eval (parameters_l η)) (n.eval (parameters_l η)) := by
    simpa only [parameters_empty_l] using h
  exact ⟨run_formula_l K φ η B β C W ω w N Q e t₀ t₁ t₂ a n k y h',
    output_formula_l K φ η B β C W ω w N Q e t₀ t₁ t₂ a n k y h'⟩

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β C W ω w N Q e t₀ t₁ t₂ a n k y : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B β C W ω w N Q e t₀ t₁ t₂ a n k y)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 φ B β C W ω w N Q e t₀ t₁ t₂ a n k y)

#print axioms output_delta_l
#print axioms output_member_l
#print axioms run_formula_l
#print axioms output_formula_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramOutputBounded
