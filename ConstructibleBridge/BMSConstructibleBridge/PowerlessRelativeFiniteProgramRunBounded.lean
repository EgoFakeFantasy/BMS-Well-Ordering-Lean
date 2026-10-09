import BMSConstructibleBridge.PowerlessRelativeFiniteProgramTraceBounded
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramLimitRun

/-! # 全六见证真正有界的程序读数

原 LimitRun 给全部见证属于 W，本模块进一步将历史、末态有效性和
读数正文全部改写为纯有界检查。自由参数和算子首两槽保持原位。
等价出口回到同一原 run；Δ₀ 分类仍以实际算子正文的 Δ₀ 证书为前提。
不由单个 run 的存在推断整个求值像是集合。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramRunBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)
open PowerlessBMSQuotientSubsetImageDerives
  (parameters_l parameters_pushBound_l parameters_empty_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private def binding_m {Γ Δ : SortContext ℒ} : Substitution ℒ [] Δ Γ Δ :=
  .map (fun v => nomatch v) (fun v => .fvar v)
private def embed_m {Γ Δ : SortContext ℒ} (t : Term ℒ [] Δ .set) : Term ℒ Γ Δ .set :=
  t.substitute binding_m
private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up (up t))
private abbrev up₆ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up₃ (up₃ t)

def body_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C W ω w e t₀ t₁ t₂ a n k : Term ℒ [] Δ .set)
    (S D F s E g y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessRelativeFiniteProgramTraceBounded.trace_m φ B C W ω w e t₀ t₁ t₂
    (embed_m a) (embed_m n) S D F (embed_m e)) <|
      .conj (PowerlessValueBounded.formula_m F (embed_m n) s) <|
        .conj (PowerlessRelativeFiniteProgramStateBounded.valid_m
          (embed_m W) (embed_m ω) (embed_m n) E g s)
            (PowerlessValueBounded.formula_m g (embed_m k) y)

def run_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C W ω w e t₀ t₁ t₂ a n k : Term ℒ [] Δ .set) (y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists (embed_m W) <|
    membershipLevyBound.boundedExists (embed_m W) <|
      membershipLevyBound.boundedExists (embed_m W) <|
        membershipLevyBound.boundedExists (embed_m W) <|
          membershipLevyBound.boundedExists (embed_m W) <|
            membershipLevyBound.boundedExists (embed_m W) <|
              body_m φ B C W ω w e t₀ t₁ t₂ a n k
                (.bvar (.there (.there (.there (.there (.there .here))))))
                (.bvar (.there (.there (.there (.there .here)))))
                (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here)))
                (.bvar (.there .here)) (.bvar .here) (up₆ y)

theorem body_delta_l {Γ Δ : SortContext ℒ}
    {φ : Formula ℒ [] (.set :: .set :: Δ)} (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (B C W ω w e t₀ t₁ t₂ a n k : Term ℒ [] Δ .set) (S D F s E g y : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (body_m φ B C W ω w e t₀ t₁ t₂ a n k S D F s E g y) :=
  .conj (PowerlessRelativeFiniteProgramTraceBounded.trace_delta_l hφ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) <|
    .conj (PowerlessValueBounded.delta_l _ _ _) <|
      .conj (PowerlessRelativeFiniteProgramStateBounded.valid_delta_l _ _ _ _ _ _)
        (PowerlessValueBounded.delta_l _ _ _)

theorem run_delta_l {Γ Δ : SortContext ℒ}
    {φ : Formula ℒ [] (.set :: .set :: Δ)} (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (B C W ω w e t₀ t₁ t₂ a n k : Term ℒ [] Δ .set) (y : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (run_m φ B C W ω w e t₀ t₁ t₂ a n k y) :=
  .bounded_exists (embed_m W) <| .bounded_exists (embed_m W) <|
    .bounded_exists (embed_m W) <| .bounded_exists (embed_m W) <|
      .bounded_exists (embed_m W) <| .bounded_exists (embed_m W) <|
        body_delta_l hφ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

private theorem embed_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ) (t : Term ℒ [] Δ .set) :
    (embed_m t).eval η = t.eval (parameters_l η) := by
  rw [embed_m, Term.eval_substitute]
  apply congrArg (fun ξ => t.eval ξ)
  apply Env.ext
  · intro s v; nomatch v
  · intro s v; rfl

theorem run_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B β C W ω w e t₀ t₁ t₂ a n k : Term ℒ [] Δ .set) (y : Term ℒ Γ Δ .set)
    (hB : ∀ x, mem_l hℳ x (B.eval (parameters_l η)) →
      ∀ z, mem_l hℳ z x → mem_l hℳ z (B.eval (parameters_l η)))
    (hβ : limit_l hℳ (β.eval (parameters_l η)))
    (hW : level_l hℳ (B.eval (parameters_l η)) (β.eval (parameters_l η)) (W.eval (parameters_l η)))
    (hBW : mem_l hℳ (B.eval (parameters_l η)) (W.eval (parameters_l η)))
    (hC : ∀ x, mem_l hℳ x (C.eval (parameters_l η)) → mem_l hℳ x (W.eval (parameters_l η)))
    (hw : mem_l hℳ (w.eval (parameters_l η)) (W.eval (parameters_l η)))
    (he : mem_l hℳ (e.eval (parameters_l η)) (W.eval (parameters_l η)))
    (hn : mem_l hℳ (n.eval (parameters_l η)) K.omega)
    (hφ : PowerlessRelativeFiniteProgramLimitStep.closed_l φ (parameters_l η)
      (B.eval (parameters_l η)) (W.eval (parameters_l η))) :
    (run_m φ B C W ω w e t₀ t₁ t₂ a n k y).satisfies η ↔
      PowerlessRelativeFiniteProgramLimitRun.run_l
        (PowerlessRelativeFiniteProgramExecution.relation_m φ B C ω w e t₀ t₁ t₂) (parameters_l η)
        (B.eval (parameters_l η)) (ω.eval (parameters_l η)) (W.eval (parameters_l η))
        (e.eval (parameters_l η)) (a.eval (parameters_l η)) (n.eval (parameters_l η))
        (k.eval (parameters_l η)) (y.eval η) := by
  have hBody {Θ : SortContext ℒ} (ξ : Env 𝒱 Θ Δ)
      (hξ : parameters_l ξ = parameters_l η) (S D F s E g z : Term ℒ Θ Δ .set)
      (hD : mem_l hℳ (D.eval ξ) (W.eval (parameters_l η)))
      (hs : mem_l hℳ (s.eval ξ) (W.eval (parameters_l η))) :
      (body_m φ B C W ω w e t₀ t₁ t₂ a n k S D F s E g z).satisfies ξ ↔
        PowerlessDefinableFiniteTrace.trace_l
          (PowerlessRelativeFiniteProgramExecution.relation_m φ B C ω w e t₀ t₁ t₂) (parameters_l η)
          (e.eval (parameters_l η)) (a.eval (parameters_l η)) (n.eval (parameters_l η))
          (S.eval ξ) (D.eval ξ) (F.eval ξ) ∧
          value_l (ℳ := 𝒱) (F.eval ξ) (n.eval (parameters_l η)) (s.eval ξ) ∧
          PowerlessRelativeFiniteProgramStep.valid_l (B.eval (parameters_l η)) (ω.eval (parameters_l η))
            (n.eval (parameters_l η)) (E.eval ξ) (g.eval ξ) (s.eval ξ) ∧
          value_l (ℳ := 𝒱) (g.eval ξ) (k.eval (parameters_l η)) (z.eval ξ) := by
    have hTrace := PowerlessRelativeFiniteProgramTraceBounded.trace_formula_l K φ ξ
      B β C W ω w e t₀ t₁ t₂ (embed_m a) (embed_m n) S D F (embed_m e)
      (by simpa only [hξ] using hB) (by simpa only [hξ] using hβ)
      (by simpa only [hξ] using hW) (by simpa only [hξ] using hBW)
      (by simpa only [hξ] using hC) (by simpa only [hξ] using hw)
      (by simpa only [hξ] using he) (by simpa only [hξ] using hD)
      (by simpa only [embed_l, hξ] using hn) (by simpa only [hξ] using hφ)
    have hValid := PowerlessRelativeFiniteProgramStateBounded.valid_formula_l ξ
      (embed_m B) (embed_m β) (embed_m W) (embed_m ω) (embed_m n) E g s
      (by simpa only [embed_l, hξ] using hB)
      (by simpa only [embed_l, hξ] using hW) (by simpa only [embed_l, hξ] using hs)
    simp only [body_m, Formula.satisfies, PowerlessValueBounded.formula_l]
    simpa only [embed_l, hξ] using and_congr hTrace (and_congr Iff.rfl (and_congr hValid Iff.rfl))
  let S : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
    .bvar (.there (.there (.there (.there (.there .here)))))
  let D : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
    .bvar (.there (.there (.there (.there .here))))
  let F : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
    .bvar (.there (.there (.there .here)))
  let s : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
    .bvar (.there (.there .here))
  let E : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
    .bvar (.there .here)
  let g : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set := .bvar .here
  simp only [run_m, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, Arguments.eval, Term.eval_weakenBound,
    embed_l, parameters_pushBound_l, Term.eval]
  change (∃ T, mem_l hℳ T (W.eval (parameters_l η)) ∧
    ∃ A, mem_l hℳ A (W.eval (parameters_l η)) ∧ ∃ H, mem_l hℳ H (W.eval (parameters_l η)) ∧
    ∃ v, mem_l hℳ v (W.eval (parameters_l η)) ∧ ∃ P, mem_l hℳ P (W.eval (parameters_l η)) ∧
    ∃ G, mem_l hℳ G (W.eval (parameters_l η)) ∧
      (body_m φ B C W ω w e t₀ t₁ t₂ a n k S D F s E g (up₆ y)).satisfies
        ((((((η.pushBound T).pushBound A).pushBound H).pushBound v).pushBound P).pushBound G)) ↔ _
  constructor
  · rintro ⟨T, hT, A, hA, H, hH, v, hv, P, hP, G, hG, h⟩
    let ξ : Env 𝒱 (.set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ :=
      (((((η.pushBound T).pushBound A).pushBound H).pushBound v).pushBound P).pushBound G
    have h₀ := (hBody ξ rfl S D F s E g (up₆ y) hA hv).mp h
    exact ⟨T, A, H, v, P, G, hT, hA, hH, hv, hP, hG,
      by simpa only [ξ, S, D, F, s, E, g, up₆, up₃, up, Term.eval_weakenBound,
        Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there] using h₀⟩
  · rintro ⟨T, A, H, v, P, G, hT, hA, hH, hv, hP, hG, h⟩
    refine ⟨T, hT, A, hA, H, hH, v, hv, P, hP, G, hG, ?_⟩
    let ξ : Env 𝒱 (.set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ :=
      (((((η.pushBound T).pushBound A).pushBound H).pushBound v).pushBound P).pushBound G
    apply (hBody ξ rfl S D F s E g (up₆ y) hA hv).mpr
    simpa only [ξ, S, D, F, s, E, g, up₆, up₃, up, Term.eval_weakenBound,
      Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there] using h

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β C W ω w e t₀ t₁ t₂ a n k y : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.limit_m β) <|
      .imp (PowerlessRelativeHierarchySyntax.level_m B β W) <|
        .imp (SecondOrderObjectSyntax.member_m B W) <| .imp (ThirdOrderTheory.subset_m C W) <|
          .imp (SecondOrderObjectSyntax.member_m w W) <| .imp (SecondOrderObjectSyntax.member_m e W) <|
            .imp (SecondOrderOmegaSyntax.omega_m ω) <| .imp (SecondOrderObjectSyntax.member_m n ω) <|
              .imp (PowerlessRelativeFiniteProgramLimitStep.closed_m φ B W) <|
                .iff (run_m φ B C W ω w e t₀ t₁ t₂ a n k y)
                  (PowerlessRelativeFiniteProgramLimitRun.run_m
                    (PowerlessRelativeFiniteProgramExecution.relation_m φ B C ω w e t₀ t₁ t₂)
                    B ω W e a n k y)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β C W ω w e t₀ t₁ t₂ a n k y : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B β C W ω w e t₀ t₁ t₂ a n k y)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (B β C W ω w e t₀ t₁ t₂ a n k y : Term ℒ [] Δ .set) :
    (sentence_m φ B β C W ω w e t₀ t₁ t₂ a n k y).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.limit_formula_l, PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeFiniteProgramLimitStep.closed_formula_l K, subset_formula_l, SecondOrderOmegaSyntax.omega_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, PowerlessRelativeFiniteProgramLimitRun.run_formula_l K,
    parameters_empty_l]
  intro η hB hβ hW hBW hC hw he hω hn hφ
  have hωEq := SecondOrderOmega.unique_l h𝒩 hω K.omega_spec
  simpa only [parameters_empty_l] using run_formula_l K φ η B β C W ω w e t₀ t₁ t₂ a n k y
    (by simpa only [parameters_empty_l] using hB) (by simpa only [parameters_empty_l] using hβ)
    (by simpa only [parameters_empty_l] using hW) (by rw [parameters_empty_l]; exact hBW)
    (by rw [parameters_empty_l]; exact hC) (by rw [parameters_empty_l]; exact hw)
    (by rw [parameters_empty_l]; exact he) (by rw [parameters_empty_l]; exact hωEq ▸ hn)
    (by simpa only [parameters_empty_l] using hφ)

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β C W ω w e t₀ t₁ t₂ a n k y : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B β C W ω w e t₀ t₁ t₂ a n k y)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 φ B β C W ω w e t₀ t₁ t₂ a n k y)

#print axioms run_delta_l
#print axioms run_formula_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramRunBounded
