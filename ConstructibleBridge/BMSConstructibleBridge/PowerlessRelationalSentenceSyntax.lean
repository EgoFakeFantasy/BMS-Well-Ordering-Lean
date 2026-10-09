import BMSConstructibleBridge.PowerlessRelativeClassEvaluationSystem
import BMSConstructibleBridge.PowerlessRelativeParameters

/-! # 跨域闭句编译的原语言模式

源闭句是外部模式索引；对象句先量化同一数码与最小赋值长度，再量化
任意非空求值域和相应图。不引入对整类的内部统一真值谓词。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalSentenceSyntax

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderObjectSyntax (member_m map_m value_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def relative_m {Γ Δ : SortContext ℒ} (φ : Sentence ℒ) (A : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  PowerlessRelativeParameters.instance_m φ A (fun v => nomatch v)

theorem relative_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (φ : Sentence ℒ) (η : Env 𝒩 Γ Δ) (A : Term ℒ Γ Δ .set) (hA : ∃ a, member_l 𝒩 a (A.eval η)) :
    (relative_m φ A).satisfies η ↔ φ.TrueIn (PowerlessMemberStructure.structure_l (A.eval η) hA) :=
  PowerlessRelativeParameters.instance_l φ η A (fun v => nomatch v) Env.empty rfl (fun v => nomatch v)

def nonempty_m {Γ Δ : SortContext ℒ} (A : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set (member_m (.bvar .here) (up A))

theorem nonempty_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (A : Term ℒ Γ Δ .set) :
    (nonempty_m A).satisfies η ↔ ∃ a, member_l 𝒩 a (A.eval η) := by
  simp only [nonempty_m, Formula.satisfies, member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def reading_m {Γ Δ : SortContext ℒ} (φ : Sentence ℒ) (ω A G c N : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (member_m (.bvar .here) (up ω)) <|
    .imp (ThirdOrderTheory.subset_m (up N) (.bvar .here)) <|
      .forallE .set <| .imp (map_m (.bvar .here) (.bvar (.there .here)) (up (up A))) <|
        .iff (value_m (up (up G)) (up (up c)) (.bvar .here)) (relative_m φ (up (up A)))

theorem reading_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (φ : Sentence ℒ) (η : Env 𝒩 Γ Δ) (ω A G c N : Term ℒ Γ Δ .set)
    (hA : ∃ a, member_l 𝒩 a (A.eval η)) :
    (reading_m φ ω A G c N).satisfies η ↔
      ∀ m, member_l 𝒩 m (ω.eval η) → subset_l (N.eval η) m → ∀ f, map_l f m (A.eval η) →
        (value_l (G.eval η) (c.eval η) f ↔ φ.TrueIn (PowerlessMemberStructure.structure_l (A.eval η) hA)) := by
  simp only [reading_m, Formula.satisfies, map_formula_l, subset_formula_l, value_formula_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  apply forall_congr'
  intro m
  apply imp_congr_right
  intro _
  apply imp_congr_right
  intro _
  apply forall_congr'
  intro f
  apply imp_congr_right
  intro _
  have hA' : ∃ a, member_l 𝒩 a ((up (up A)).eval ((η.pushBound m).pushBound f)) := by
    simpa only [up, Term.eval_weakenBound] using hA
  have h := relative_formula_l φ ((η.pushBound m).pushBound f) (up (up A)) hA'
  simpa only [up, Term.eval_weakenBound] using iff_congr Iff.rfl h

def domain_m {Γ Δ : SortContext ℒ} (φ : Sentence ℒ)
    (ω e T t₁ t₂ t₃ c N A : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up t)
  .imp (nonempty_m A) <| .existsE .set <| .existsE .set <|
    .conj (PowerlessRelativeClassEvaluationSystem.spec_m (w ω) (w A) (w e) (w t₁) (w t₂) (w t₃)
      (w T) (.bvar (.there .here)) (.bvar .here))
      (reading_m φ (w ω) (w A) (.bvar .here) (w c) (w N))

theorem domain_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (φ : Sentence ℒ) (η : Env 𝒩 Γ Δ) (ω e T t₁ t₂ t₃ c N A : Term ℒ Γ Δ .set) :
    (domain_m φ ω e T t₁ t₂ t₃ c N A).satisfies η ↔
      ∀ hA : ∃ a, member_l 𝒩 a (A.eval η), ∃ S G,
        PowerlessRelativeClassEvaluationSystem.spec_l (ω.eval η) (A.eval η) (e.eval η)
          (t₁.eval η) (t₂.eval η) (t₃.eval η) (T.eval η) S G ∧
        ∀ m, member_l 𝒩 m (ω.eval η) → subset_l (N.eval η) m → ∀ f, map_l f m (A.eval η) →
          (value_l G (c.eval η) f ↔ φ.TrueIn (PowerlessMemberStructure.structure_l (A.eval η) hA)) := by
  simp only [domain_m, Formula.satisfies, nonempty_formula_l,
    PowerlessRelativeClassEvaluationSystem.spec_formula_l, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  apply forall_congr'
  intro hA
  apply exists_congr
  intro S
  apply exists_congr
  intro G
  have hA' : ∃ a, member_l 𝒩 a ((up (up A)).eval ((η.pushBound S).pushBound G)) := by
    simpa only [up, Term.eval_weakenBound] using hA
  have h := reading_formula_l φ ((η.pushBound S).pushBound G)
    (up (up ω)) (up (up A)) (.bvar .here) (up (up c)) (up (up N)) hA'
  simpa only [up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here] using and_congr Iff.rfl h

def codes_m {Γ Δ : SortContext ℒ} (φ : Sentence ℒ)
    (ω e T t₁ t₂ t₃ : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up (up t))
  .existsE .set <| .conj (member_m (.bvar .here) (up ω)) <|
    .existsE .set <| .conj (member_m (.bvar .here) (up (up ω))) <|
      .forallE .set <| domain_m φ (w ω) (w e) (w T) (w t₁) (w t₂) (w t₃)
        (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)

theorem codes_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (φ : Sentence ℒ) (η : Env 𝒩 Γ Δ) (ω e T t₁ t₂ t₃ : Term ℒ Γ Δ .set) :
    (codes_m φ ω e T t₁ t₂ t₃).satisfies η ↔
      ∃ c, member_l 𝒩 c (ω.eval η) ∧ ∃ N, member_l 𝒩 N (ω.eval η) ∧
        ∀ A, ∀ hA : ∃ a, member_l 𝒩 a A, ∃ S G,
          PowerlessRelativeClassEvaluationSystem.spec_l (ω.eval η) A (e.eval η)
            (t₁.eval η) (t₂.eval η) (t₃.eval η) (T.eval η) S G ∧
          ∀ m, member_l 𝒩 m (ω.eval η) → subset_l N m → ∀ f, map_l f m A →
            (value_l G c f ↔ φ.TrueIn (PowerlessMemberStructure.structure_l A hA)) := by
  simp only [codes_m, Formula.satisfies, domain_formula_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def existence_m {Γ Δ : SortContext ℒ} (φ : Sentence ℒ) (ω : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <|
    codes_m φ (up (up (up (up (up ω))))) (.bvar (.there (.there (.there (.there .here)))))
      (.bvar .here) (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here))) (.bvar (.there .here))

theorem existence_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (φ : Sentence ℒ) (η : Env 𝒩 Γ Δ) (ω : Term ℒ Γ Δ .set) :
    (existence_m φ ω).satisfies η ↔
      ∃ e t₁ t₂ t₃ T c, member_l 𝒩 c (ω.eval η) ∧ ∃ N, member_l 𝒩 N (ω.eval η) ∧
        ∀ A, ∀ hA : ∃ a, member_l 𝒩 a A, ∃ S G,
          PowerlessRelativeClassEvaluationSystem.spec_l (ω.eval η) A e t₁ t₂ t₃ T S G ∧
          ∀ m, member_l 𝒩 m (ω.eval η) → subset_l N m → ∀ f, map_l f m A →
            (value_l G c f ↔ φ.TrueIn (PowerlessMemberStructure.structure_l A hA)) := by
  simp only [existence_m, Formula.satisfies, codes_formula_l, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m {Γ Δ : SortContext ℒ} (φ : Sentence ℒ) (ω : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) (existence_m φ ω)

def sentence_m {Δ : SortContext ℒ} (φ : Sentence ℒ)
    (ω : Term ℒ [] Δ .set) : Sentence ℒ := Metatheory.Formula.forall_close (schema_m φ ω)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalSentenceSyntax
