import BMSConstructibleBridge.PowerlessRelativeFiniteProgramEvaluationGraph
import BMSConstructibleBridge.PowerlessRelativeClassFunctionGraph

/-! # 实际程序码域上的 Class 求值函数

原码域允许空词和无有效输出坐标；原总化求值定理仍给每码唯一输出。
将这个总单值性用于 Class 内 Δ₀ 函数图构造，再以实际精确像改换陪域。
结论包括干净集合函数、全原商图读数和精确像，不从宿主函数选取图。
本模块仍需实际算子与层守卫；可数性、凝聚与完整 Collection 未在此假定。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramEvaluationFunction

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessBMSQuotientSubsetImageDerives
  (parameters_l parameters_pushBound_l parameters_empty_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem total_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B β C W ω Q e t₀ t₁ t₂ a S P : Term ℒ [] Δ .set)
    (h : PowerlessRelativeFiniteProgramEvaluationBounded.guard_l φ η
      (B.eval η) (β.eval η) (C.eval η) (W.eval η) (ω.eval η) (Q.eval η)
      (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η))
    (hDomain : PowerlessRelativeFiniteProgramDomain.domain_l
      (B.eval η) (ω.eval η) (Q.eval η) (S.eval η) (P.eval η)) :
    ∀ p, mem_l hℳ p (P.eval η) → ∃! y,
      PowerlessRelativeFiniteProgramEvaluation.matrix_l false φ η
        (B.eval η) (C.eval η) (ω.eval η) (Q.eval η) (e.eval η)
        (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) p y := by
  obtain ⟨hB, _, _, _, hC, _, hω, _, _, he, ha, ht, hφ, _⟩ := h
  intro p hp
  have h₀ := PowerlessRelativeFiniteProgramEvaluation.result_l K φ (η.pushBound p)
    (up B) (up C) (up ω) (up Q) (up e) (up t₀) (up t₁) (up t₂) (up a) (.bvar .here)
    (by simpa only [up, Term.eval_weakenBound] using hB)
    (by simpa only [up, Term.eval_weakenBound] using hC)
    (by simpa only [up, Term.eval_weakenBound] using hω)
    (by simpa only [up, Term.eval_weakenBound] using he)
    (by simpa only [up, Term.eval_weakenBound] using ha)
    (by simpa only [up, Term.eval_weakenBound] using ht)
    (by simpa only [up, Term.eval_weakenBound, parameters_pushBound_l, parameters_empty_l] using hφ)
    (by simpa only [up, Term.eval_weakenBound] using hDomain)
    (by simpa only [Term.eval, Env.pushBound_bound_here] using hp)
  simpa only [up, Term.eval_weakenBound, parameters_pushBound_l, parameters_empty_l,
    Term.eval, Env.pushBound_bound_here] using h₀.1

variable {A : type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x A → ∀ y, mem_l hℳ y x → mem_l hℳ y A}

private theorem term_l {Δ : SortContext ℒ}
    (η : Env (PowerlessRelativeClassStructure.structure_l hℳ A hBase) [] Δ)
    (t : Term ℒ [] Δ .set) :
    t.eval (PowerlessRelativeClassRelativization.env_l η) = (t.eval η).val := by
  match t with
  | .bvar v => nomatch v
  | .fvar _ => rfl
  | .app f _ => nomatch f

theorem exists_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    {φ : Formula ℒ [] (.set :: .set :: Δ)} (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (η : Env (PowerlessRelativeClassStructure.structure_l hℳ A hBase) [] Δ)
    (B β C W ω Q e t₀ t₁ t₂ a S P : Term ℒ [] Δ .set)
    (h : let ξ := PowerlessRelativeClassRelativization.env_l η
      PowerlessRelativeFiniteProgramEvaluationBounded.guard_l φ ξ
        (B.eval ξ) (β.eval ξ) (C.eval ξ) (W.eval ξ) (ω.eval ξ) (Q.eval ξ)
        (e.eval ξ) (t₀.eval ξ) (t₁.eval ξ) (t₂.eval ξ) (a.eval ξ))
    (hDomain : let ξ := PowerlessRelativeClassRelativization.env_l η
      PowerlessRelativeFiniteProgramDomain.domain_l
        (B.eval ξ) (ω.eval ξ) (Q.eval ξ) (S.eval ξ) (P.eval ξ)) :
    let ξ := PowerlessRelativeClassRelativization.env_l η
    ∃ G I : PowerlessRelativeClassStructure.type_l hℳ A,
      map_l (ℳ := 𝒱) G.val (P.eval ξ) I.val ∧
      (∀ p y : type_l hℳ, value_l (ℳ := 𝒱) G.val p y ↔
        mem_l hℳ p (P.eval ξ) ∧ PowerlessRelativeFiniteProgramEvaluation.matrix_l false φ ξ
          (B.eval ξ) (C.eval ξ) (ω.eval ξ) (Q.eval ξ) (e.eval ξ)
          (t₀.eval ξ) (t₁.eval ξ) (t₂.eval ξ) (a.eval ξ) p y) ∧
      (∀ y : type_l hℳ, mem_l hℳ y I.val ↔ ∃ p, mem_l hℳ p (P.eval ξ) ∧
        PowerlessRelativeFiniteProgramEvaluation.matrix_l false φ ξ
          (B.eval ξ) (C.eval ξ) (ω.eval ξ) (Q.eval ξ) (e.eval ξ)
          (t₀.eval ξ) (t₁.eval ξ) (t₂.eval ξ) (a.eval ξ) p y) := by
  let ξ := PowerlessRelativeClassRelativization.env_l η
  let ψ := PowerlessRelativeFiniteProgramEvaluationGraph.relation_m φ B C W ω Q e t₀ t₁ t₂ a
  have hψ := PowerlessRelativeFiniteProgramEvaluationGraph.relation_delta_l hφ B C W ω Q e t₀ t₁ t₂ a
  have hReadClass (p y : PowerlessRelativeClassStructure.type_l hℳ A) :
      ψ.satisfies ((η.pushFree y).pushFree p) ↔
        PowerlessRelativeFiniteProgramEvaluation.matrix_l false φ ξ
          (B.eval ξ) (C.eval ξ) (ω.eval ξ) (Q.eval ξ) (e.eval ξ)
          (t₀.eval ξ) (t₁.eval ξ) (t₂.eval ξ) (a.eval ξ) p.val y.val := by
    have hEnv : PowerlessRelativeClassRelativization.env_l ((η.pushFree y).pushFree p) =
        ((ξ.pushFree (sort := SetTheory.SetSort.set) y.val).pushFree
          (sort := SetTheory.SetSort.set) p.val) := by
      apply Env.ext
      · intro s v; nomatch v
      · intro s v
        cases s
        cases v with
        | here => rfl
        | there v => cases v <;> rfl
    have hAbsolute := PowerlessRelativeClassBounded.formula_l hψ ((η.pushFree y).pushFree p)
    rw [hEnv] at hAbsolute
    exact hAbsolute.trans (PowerlessRelativeFiniteProgramEvaluationGraph.relation_formula_l
      K φ ξ B β C W ω Q e t₀ t₁ t₂ a h p.val y.val)
  have hTotal (p : PowerlessRelativeClassStructure.type_l hℳ A)
      (hp : mem_l hℳ p.val (P.eval η).val) : ∃! y : PowerlessRelativeClassStructure.type_l hℳ A,
        mem_l hℳ y.val (W.eval η).val ∧ ψ.satisfies ((η.pushFree y).pushFree p) := by
    obtain ⟨y, hy, hUnique⟩ := total_l K φ ξ B β C W ω Q e t₀ t₁ t₂ a S P h hDomain
      p.val (by simpa only [ξ, term_l] using hp)
    have hyW := PowerlessRelativeFiniteProgramEvaluationGraph.output_member_l
      K φ ξ B β C W ω Q e t₀ t₁ t₂ a h p.val y hy
    let y' : PowerlessRelativeClassStructure.type_l hℳ A := ⟨y,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase (W.eval η).property
        (by simpa only [ξ, term_l] using hyW)⟩
    refine ⟨y', ⟨by simpa only [ξ, term_l] using hyW, (hReadClass p y').mpr hy⟩, ?_⟩
    rintro z ⟨_, hz⟩
    exact Subtype.ext (hUnique z.val ((hReadClass p z).mp hz))
  obtain ⟨G, hG, hGraph⟩ := PowerlessRelativeClassFunctionGraph.exists_l
    hψ η (P.eval η) (W.eval η) hTotal
  have hMap : map_l (ℳ := 𝒱) G.val (P.eval ξ) (W.eval ξ) := by
    simpa only [ξ, term_l] using hG
  have hRead (p y : type_l hℳ) : value_l (ℳ := 𝒱) G.val p y ↔
      mem_l hℳ p (P.eval ξ) ∧ PowerlessRelativeFiniteProgramEvaluation.matrix_l false φ ξ
        (B.eval ξ) (C.eval ξ) (ω.eval ξ) (Q.eval ξ) (e.eval ξ)
        (t₀.eval ξ) (t₁.eval ξ) (t₂.eval ξ) (a.eval ξ) p y := by
    rw [hGraph p y, ← term_l η P, ← term_l η W]
    rw [PowerlessRelativeFiniteProgramEvaluationGraph.relation_formula_l
      K φ ξ B β C W ω Q e t₀ t₁ t₂ a h p y]
    constructor
    · rintro ⟨hp, _, hy⟩; exact ⟨hp, hy⟩
    · rintro ⟨hp, hy⟩
      exact ⟨hp, PowerlessRelativeFiniteProgramEvaluationGraph.output_member_l
        K φ ξ B β C W ω Q e t₀ t₁ t₂ a h p y hy, hy⟩
  obtain ⟨I, hI⟩ := PowerlessRelativeClassSelectedImage.exists_l
    (hBase := hBase) G (P.eval η) (W.eval η)
  have hImage (y : type_l hℳ) : mem_l hℳ y I.val ↔ ∃ p, mem_l hℳ p (P.eval ξ) ∧
      PowerlessRelativeFiniteProgramEvaluation.matrix_l false φ ξ
        (B.eval ξ) (C.eval ξ) (ω.eval ξ) (Q.eval ξ) (e.eval ξ)
        (t₀.eval ξ) (t₁.eval ξ) (t₂.eval ξ) (a.eval ξ) p y := by
    rw [hI y, ← term_l η W, ← term_l η P]
    constructor
    · rintro ⟨_, p, hp, hpy⟩
      exact ⟨p, hp, ((hRead p y).mp hpy).2⟩
    · rintro ⟨p, hp, hy⟩
      exact ⟨PowerlessRelativeFiniteProgramEvaluationGraph.output_member_l
        K φ ξ B β C W ω Q e t₀ t₁ t₂ a h p y hy,
          p, hp, (hRead p y).mpr ⟨hp, hy⟩⟩
  refine ⟨G, I, ⟨?_, ?_⟩, hRead, hImage⟩
  · intro q hq
    obtain ⟨p, y, hp, _, hpy⟩ := hMap.1 q hq
    exact ⟨p, y, hp, (hImage y).mpr ⟨p, hp, ((hRead p y).mp ⟨q, hq, hpy⟩).2⟩, hpy⟩
  · intro p hp
    obtain ⟨y, ⟨_, hpy⟩, hUnique⟩ := hMap.2 p hp
    refine ⟨y, ⟨(hImage y).mpr ⟨p, hp, ((hRead p y).mp hpy).2⟩, hpy⟩, ?_⟩
    rintro z ⟨_, hpz⟩
    exact hUnique z ⟨PowerlessRelativeFiniteProgramEvaluationGraph.output_member_l
      K φ ξ B β C W ω Q e t₀ t₁ t₂ a h p z ((hRead p z).mp hpz).2, hpz⟩

def conclusion_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a P : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .existsE .set <| .existsE .set <|
    let G := .bvar (.there .here)
    let I := .bvar .here
    .conj (PowerlessRelativeHierarchySyntax.class_m (up₂ B) G) <|
      .conj (PowerlessRelativeHierarchySyntax.class_m (up₂ B) I) <|
        .conj (SecondOrderObjectSyntax.map_m G (up₂ P) I) <|
          .conj (PowerlessRelativeFiniteProgramEvaluationGraph.reading_m φ
            (up₂ B) (up₂ C) (up₂ ω) (up₂ Q) (up₂ e) (up₂ t₀) (up₂ t₁) (up₂ t₂) (up₂ a) (up₂ P) G)
            (PowerlessRelativeFiniteProgramEvaluationGraph.image_m φ
              (up₂ B) (up₂ C) (up₂ ω) (up₂ Q) (up₂ e) (up₂ t₀) (up₂ t₁) (up₂ t₂) (up₂ a) (up₂ P) I)

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β C W ω Q e t₀ t₁ t₂ a S P : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_m Δ B (fun v => .fvar v)) <|
    .imp (PowerlessRelativeFiniteProgramEvaluationBounded.guard_m φ B β C W ω Q e t₀ t₁ t₂ a) <|
      .imp (PowerlessRelativeFiniteProgramDomain.domain_m B ω Q S P)
        (conclusion_m φ B C ω Q e t₀ t₁ t₂ a P)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β C W ω Q e t₀ t₁ t₂ a S P : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B β C W ω Q e t₀ t₁ t₂ a S P)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    {φ : Formula ℒ [] (.set :: .set :: Δ)} (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (B β C W ω Q e t₀ t₁ t₂ a S P : Term ℒ [] Δ .set) :
    (sentence_m φ B β C W ω Q e t₀ t₁ t₂ a S P).TrueIn
      (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro ζ hParams hGuard hDomain
  have hParams' := (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_formula_l
    K Δ ζ B (fun v => .fvar v)).mp hParams
  have hGuard' := (PowerlessRelativeFiniteProgramEvaluationBounded.guard_formula_l K
    φ ζ B β C W ω Q e t₀ t₁ t₂ a).mp hGuard
  have hDomain' := (PowerlessRelativeFiniteProgramDomain.domain_formula_l K ζ B ω Q S P).mp hDomain
  have hBase := hGuard'.1
  let η : Env (PowerlessRelativeClassStructure.structure_l h𝒩 (B.eval ζ) hBase) [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with
        | .set => ⟨ζ.freeVal v, hParams' _ v⟩ }
  have hη : PowerlessRelativeClassRelativization.env_l η = ζ := by
    apply Env.ext
    · intro s v; nomatch v
    · intro s v; cases s; rfl
  obtain ⟨G, I, hMap, hRead, hImage⟩ := exists_l (hBase := hBase) K hφ η
    B β C W ω Q e t₀ t₁ t₂ a S P
    (by simpa only [hη, parameters_empty_l] using hGuard')
    (by simpa only [hη] using hDomain')
  simp only [conclusion_m, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.class_formula_l K, map_formula_l,
    PowerlessRelativeFiniteProgramEvaluationGraph.reading_formula_l K,
    PowerlessRelativeFiniteProgramEvaluationGraph.image_formula_l K,
    parameters_pushBound_l, parameters_empty_l, up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  refine ⟨G.val, I.val, G.property, I.property, ?_, ?_, ?_⟩
  · simpa only [hη] using hMap
  · simpa only [hη, ThirdOrderSemantics.carrier_l, SecondOrderQuotient.structure_l] using hRead
  · simpa only [hη] using hImage

theorem derives_m {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (B β C W ω Q e t₀ t₁ t₂ a S P : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B β C W ω Q e t₀ t₁ t₂ a S P)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ h𝒩 => models_l h𝒩 hφ B β C W ω Q e t₀ t₁ t₂ a S P)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramEvaluationFunction
