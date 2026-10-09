import BMSConstructibleBridge.PowerlessRelativeFiniteProgramEvaluationBounded
import BMSConstructibleBridge.PowerlessRelativeClassRelationalGraph
import BMSConstructibleBridge.PowerlessRelativeClassSelectedImage

/-! # 全部有界程序求值的实际 Class 图与精确像

先把绑定的代码／输出槽开放为关系的输入／输出槽，再在实际 Class 中
使用 Δ₀ 图存在定理。输出成员守卫消去外加的 W 限制，精确像的读数
量化全部原商对象。这里构造整张图与整个像，而非逐个输出的宿主集合。
算子 Δ₀ 和保层守卫仍须由实际有限公式族实例提供；不宣称已经完成凝聚、
完整 cutoff Collection 或 BMS 的最终推导。图的全域单值性另由码域验证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramEvaluationGraph

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

/-- 关系首槽是代码，次槽是输出；算子本身的首两槽不交换。 -/
def relation_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C W ω Q e t₀ t₁ t₂ a : Term ℒ [] Δ .set) : Formula ℒ [] (.set :: .set :: Δ) :=
  PowerlessSourceOpening.form_m <|
    PowerlessRelativeFiniteProgramEvaluationBounded.matrix_m false φ
      (up₂ B) (up₂ C) (up₂ W) (up₂ ω) (up₂ Q) (up₂ e)
      (up₂ t₀) (up₂ t₁) (up₂ t₂) (up₂ a) (.bvar .here) (.bvar (.there .here))

theorem relation_delta_l {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (B C W ω Q e t₀ t₁ t₂ a : Term ℒ [] Δ .set) :
    Formula.IsDelta0 membershipLevyBound (relation_m φ B C W ω Q e t₀ t₁ t₂ a) := by
  unfold relation_m PowerlessSourceOpening.form_m PowerlessSourceOpening.binding_m
  exact Formula.IsDelta0.substituteMapped
    (boundSubstitution := _) (freeSubstitution := _)
    (PowerlessRelativeFiniteProgramEvaluationBounded.matrix_delta_l false hφ
      _ _ _ _ _ _ _ _ _ _ _ _)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

private theorem opening_l {Δ : SortContext ℒ} (η : Env 𝒱 [] Δ) (p y : type_l hℳ) :
    PowerlessSourceOpening.env_l ((η.pushBound (sort := SetTheory.SetSort.set) y).pushBound
      (sort := SetTheory.SetSort.set) p) =
      (η.pushFree (sort := SetTheory.SetSort.set) y).pushFree (sort := SetTheory.SetSort.set) p := by
  have hη : PowerlessSourceOpening.env_l η = η := by
    apply Env.ext
    · intro s v; nomatch v
    · intro s v; rfl
  rw [PowerlessSourceOpening.push_l, PowerlessSourceOpening.push_l, hη]

theorem relation_formula_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B β C W ω Q e t₀ t₁ t₂ a : Term ℒ [] Δ .set)
    (h : PowerlessRelativeFiniteProgramEvaluationBounded.guard_l φ η
      (B.eval η) (β.eval η) (C.eval η) (W.eval η) (ω.eval η) (Q.eval η)
      (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η)) (p y : type_l hℳ) :
    (relation_m φ B C W ω Q e t₀ t₁ t₂ a).satisfies ((η.pushFree y).pushFree p) ↔
      PowerlessRelativeFiniteProgramEvaluation.matrix_l false φ η
        (B.eval η) (C.eval η) (ω.eval η) (Q.eval η) (e.eval η)
        (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) p y := by
  rw [relation_m, ← opening_l, PowerlessSourceOpening.formula_l]
  simpa only [up₂, up, Term.eval_weakenBound, parameters_pushBound_l,
    parameters_empty_l, Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there] using
    PowerlessRelativeFiniteProgramEvaluationBounded.matrix_formula_l K false φ
      ((η.pushBound y).pushBound p) (up₂ B) (up₂ β) (up₂ C) (up₂ W) (up₂ ω)
      (up₂ Q) (up₂ e) (up₂ t₀) (up₂ t₁) (up₂ t₂) (up₂ a)
      (.bvar .here) (.bvar (.there .here))
      (by simpa only [up₂, up, Term.eval_weakenBound, parameters_pushBound_l,
        parameters_empty_l] using h)

theorem output_member_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B β C W ω Q e t₀ t₁ t₂ a : Term ℒ [] Δ .set)
    (h : PowerlessRelativeFiniteProgramEvaluationBounded.guard_l φ η
      (B.eval η) (β.eval η) (C.eval η) (W.eval η) (ω.eval η) (Q.eval η)
      (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η))
    (p y : type_l hℳ)
    (hy : PowerlessRelativeFiniteProgramEvaluation.matrix_l false φ η
      (B.eval η) (C.eval η) (ω.eval η) (Q.eval η) (e.eval η)
      (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) p y) : mem_l hℳ y (W.eval η) := by
  have h₀ := (relation_formula_l K φ η B β C W ω Q e t₀ t₁ t₂ a h p y).mpr hy
  rw [relation_m, ← opening_l, PowerlessSourceOpening.formula_l] at h₀
  have h₁ := PowerlessRelativeFiniteProgramEvaluationBounded.matrix_member_l φ
    ((η.pushBound y).pushBound p) (up₂ B) (up₂ C) (up₂ W) (up₂ ω) (up₂ Q)
      (up₂ e) (up₂ t₀) (up₂ t₁) (up₂ t₂) (up₂ a)
      (.bvar .here) (.bvar (.there .here)) h₀
  simpa only [up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_there, Env.pushBound_bound_here] using h₁

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

/-- 实际 Class 参数给出整个原求值关系的集合图与精确像。 -/
theorem exists_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    {φ : Formula ℒ [] (.set :: .set :: Δ)} (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (η : Env (PowerlessRelativeClassStructure.structure_l hℳ A hBase) [] Δ)
    (B β C W ω Q e t₀ t₁ t₂ a P : Term ℒ [] Δ .set)
    (h : let ξ := PowerlessRelativeClassRelativization.env_l η
      PowerlessRelativeFiniteProgramEvaluationBounded.guard_l φ ξ
        (B.eval ξ) (β.eval ξ) (C.eval ξ) (W.eval ξ) (ω.eval ξ) (Q.eval ξ)
        (e.eval ξ) (t₀.eval ξ) (t₁.eval ξ) (t₂.eval ξ) (a.eval ξ)) :
    let ξ := PowerlessRelativeClassRelativization.env_l η
    ∃ G I : PowerlessRelativeClassStructure.type_l hℳ A,
      (∀ p y : type_l hℳ, value_l (ℳ := 𝒱) G.val p y ↔
        mem_l hℳ p (P.eval ξ) ∧ PowerlessRelativeFiniteProgramEvaluation.matrix_l false φ ξ
          (B.eval ξ) (C.eval ξ) (ω.eval ξ) (Q.eval ξ) (e.eval ξ)
          (t₀.eval ξ) (t₁.eval ξ) (t₂.eval ξ) (a.eval ξ) p y) ∧
      (∀ y : type_l hℳ, mem_l hℳ y I.val ↔ ∃ p, mem_l hℳ p (P.eval ξ) ∧
        PowerlessRelativeFiniteProgramEvaluation.matrix_l false φ ξ
          (B.eval ξ) (C.eval ξ) (ω.eval ξ) (Q.eval ξ) (e.eval ξ)
          (t₀.eval ξ) (t₁.eval ξ) (t₂.eval ξ) (a.eval ξ) p y) := by
  let ξ := PowerlessRelativeClassRelativization.env_l η
  obtain ⟨G, hG⟩ := PowerlessRelativeClassRelationalGraph.exists_ambient_l
    (relation_delta_l hφ B C W ω Q e t₀ t₁ t₂ a) η (P.eval η) (W.eval η)
  have hRead (p y : type_l hℳ) : value_l (ℳ := 𝒱) G.val p y ↔
      mem_l hℳ p (P.eval ξ) ∧ PowerlessRelativeFiniteProgramEvaluation.matrix_l false φ ξ
        (B.eval ξ) (C.eval ξ) (ω.eval ξ) (Q.eval ξ) (e.eval ξ)
        (t₀.eval ξ) (t₁.eval ξ) (t₂.eval ξ) (a.eval ξ) p y := by
    rw [hG p y, ← term_l η P, ← term_l η W]
    rw [relation_formula_l K φ ξ B β C W ω Q e t₀ t₁ t₂ a h p y]
    constructor
    · rintro ⟨hp, _, hy⟩; exact ⟨hp, hy⟩
    · rintro ⟨hp, hy⟩
      exact ⟨hp, output_member_l K φ ξ B β C W ω Q e t₀ t₁ t₂ a h p y hy, hy⟩
  obtain ⟨I, hI⟩ := PowerlessRelativeClassSelectedImage.exists_l
    (hBase := hBase) G (P.eval η) (W.eval η)
  refine ⟨G, I, hRead, fun y => ?_⟩
  rw [hI y, ← term_l η W, ← term_l η P]
  constructor
  · rintro ⟨_, p, hp, hpy⟩
    exact ⟨p, hp, ((hRead p y).mp hpy).2⟩
  · rintro ⟨p, hp, hy⟩
    exact ⟨output_member_l K φ ξ B β C W ω Q e t₀ t₁ t₂ a h p y hy,
      p, hp, (hRead p y).mpr ⟨hp, hy⟩⟩

def parameters_m {Γ Ε : SortContext ℒ} (Δ : SortContext ℒ)
    (B : Term ℒ Γ Ε .set) (τ : VariableSubstitution ℒ Δ Γ Ε) : Formula ℒ Γ Ε :=
  match Δ with
  | [] => .truth
  | .set :: Δ => .conj (PowerlessRelativeHierarchySyntax.class_m B (τ .here))
      (parameters_m Δ B (fun v => τ (.there v)))

theorem parameters_formula_l (K : source_coding_l hℳ) {Γ Ε : SortContext ℒ}
    (Δ : SortContext ℒ) (η : Env 𝒱 Γ Ε) (B : Term ℒ Γ Ε .set)
    (τ : VariableSubstitution ℒ Δ Γ Ε) : (parameters_m Δ B τ).satisfies η ↔
      ∀ s (v : Variable Δ s), PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) ((τ v).eval η) := by
  induction Δ with
  | nil =>
      constructor
      · intro _ _ v; nomatch v
      · intro _; trivial
  | cons s Δ ih =>
      cases s
      change (_ ∧ (parameters_m Δ B (fun v => τ (.there v))).satisfies η) ↔ _
      rw [PowerlessRelativeHierarchySemantics.class_formula_l K, ih]
      constructor
      · rintro ⟨h₀, h₁⟩ s v
        cases s
        cases v with
        | here => exact h₀
        | there v => exact h₁ _ v
      · intro h
        exact ⟨h _ .here, fun _ v => h _ (.there v)⟩

def reading_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a P G : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <|
    let p := .bvar (.there .here)
    let y := .bvar .here
    .iff (PowerlessValueBounded.formula_m (up₂ G) p y) <|
      .conj (SecondOrderObjectSyntax.member_m p (up₂ P)) <|
        PowerlessRelativeFiniteProgramEvaluation.matrix_m false φ
          (up₂ B) (up₂ C) (up₂ ω) (up₂ Q) (up₂ e) (up₂ t₀) (up₂ t₁) (up₂ t₂) (up₂ a) p y

def image_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a P I : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <|
    .iff (SecondOrderObjectSyntax.member_m (.bvar .here) (up I)) <|
      membershipLevyBound.boundedExists (up P) <|
        PowerlessRelativeFiniteProgramEvaluation.matrix_m false φ
          (up₂ B) (up₂ C) (up₂ ω) (up₂ Q) (up₂ e) (up₂ t₀) (up₂ t₁) (up₂ t₂) (up₂ a)
          (.bvar .here) (.bvar (.there .here))

theorem reading_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B C ω Q e t₀ t₁ t₂ a P G : Term ℒ Γ Δ .set) :
    (reading_m φ B C ω Q e t₀ t₁ t₂ a P G).satisfies η ↔
      ∀ p y, value_l (ℳ := 𝒱) (G.eval η) p y ↔ mem_l hℳ p (P.eval η) ∧
        PowerlessRelativeFiniteProgramEvaluation.matrix_l false φ (parameters_l η)
          (B.eval η) (C.eval η) (ω.eval η) (Q.eval η) (e.eval η)
          (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) p y := by
  simp only [reading_m, Formula.satisfies, PowerlessValueBounded.formula_l,
    PowerlessRelativeFiniteProgramEvaluation.matrix_formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval, parameters_pushBound_l,
    up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  rfl

theorem image_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B C ω Q e t₀ t₁ t₂ a P I : Term ℒ Γ Δ .set) :
    (image_m φ B C ω Q e t₀ t₁ t₂ a P I).satisfies η ↔
      ∀ y, mem_l hℳ y (I.eval η) ↔ ∃ p, mem_l hℳ p (P.eval η) ∧
        PowerlessRelativeFiniteProgramEvaluation.matrix_l false φ (parameters_l η)
          (B.eval η) (C.eval η) (ω.eval η) (Q.eval η) (e.eval η)
          (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) p y := by
  simp only [image_m, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies,
    PowerlessRelativeFiniteProgramEvaluation.matrix_formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval, parameters_pushBound_l,
    up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  rfl

def conclusion_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a P : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .existsE .set <| .existsE .set <|
    let G := .bvar (.there .here)
    let I := .bvar .here
    .conj (PowerlessRelativeHierarchySyntax.class_m (up₂ B) G) <|
      .conj (PowerlessRelativeHierarchySyntax.class_m (up₂ B) I) <|
        .conj (reading_m φ (up₂ B) (up₂ C) (up₂ ω) (up₂ Q) (up₂ e)
          (up₂ t₀) (up₂ t₁) (up₂ t₂) (up₂ a) (up₂ P) G)
          (image_m φ (up₂ B) (up₂ C) (up₂ ω) (up₂ Q) (up₂ e)
            (up₂ t₀) (up₂ t₁) (up₂ t₂) (up₂ a) (up₂ P) I)

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β C W ω Q e t₀ t₁ t₂ a P : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (parameters_m Δ B (fun v => .fvar v)) <|
    .imp (PowerlessRelativeFiniteProgramEvaluationBounded.guard_m φ B β C W ω Q e t₀ t₁ t₂ a)
      (conclusion_m φ B C ω Q e t₀ t₁ t₂ a P)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β C W ω Q e t₀ t₁ t₂ a P : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B β C W ω Q e t₀ t₁ t₂ a P)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    {φ : Formula ℒ [] (.set :: .set :: Δ)} (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (B β C W ω Q e t₀ t₁ t₂ a P : Term ℒ [] Δ .set) :
    (sentence_m φ B β C W ω Q e t₀ t₁ t₂ a P).TrueIn
      (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro ζ hParams hGuard
  have hParams' := (parameters_formula_l K Δ ζ B (fun v => .fvar v)).mp hParams
  have hGuard' := (PowerlessRelativeFiniteProgramEvaluationBounded.guard_formula_l K
    φ ζ B β C W ω Q e t₀ t₁ t₂ a).mp hGuard
  have hBase := hGuard'.1
  let η : Env (PowerlessRelativeClassStructure.structure_l h𝒩 (B.eval ζ) hBase) [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with
        | .set => ⟨ζ.freeVal v, hParams' _ v⟩ }
  have hη : PowerlessRelativeClassRelativization.env_l η = ζ := by
    apply Env.ext
    · intro s v; nomatch v
    · intro s v; cases s; rfl
  obtain ⟨G, I, hRead, hImage⟩ := exists_l (hBase := hBase) K hφ η
    B β C W ω Q e t₀ t₁ t₂ a P
    (by simpa only [hη, parameters_empty_l] using hGuard')
  simp only [conclusion_m, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    reading_formula_l K, image_formula_l K, parameters_pushBound_l, parameters_empty_l,
    up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  refine ⟨G.val, I.val, G.property, I.property, ?_, ?_⟩
  · simpa only [hη, ThirdOrderSemantics.carrier_l, SecondOrderQuotient.structure_l] using hRead
  · simpa only [hη] using hImage

theorem derives_m {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (B β C W ω Q e t₀ t₁ t₂ a P : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B β C W ω Q e t₀ t₁ t₂ a P)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ h𝒩 => models_l h𝒩 hφ B β C W ω Q e t₀ t₁ t₂ a P)

#print axioms relation_delta_l
#print axioms relation_formula_l
#print axioms output_member_l
#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramEvaluationGraph
