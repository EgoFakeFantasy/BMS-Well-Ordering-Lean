import BMSConstructibleBridge.PowerlessRelativeFiniteProgramEvaluationFunction
import BMSConstructibleBridge.PowerlessRelativeClassImageCountability

/-! # 实际程序求值精确像的类内可数性

原程序域的类内单射经实际求值集合函数传到精确像。包括空词、无效坐标
和缺省输出，不以有效运行子集替换原总化求值。不假定求值像属于原见证层。
码域可数性仍须由实际字母表构造；本模块不把这一前提当作终局已解决。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramEvaluationCountability

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_empty_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {A : type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x A → ∀ y, mem_l hℳ y x → mem_l hℳ y A}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

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
        (B.eval ξ) (ω.eval ξ) (Q.eval ξ) (S.eval ξ) (P.eval ξ))
    (hCount : let ξ := PowerlessRelativeClassRelativization.env_l η
      PowerlessRelativeOrdinalCutoff.countable_l A (ω.eval ξ) (P.eval ξ)) :
    let ξ := PowerlessRelativeClassRelativization.env_l η
    ∃ I : PowerlessRelativeClassStructure.type_l hℳ A,
      PowerlessRelativeOrdinalCutoff.countable_l A (ω.eval ξ) I.val ∧
      ∀ y : type_l hℳ, mem_l hℳ y I.val ↔ ∃ p, mem_l hℳ p (P.eval ξ) ∧
        PowerlessRelativeFiniteProgramEvaluation.matrix_l false φ ξ
          (B.eval ξ) (C.eval ξ) (ω.eval ξ) (Q.eval ξ) (e.eval ξ)
          (t₀.eval ξ) (t₁.eval ξ) (t₂.eval ξ) (a.eval ξ) p y := by
  let ξ := PowerlessRelativeClassRelativization.env_l η
  obtain ⟨G, I, hMap, hRead, hImage⟩ :=
    PowerlessRelativeFiniteProgramEvaluationFunction.exists_l K hφ η
      B β C W ω Q e t₀ t₁ t₂ a S P h hDomain
  have hOnto : ∀ y, mem_l hℳ y I.val →
      ∃ p, mem_l hℳ p (P.eval ξ) ∧ value_l (ℳ := 𝒱) G.val p y := by
    intro y hy
    obtain ⟨p, hp, hpy⟩ := (hImage y).mp hy
    exact ⟨p, hp, (hRead p y).mpr ⟨hp, hpy⟩⟩
  obtain ⟨_, _, _, _, _, _, hω, _, _, _, _, _, _, _⟩ := h
  have hP : PowerlessRelativeClassCorrespondence.member_l hℳ A (P.eval ξ) := by
    simpa only [ξ, term_l] using (P.eval η).property
  exact ⟨I, PowerlessRelativeClassImageCountability.countable_l (hBase := hBase)
    K hω hP I.property G.property hMap hOnto hCount, hImage⟩

def conclusion_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a P : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .existsE .set <| .conj (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here)) <|
    .conj (PowerlessRelativeOrdinalCutoff.countable_m (up B) (up ω) (.bvar .here))
      (PowerlessRelativeFiniteProgramEvaluationGraph.image_m φ
        (up B) (up C) (up ω) (up Q) (up e) (up t₀) (up t₁) (up t₂) (up a) (up P) (.bvar .here))

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β C W ω Q e t₀ t₁ t₂ a S P : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_m Δ B (fun v => .fvar v)) <|
    .imp (PowerlessRelativeFiniteProgramEvaluationBounded.guard_m φ B β C W ω Q e t₀ t₁ t₂ a) <|
      .imp (PowerlessRelativeFiniteProgramDomain.domain_m B ω Q S P) <|
        .imp (PowerlessRelativeOrdinalCutoff.countable_m B ω P)
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
  intro ζ hParams hGuard hDomain hCount
  have hParams' := (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_formula_l
    K Δ ζ B (fun v => .fvar v)).mp hParams
  have hGuard' := (PowerlessRelativeFiniteProgramEvaluationBounded.guard_formula_l K
    φ ζ B β C W ω Q e t₀ t₁ t₂ a).mp hGuard
  have hDomain' := (PowerlessRelativeFiniteProgramDomain.domain_formula_l K ζ B ω Q S P).mp hDomain
  have hCount' := (PowerlessRelativeOrdinalCutoff.countable_formula_l K ζ B ω P).mp hCount
  have hBase := hGuard'.1
  let η : Env (PowerlessRelativeClassStructure.structure_l h𝒩 (B.eval ζ) hBase) [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with
        | .set => ⟨ζ.freeVal v, hParams' _ v⟩ }
  have hη : PowerlessRelativeClassRelativization.env_l η = ζ := by
    apply Env.ext
    · intro s v; nomatch v
    · intro s v; cases s; rfl
  obtain ⟨I, hI, hImage⟩ := exists_l (hBase := hBase) K hφ η B β C W ω Q e t₀ t₁ t₂ a S P
    (by simpa only [hη, parameters_empty_l] using hGuard')
    (by simpa only [hη] using hDomain') (by simpa only [hη] using hCount')
  simp only [conclusion_m, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeOrdinalCutoff.countable_formula_l K,
    PowerlessRelativeFiniteProgramEvaluationGraph.image_formula_l K,
    up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here,
    PowerlessBMSQuotientSubsetImageDerives.parameters_pushBound_l, parameters_empty_l]
  exact ⟨I.val, I.property, by simpa only [hη] using hI,
    by simpa only [hη] using hImage⟩

theorem derives_m {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (B β C W ω Q e t₀ t₁ t₂ a S P : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B β C W ω Q e t₀ t₁ t₂ a S P)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ h𝒩 => models_l h𝒩 hφ B β C W ω Q e t₀ t₁ t₂ a S P)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramEvaluationCountability
