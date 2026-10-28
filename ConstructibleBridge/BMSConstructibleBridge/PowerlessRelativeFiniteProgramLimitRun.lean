import BMSConstructibleBridge.PowerlessRelativeFiniteProgramLimitExecution
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramOutput

/-! # 真实程序读数的全部见证留在同一层

同层有限历史与旧实际历史的干净图唯一性给出同一末态和读数。
只替换历史陪域，不断言旧陪域本身留层。六个存在见证均属于 W，
输出也属于 W；有效坐标确有这种真实 run，而非缺省总化。
这仍不提供整个求值图或无限求值像的集合性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramLimitRun

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)
open PowerlessRelativeFiniteProgramExecution (relation_m relation_formula_l)
open PowerlessRelativeFiniteProgramInstruction (functional_l functional_m tags_m)
open PowerlessDefinableFiniteTrace (trace_l trace_m trace_formula_l)
open PowerlessRelativeFiniteProgramLimitStep (coordinates_l reading_l)
open PowerlessBMSQuotientSubsetImageDerives
  (parameters_l parameters_pushBound_l parameters_empty_l at_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private def binding_m {Γ Δ : SortContext ℒ} : Substitution ℒ [] Δ Γ Δ :=
  .map (fun v => nomatch v) (fun v => .fvar v)

private def embed_m {Γ Δ : SortContext ℒ} (t : Term ℒ [] Δ .set) : Term ℒ Γ Δ .set :=
  t.substitute binding_m

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)
private abbrev up₆ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up₃ (up₃ t)

def run_m {Γ Δ : SortContext ℒ} (ψ : Formula ℒ [] (.set :: .set :: Δ))
    (B ω W e a n k : Term ℒ [] Δ .set) (y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <|
    .existsE .set <| .existsE .set <| .existsE .set <|
      let S : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
        .bvar (.there (.there (.there (.there (.there .here)))))
      let D := .bvar (.there (.there (.there (.there .here))))
      let F := .bvar (.there (.there (.there .here)))
      let s := .bvar (.there (.there .here))
      let E := .bvar (.there .here)
      let g := .bvar .here
      .conj (SecondOrderObjectSyntax.member_m S (embed_m W)) <|
        .conj (SecondOrderObjectSyntax.member_m D (embed_m W)) <|
          .conj (SecondOrderObjectSyntax.member_m F (embed_m W)) <|
            .conj (SecondOrderObjectSyntax.member_m s (embed_m W)) <|
              .conj (SecondOrderObjectSyntax.member_m E (embed_m W)) <|
                .conj (SecondOrderObjectSyntax.member_m g (embed_m W)) <|
                  .conj (trace_m ψ (embed_m e) (embed_m a) (embed_m n) S D F) <|
                    .conj (SecondOrderObjectSyntax.value_m F (embed_m n) s) <|
                      .conj (PowerlessRelativeFiniteProgramStep.valid_m (embed_m B)
                        (embed_m ω) (embed_m n) E g s)
                          (SecondOrderObjectSyntax.value_m g (embed_m k) (up₆ y))

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

def run_l {Δ : SortContext ℒ} (ψ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (B ω W e a n k y : type_l hℳ) : Prop :=
  ∃ S D F s E g, mem_l hℳ S W ∧ mem_l hℳ D W ∧ mem_l hℳ F W ∧
    mem_l hℳ s W ∧ mem_l hℳ E W ∧ mem_l hℳ g W ∧ trace_l ψ η e a n S D F ∧
      value_l (ℳ := 𝒱) F n s ∧ PowerlessRelativeFiniteProgramStep.valid_l B ω n E g s ∧
        value_l (ℳ := 𝒱) g k y

theorem run_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (ψ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B ω W e a n k : Term ℒ [] Δ .set) (y : Term ℒ Γ Δ .set) :
    (run_m ψ B ω W e a n k y).satisfies η ↔ run_l ψ (parameters_l η)
      (B.eval (parameters_l η)) (ω.eval (parameters_l η)) (W.eval (parameters_l η))
        (e.eval (parameters_l η)) (a.eval (parameters_l η))
          (n.eval (parameters_l η)) (k.eval (parameters_l η)) (y.eval η) := by
  simp only [run_m, run_l, Formula.satisfies, trace_formula_l,
    value_formula_l, PowerlessRelativeFiniteProgramStep.valid_formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval, embed_l, parameters_pushBound_l,
    up₆, up₃, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem forget_l {Δ : SortContext ℒ} (ψ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {B β W ω e a n k y : type_l hℳ}
    (hW : level_l hℳ B β W) (hy : run_l ψ η B ω W e a n k y) :
    PowerlessRelativeFiniteProgramOutput.run_l ψ η B ω e a n k y := by
  obtain ⟨S, D, F, s, E, g, _, hD, hF, _, _, _, hTrace, hs, hValid, hy⟩ := hy
  exact ⟨S, D, F, s, E, g, ⟨β, W, hW, hD⟩, ⟨β, W, hW, hF⟩,
    hTrace, hs, hValid, hy⟩

theorem refine_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B β W C ω w N Q e t₀ t₁ t₂ a n k : Term ℒ [] Δ .set) {y : type_l hℳ}
    (hB : ∀ x, mem_l hℳ x (B.eval η) → ∀ z, mem_l hℳ z x → mem_l hℳ z (B.eval η))
    (hβ : limit_l hℳ (β.eval η)) (hW : level_l hℳ (B.eval η) (β.eval η) (W.eval η))
    (hBW : mem_l hℳ (B.eval η) (W.eval η))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η))
    (hCW : ∀ x, mem_l hℳ x (C.eval η) → mem_l hℳ x (W.eval η))
    (hω : SecondOrderOmega.omega_l hℳ (ω.eval η))
    (hωW : mem_l hℳ (ω.eval η) (W.eval η)) (he : ∀ x, ¬mem_l hℳ x (e.eval η))
    (ha : PowerlessRelativeFiniteProgramStep.record_l (e.eval η) (e.eval η) (e.eval η) (a.eval η))
    (hw : map_l (ℳ := 𝒱) (w.eval η) (N.eval η) (Q.eval η))
    (ht : t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η)
    (hφ : functional_l φ η (B.eval η))
    (hφW : PowerlessRelativeFiniteProgramLimitStep.closed_l φ η (B.eval η) (W.eval η))
    (hn : mem_l hℳ (n.eval η) (ω.eval η))
    (hy : PowerlessRelativeFiniteProgramOutput.run_l (relation_m φ B C ω w e t₀ t₁ t₂) η
      (B.eval η) (ω.eval η) (e.eval η) (a.eval η) (n.eval η) (k.eval η) y) :
    mem_l hℳ y (W.eval η) ∧ run_l (relation_m φ B C ω w e t₀ t₁ t₂) η
      (B.eval η) (ω.eval η) (W.eval η) (e.eval η) (a.eval η) (n.eval η) (k.eval η) y := by
  obtain ⟨S, D, F, hS, hD, hF, hTrace⟩ := PowerlessRelativeFiniteProgramLimitExecution.exists_l
    K φ η B β W C ω w N Q e t₀ t₁ t₂ a n hB hβ hW hBW hC hCW hω hωW he ha hw ht hφ hφW hn
  obtain ⟨T, A, G, s, E, g, _, _, hOld, hs, hValid, hy⟩ := hy
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  have heEq : e.eval η = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val :=
    SecondOrderQuotient.ext_l hℳ _ _ (fun x =>
      iff_of_false (he x) (PowerlessBMSQuotientSuccessor.zero_l K x))
  have hUnique : ∀ x y z,
      (relation_m φ B C ω w e t₀ t₁ t₂).satisfies ((η.pushFree x).pushFree y) →
      (relation_m φ B C ω w e t₀ t₁ t₂).satisfies ((η.pushFree x).pushFree z) → y = z := by
    intro x y z hy hz
    obtain ⟨t, _, h⟩ := PowerlessRelativeFiniteProgramStep.exists_unique_l φ η hB hC hw ht hφ x
    exact (h y ((relation_formula_l K φ η B C ω w e t₀ t₁ t₂ x y).mp hy)).trans
      (h z ((relation_formula_l K φ η B C ω w e t₀ t₁ t₂ x z).mp hz)).symm
  have hGF := PowerlessDefinableFiniteTraceUnique.unique_l K
    (relation_m φ B C ω w e t₀ t₁ t₂) η (hωEq ▸ hn) heEq hOld hTrace hUnique
  subst G
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hB hW
  have hsW := reading_l hTrans hF hs
  obtain ⟨p, hEg, hnp⟩ := hValid.1
  obtain ⟨_, hpW⟩ := coordinates_l hTrans hsW hnp
  obtain ⟨hEW, hgW⟩ := coordinates_l hTrans hpW hEg
  exact ⟨reading_l hTrans hgW hy, S, D, F, s, E, g,
    hS, hD, hF, hsW, hEW, hgW, hTrace, hs, hValid, hy⟩

def result_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C W ω w e t₀ t₁ t₂ a n k : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  let ψ := relation_m φ B C ω w e t₀ t₁ t₂
  .conj (.forallE .set <|
    .imp (PowerlessRelativeFiniteProgramOutput.run_m ψ B ω e a n k (.bvar .here)) <|
      .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up W))
        (run_m ψ B ω W e a n k (.bvar .here))) <|
    .imp (SecondOrderObjectSyntax.member_m k n) <|
      .existsE .set <| .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up W))
        (run_m ψ B ω W e a n k (.bvar .here))

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β W C ω w N Q e t₀ t₁ t₂ a n k : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.limit_m β) <|
      .imp (PowerlessRelativeHierarchySyntax.level_m B β W) <|
        .imp (SecondOrderObjectSyntax.member_m B W) <|
          .imp (PowerlessRelativeHierarchySyntax.class_m B C) <|
            .imp (ThirdOrderTheory.subset_m C W) <|
              .imp (SecondOrderOmegaSyntax.omega_m ω) <|
                .imp (SecondOrderObjectSyntax.member_m ω W) <|
                  .imp (PowerlessDefinableFiniteTraceDerives.zero_m e) <|
                    .imp (PowerlessRelativeFiniteProgramStep.record_m e e e a) <|
                      .imp (SecondOrderObjectSyntax.map_m w N Q) <| .imp (tags_m t₀ t₁ t₂) <|
                        .imp (functional_m φ B) <|
                          .imp (PowerlessRelativeFiniteProgramLimitStep.closed_m φ B W) <|
                            .imp (SecondOrderObjectSyntax.member_m n ω)
                              (result_m φ B C W ω w e t₀ t₁ t₂ a n k)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β W C ω w N Q e t₀ t₁ t₂ a n k : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B β W C ω w N Q e t₀ t₁ t₂ a n k)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (B β W C ω w N Q e t₀ t₁ t₂ a n k : Term ℒ [] Δ .set) :
    (sentence_m φ B β W C ω w N Q e t₀ t₁ t₂ a n k).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, result_m, tags_m, functional_m, Formula.satisfies,
    PowerlessDefinableFiniteTraceDerives.zero_m,
    PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.limit_formula_l, PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeHierarchySemantics.class_formula_l K, subset_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeFiniteProgramStep.record_formula_l,
    PowerlessRelativeFiniteProgramLimitStep.closed_formula_l K, run_formula_l K,
    PowerlessRelativeFiniteProgramOutput.run_formula_l K, map_formula_l, at_formula_l,
    parameters_pushBound_l, parameters_empty_l, SecondOrderObjectSyntax.member_m,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro η hB hβ hW hBW hC hCW hω hωW he ha hw ht hφ hφW hn
  constructor
  · intro y hy
    exact refine_l K φ η B β W C ω w N Q e t₀ t₁ t₂ a n k
      hB hβ hW hBW hC hCW hω hωW he ha hw ht hφ hφW hn hy
  · intro hk
    obtain ⟨y, hy⟩ := PowerlessRelativeFiniteProgramOutput.run_exists_l K φ η
      B C ω w N Q e t₀ t₁ t₂ a n k hB hC hω he ha hw ht hφ hn hk
    exact ⟨y, refine_l K φ η B β W C ω w N Q e t₀ t₁ t₂ a n k
      hB hβ hW hBW hC hCW hω hωW he ha hw ht hφ hφW hn hy⟩

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β W C ω w N Q e t₀ t₁ t₂ a n k : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B β W C ω w N Q e t₀ t₁ t₂ a n k)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ h𝒩 => models_l h𝒩 φ B β W C ω w N Q e t₀ t₁ t₂ a n k)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramLimitRun
