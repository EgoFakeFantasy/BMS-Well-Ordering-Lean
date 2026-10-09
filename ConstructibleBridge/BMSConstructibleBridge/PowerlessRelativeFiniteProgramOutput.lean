import BMSConstructibleBridge.PowerlessRelativeFiniteProgramInvariant

/-! # 实际内部程序的唯一输出

从内部执行历史的最后状态读取指定存储坐标。所有有效坐标确有读数，
不以缺省值掩盖执行存在性；缺失坐标缺省为 B。输出总且单值并属于
Class，不假定整个求值像成为集合或无限求值图存在。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramOutput

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeFiniteProgramExecution (relation_m relation_formula_l)
open PowerlessRelativeFiniteProgramInstruction (functional_m functional_l tags_m)
open PowerlessDefinableFiniteTrace (trace_m trace_l trace_formula_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_l parameters_pushBound_l parameters_empty_l at_formula_l)

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
    (B ω e a n k : Term ℒ [] Δ .set) (y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <|
    .existsE .set <| .existsE .set <| .existsE .set <|
      let S : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
        .bvar (.there (.there (.there (.there (.there .here)))))
      let D := .bvar (.there (.there (.there (.there .here))))
      let F := .bvar (.there (.there (.there .here)))
      let s := .bvar (.there (.there .here))
      let E := .bvar (.there .here)
      let g := .bvar .here
      .conj (PowerlessRelativeHierarchySyntax.class_m (embed_m B) D) <|
        .conj (PowerlessRelativeHierarchySyntax.class_m (embed_m B) F) <|
          .conj (trace_m ψ (embed_m e) (embed_m a) (embed_m n) S D F) <|
            .conj (SecondOrderObjectSyntax.value_m F (embed_m n) s) <|
              .conj (PowerlessRelativeFiniteProgramStep.valid_m (embed_m B) (embed_m ω)
                (embed_m n) E g s) (SecondOrderObjectSyntax.value_m g (embed_m k) (up₆ y))

def output_m {Γ Δ : SortContext ℒ} (ψ : Formula ℒ [] (.set :: .set :: Δ))
    (B ω e a n k : Term ℒ [] Δ .set) (y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessRelativeHierarchySyntax.class_m (embed_m B) y) <| .disj
    (run_m ψ B ω e a n k y) <| .conj
      (.neg (.existsE .set (run_m ψ B ω e a n k (.bvar .here)))) (.equal y (embed_m B))

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
    (η : Env 𝒱 [] Δ) (B ω e a n k y : type_l hℳ) : Prop :=
  ∃ S D F s E g, PowerlessRelativeClassCorrespondence.member_l hℳ B D ∧
    PowerlessRelativeClassCorrespondence.member_l hℳ B F ∧ trace_l ψ η e a n S D F ∧
      value_l (ℳ := 𝒱) F n s ∧ PowerlessRelativeFiniteProgramStep.valid_l B ω n E g s ∧
        value_l (ℳ := 𝒱) g k y

def output_l {Δ : SortContext ℒ} (ψ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (B ω e a n k y : type_l hℳ) : Prop :=
  PowerlessRelativeClassCorrespondence.member_l hℳ B y ∧
    (run_l ψ η B ω e a n k y ∨ ((¬∃ z, run_l ψ η B ω e a n k z) ∧ y = B))

theorem run_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (ψ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B ω e a n k : Term ℒ [] Δ .set) (y : Term ℒ Γ Δ .set) :
    (run_m ψ B ω e a n k y).satisfies η ↔ run_l ψ (parameters_l η)
      (B.eval (parameters_l η)) (ω.eval (parameters_l η)) (e.eval (parameters_l η))
        (a.eval (parameters_l η)) (n.eval (parameters_l η)) (k.eval (parameters_l η)) (y.eval η) := by
  simp only [run_m, run_l, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    trace_formula_l, value_formula_l, PowerlessRelativeFiniteProgramStep.valid_formula_l K,
    embed_l, parameters_pushBound_l, up₆, up₃, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem output_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (ψ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B ω e a n k : Term ℒ [] Δ .set) (y : Term ℒ Γ Δ .set) :
    (output_m ψ B ω e a n k y).satisfies η ↔ output_l ψ (parameters_l η)
      (B.eval (parameters_l η)) (ω.eval (parameters_l η)) (e.eval (parameters_l η))
        (a.eval (parameters_l η)) (n.eval (parameters_l η)) (k.eval (parameters_l η)) (y.eval η) := by
  simp only [output_m, output_l, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.class_formula_l K, run_formula_l K, embed_l,
    parameters_pushBound_l, Term.eval]
  rfl

theorem run_class_l {Δ : SortContext ℒ} (ψ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {B ω e a n k y : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ z, mem_l hℳ z x → mem_l hℳ z B)
    (hy : run_l ψ η B ω e a n k y) : PowerlessRelativeClassCorrespondence.member_l hℳ B y := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hValid, hy⟩ := hy
  exact PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hValid.2.2.2.1
    (SecondOrderFunctionProperties.value_mem_l hℳ hValid.2.2.2.2.2 hy).2

theorem run_unique_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (ψ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ) {B ω e a n k y z : type_l hℳ}
    (hn : mem_l hℳ n K.omega) (he : e = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hUnique : ∀ x y z, ψ.satisfies ((η.pushFree x).pushFree y) →
      ψ.satisfies ((η.pushFree x).pushFree z) → y = z)
    (hy : run_l ψ η B ω e a n k y) (hz : run_l ψ η B ω e a n k z) : y = z := by
  obtain ⟨S, D, F, s, E, g, _, _, hF, hs, hValid, hy⟩ := hy
  obtain ⟨T, A, H, t, C, h, _, _, hH, ht, hValid', hz⟩ := hz
  have hFH := PowerlessDefinableFiniteTraceUnique.unique_l K ψ η hn he hF hH hUnique
  subst H
  have hst := SecondOrderFunctionProperties.value_unique_l hℳ hF.2.1 hs ht
  subst t
  obtain ⟨_, hEC, hgh⟩ := PowerlessRelativeFiniteProgramStep.record_coordinates_l hValid.1 hValid'.1
  subst C; subst h
  exact SecondOrderFunctionProperties.value_unique_l hℳ hValid.2.2.2.2.2 hy hz

theorem output_exists_unique_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (ψ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ) {B ω e a n k : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ z, mem_l hℳ z x → mem_l hℳ z B)
    (hn : mem_l hℳ n K.omega) (he : e = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hUnique : ∀ x y z, ψ.satisfies ((η.pushFree x).pushFree y) →
      ψ.satisfies ((η.pushFree x).pushFree z) → y = z) :
    ∃! y, output_l ψ η B ω e a n k y := by
  classical
  by_cases hSome : ∃ y, run_l ψ η B ω e a n k y
  · obtain ⟨y, hy⟩ := hSome
    refine ⟨y, ⟨run_class_l ψ η hBase hy, Or.inl hy⟩, ?_⟩
    intro z hz
    rcases hz.2 with hz | hz
    · exact run_unique_l K ψ η hn he hUnique hz hy
    · exact (hz.1 ⟨y, hy⟩).elim
  · refine ⟨B, ⟨PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase,
      Or.inr ⟨hSome, rfl⟩⟩, ?_⟩
    intro z hz
    rcases hz.2 with hz | hz
    · exact (hSome ⟨z, hz⟩).elim
    · exact hz.2

theorem run_exists_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B C ω w N Q e t₀ t₁ t₂ a n k : Term ℒ [] Δ .set)
    (hBase : ∀ x, mem_l hℳ x (B.eval η) → ∀ z, mem_l hℳ z x → mem_l hℳ z (B.eval η))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η))
    (hω : SecondOrderOmega.omega_l hℳ (ω.eval η)) (he : ∀ x, ¬mem_l hℳ x (e.eval η))
    (hInitial : PowerlessRelativeFiniteProgramStep.record_l (e.eval η) (e.eval η) (e.eval η) (a.eval η))
    (hw : map_l (ℳ := 𝒱) (w.eval η) (N.eval η) (Q.eval η))
    (hTags : t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η)
    (hFunctional : functional_l φ η (B.eval η)) (hn : mem_l hℳ (n.eval η) (ω.eval η))
    (hk : mem_l hℳ (k.eval η) (n.eval η)) :
    ∃ y, run_l (relation_m φ B C ω w e t₀ t₁ t₂) η
      (B.eval η) (ω.eval η) (e.eval η) (a.eval η) (n.eval η) (k.eval η) y := by
  have hExecution := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
    (PowerlessRelativeFiniteProgramExecution.models_l hℳ φ B C ω w N Q e t₀ t₁ t₂ a n) η
  simp only [PowerlessRelativeFiniteProgramExecution.schema_m,
    PowerlessDefinableFiniteTraceDerives.zero_m, tags_m, functional_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeFiniteProgramStep.record_formula_l, map_formula_l, at_formula_l,
    parameters_pushBound_l, parameters_empty_l, SecondOrderObjectSyntax.member_m,
    Arguments.eval, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there] at hExecution
  have hResult := hExecution hBase hC hω he hInitial hw hTags hFunctional hn
  simp only [PowerlessRelativeFiniteProgramExecution.result_m, Formula.satisfies,
    PowerlessRelativeClassDefinableFiniteTrace.finite_formula_l K, parameters_empty_l] at hResult
  obtain ⟨S, D, F, hD, hFC, hTrace⟩ := hResult.1
  obtain ⟨s, hs, _⟩ := hTrace.2.1.2 (n.eval η) ((hTrace.1 (n.eval η)).mpr (Or.inr rfl))
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  obtain ⟨E, g, hValid⟩ := PowerlessRelativeFiniteProgramInvariant.values_l K φ η
    B C ω w N Q e t₀ t₁ t₂ a n hBase hC hωEq he hInitial hw hTags hFunctional
      (hωEq ▸ hn) hTrace (n.eval η) s hs.2
  obtain ⟨y, hy, _⟩ := hValid.2.2.2.2.2.2 (k.eval η) hk
  exact ⟨y, S, D, F, s, E, g, hD, hFC, hTrace, hs.2, hValid, hy.2⟩

def result_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w e t₀ t₁ t₂ a n k : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  let ψ := relation_m φ B C ω w e t₀ t₁ t₂
  .conj (.existsE .set <| .conj (output_m ψ B ω e a n k (.bvar .here)) <|
      .forallE .set <| .imp (output_m ψ B ω e a n k (.bvar .here))
        (.equal (.bvar .here) (.bvar (.there .here)))) <|
    .imp (SecondOrderObjectSyntax.member_m k n) (.existsE .set (run_m ψ B ω e a n k (.bvar .here)))

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w N Q e t₀ t₁ t₂ a n k : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B C) <|
      .imp (SecondOrderOmegaSyntax.omega_m ω) <|
        .imp (PowerlessDefinableFiniteTraceDerives.zero_m e) <|
          .imp (PowerlessRelativeFiniteProgramStep.record_m e e e a) <|
            .imp (SecondOrderObjectSyntax.map_m w N Q) <| .imp (tags_m t₀ t₁ t₂) <|
              .imp (functional_m φ B) <| .imp (SecondOrderObjectSyntax.member_m n ω)
                (result_m φ B C ω w e t₀ t₁ t₂ a n k)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w N Q e t₀ t₁ t₂ a n k : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B C ω w N Q e t₀ t₁ t₂ a n k)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (B C ω w N Q e t₀ t₁ t₂ a n k : Term ℒ [] Δ .set) :
    (sentence_m φ B C ω w N Q e t₀ t₁ t₂ a n k).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, result_m, PowerlessDefinableFiniteTraceDerives.zero_m, tags_m,
    functional_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeFiniteProgramStep.record_formula_l, map_formula_l, output_formula_l K,
    run_formula_l K, at_formula_l, parameters_pushBound_l, parameters_empty_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro η hBase hC hω he hInitial hw hTags hFunctional hn
  have hωEq := SecondOrderOmega.unique_l h𝒩 hω K.omega_spec
  have heEq : e.eval η = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val := by
    apply SecondOrderQuotient.ext_l h𝒩
    intro x
    exact iff_of_false (he x) (PowerlessBMSQuotientSuccessor.zero_l K x)
  let ψ := relation_m φ B C ω w e t₀ t₁ t₂
  have hUnique : ∀ x y z, ψ.satisfies ((η.pushFree x).pushFree y) →
      ψ.satisfies ((η.pushFree x).pushFree z) → y = z := by
    intro x y z hy hz
    obtain ⟨v, _, hv⟩ := PowerlessRelativeFiniteProgramStep.exists_unique_l
      φ η hBase hC hw hTags hFunctional x
    exact (hv y ((relation_formula_l K φ η B C ω w e t₀ t₁ t₂ x y).mp hy)).trans
      (hv z ((relation_formula_l K φ η B C ω w e t₀ t₁ t₂ x z).mp hz)).symm
  exact ⟨output_exists_unique_l K ψ η hBase (hωEq ▸ hn) heEq hUnique,
    fun hk => run_exists_l K φ η B C ω w N Q e t₀ t₁ t₂ a n k
      hBase hC hω he hInitial hw hTags hFunctional hn hk⟩

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w N Q e t₀ t₁ t₂ a n k : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B C ω w N Q e t₀ t₁ t₂ a n k)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 φ B C ω w N Q e t₀ t₁ t₂ a n k)

#print axioms run_formula_l
#print axioms run_unique_l
#print axioms run_exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramOutput
