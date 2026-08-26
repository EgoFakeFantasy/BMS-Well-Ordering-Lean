import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCEnumeration

/-!
# replacement presentation 的外部 Hilbert 枚举

该模块把 `[固定公理, separation, replacement]` 组织为一个独立的 Project 理论。
对象层内部化仍可在现有 ZFC 宿主中完成，但外部 checked 枚举不再混入 collection。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofCode

open _root_.YesMetaZFC.SetTheory
open _root_.YesMetaZFC.SetTheory.Definitional
open _root_.YesMetaZFC.SetTheory.Definitional.Project
open Nonlogical.BasicSetTheory

set_option autoImplicit false

/-- replacement presentation 的 Project 公理谓词。 -/
inductive FsZFCReplacementAxiom : FsProjectTheory
  | extensionality :
      FsZFCReplacementAxiom Axioms.extensionality
  | emptySet :
      FsZFCReplacementAxiom Axioms.emptySet
  | pairing :
      FsZFCReplacementAxiom Axioms.pairing
  | union :
      FsZFCReplacementAxiom Axioms.union
  | powerSet :
      FsZFCReplacementAxiom Axioms.powerSet
  | infinity :
      FsZFCReplacementAxiom Axioms.infinity
  | foundation :
      FsZFCReplacementAxiom Axioms.foundation
  | choice :
      FsZFCReplacementAxiom Axioms.choice
  | separation {parameterCount : Nat}
      (schema : Project.UnarySchema parameterCount) :
      FsZFCReplacementAxiom (Axioms.Schema.separation schema)
  | replacement {parameterCount : Nat}
      (schema : Project.BinarySchema parameterCount) :
      FsZFCReplacementAxiom (Axioms.Schema.replacement schema)

def fs_zfc_replacement_project_base_theory : FsProjectTheory :=
  FsZFCReplacementAxiom

def fs_zfc_replacement_support_raw_theory : SetTheory :=
  fs_internal_project_raw_theory fs_zfc_replacement_project_base_theory

def fs_zfc_replacement_support_theory : SetTheory :=
  fs_internal_project_theory fs_zfc_replacement_project_base_theory

theorem fs_zfc_replacement_support_raw_theory_sentence
    {formula : SetFormula}
    (hFormula : fs_zfc_replacement_support_raw_theory formula) :
    Formula.Sentence formula :=
  fs_internal_project_raw_theory_sentence hFormula

theorem fs_zfc_replacement_support_theory_hilbert_closed :
    ∀ formula,
      fs_zfc_replacement_support_theory formula →
        fs_zfc_replacement_support_theory
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set formula) := by
  intro formula hFormula
  simpa [fs_zfc_replacement_support_theory] using
    fs_internal_project_theory_hilbert_closed
      fs_zfc_replacement_project_base_theory
      (Formula.hilbertize
        Nonlogical.BasicSetTheory.SetSort.set formula)
      (Theory.hilbertize_mem
        (anchorSort :=
          Nonlogical.BasicSetTheory.SetSort.set) hFormula)

private theorem fs_zfc_replacement_fixed_axiom_sound
    {sentence : FsProjectSentence}
    (hMember : sentence ∈ fs_zfc_fixed_axioms) :
    FsZFCReplacementAxiom sentence := by
  simp [fs_zfc_fixed_axioms] at hMember
  rcases hMember with
    rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact .extensionality
  · exact .emptySet
  · exact .pairing
  · exact .union
  · exact .powerSet
  · exact .infinity
  · exact .foundation
  · exact .choice

private theorem fs_zfc_replacement_separation_generate_sound
    {payload : Nat}
    {sentence : FsProjectSentence}
    (hGenerate :
      fs_zfc_separation_generate payload =
        some sentence) :
    FsZFCReplacementAxiom sentence := by
  unfold fs_zfc_separation_generate at hGenerate
  dsimp only at hGenerate
  cases hDecode :
      fs_project_unary_schema_hilbert_decode
        (godel_unpair_value payload).1
        (godel_unpair_value payload).2 with
  | none =>
      simp [hDecode] at hGenerate
  | some schema =>
      simp only [hDecode, Option.map_some,
        Option.some.injEq] at hGenerate
      subst sentence
      exact .separation schema

private theorem fs_zfc_replacement_replacement_generate_sound
    {payload : Nat}
    {sentence : FsProjectSentence}
    (hGenerate :
      fs_zfc_replacement_generate payload =
        some sentence) :
    FsZFCReplacementAxiom sentence := by
  unfold fs_zfc_replacement_generate at hGenerate
  dsimp only at hGenerate
  cases hDecode :
      fs_project_binary_schema_hilbert_decode
        (godel_unpair_value payload).1
        (godel_unpair_value payload).2 with
  | none =>
      simp [hDecode] at hGenerate
  | some schema =>
      simp only [hDecode, Option.map_some,
        Option.some.injEq] at hGenerate
      subst sentence
      exact .replacement schema

theorem fs_zfc_replacement_axiom_generate_sound
    {certificate : Nat}
    {sentence : FsProjectSentence}
    (hGenerate :
      fs_zfc_replacement_axiom_generate certificate =
        some sentence) :
    FsZFCReplacementAxiom sentence := by
  unfold fs_zfc_replacement_axiom_generate at hGenerate
  rw [fs_zfc_axiom_generate_with_schema_plugins_eq] at hGenerate
  dsimp only at hGenerate
  split at hGenerate
  next hFixed =>
    exact fs_zfc_replacement_fixed_axiom_sound
      (List.mem_of_getElem? hGenerate)
  next hNotFixed =>
    split at hGenerate
    next hSchema =>
      exact
        ProofT.SchemaGeneratorPlugin.generate_list_sound
          fs_zfc_replacement_schema_generator_plugins
          (godel_unpair_value
            (godel_unpair_value certificate).2).1
          (godel_unpair_value
            (godel_unpair_value certificate).2).2
          (fs_zfc_replacement_schema_generator_plugins_elim
            fs_zfc_replacement_separation_generate_sound
            fs_zfc_replacement_replacement_generate_sound)
          hGenerate
    next hNotSchema =>
      simp at hGenerate

private theorem fs_zfc_replacement_separation_hilbertize_schema
    {parameterCount : Nat}
    (schema : Project.UnarySchema parameterCount) :
    Formula.hilbertize
        Nonlogical.BasicSetTheory.SetSort.set
        (fs_embed_project_sentence
          (Axioms.Schema.separation
            (fs_project_unary_schema_hilbertize schema))) =
      Formula.hilbertize
        Nonlogical.BasicSetTheory.SetSort.set
        (fs_embed_project_sentence
          (Axioms.Schema.separation schema)) := by
  simp only [fs_embed_project_sentence]
  rw [← fs_embed_project_hilbertize,
    ← fs_embed_project_hilbertize]
  congr 1
  simp only [Axioms.Schema.separation,
    Project.Sentence.forallClosure]
  rw [fs_project_hilbertize_forallClosure,
    fs_project_hilbertize_forallClosure]
  simp [Axioms.Schema.separationCore,
    fs_project_unary_schema_hilbertize,
    fs_project_hilbertize,
    fs_project_hilbertize_rename_idempotent]

private theorem fs_zfc_replacement_replacement_hilbertize_schema
    {parameterCount : Nat}
    (schema : Project.BinarySchema parameterCount) :
    Formula.hilbertize
        Nonlogical.BasicSetTheory.SetSort.set
        (fs_embed_project_sentence
          (Axioms.Schema.replacement
            (fs_project_binary_schema_hilbertize schema))) =
      Formula.hilbertize
        Nonlogical.BasicSetTheory.SetSort.set
        (fs_embed_project_sentence
          (Axioms.Schema.replacement schema)) := by
  simp only [fs_embed_project_sentence]
  rw [← fs_embed_project_hilbertize,
    ← fs_embed_project_hilbertize]
  congr 1
  simp only [Axioms.Schema.replacement,
    Project.Sentence.forallClosure]
  rw [fs_project_hilbertize_forallClosure,
    fs_project_hilbertize_forallClosure]
  simp [Axioms.Schema.replacementCore,
    fs_project_binary_schema_hilbertize,
    fs_project_hilbertize,
    fs_project_hilbertize_rename_idempotent,
    Project.Formula.existsMem]

theorem fs_zfc_replacement_axiom_generate_complete_hilbert
    {sentence : FsProjectSentence}
    (hAxiom : FsZFCReplacementAxiom sentence) :
    ∃ certificate,
      (fs_zfc_replacement_axiom_generate certificate).map
          (fun generated =>
            Formula.hilbertize
              Nonlogical.BasicSetTheory.SetSort.set
              (fs_embed_project_sentence generated)) =
        some (Formula.hilbertize
          Nonlogical.BasicSetTheory.SetSort.set
          (fs_embed_project_sentence sentence)) := by
  cases hAxiom with
  | extensionality =>
      exact ⟨godel_pair_value 0 0, by
        simp [fs_zfc_replacement_axiom_generate,
          fs_zfc_fixed_axioms, godel_unpair_value_pair]⟩
  | emptySet =>
      exact ⟨godel_pair_value 0 1, by
        simp [fs_zfc_replacement_axiom_generate,
          fs_zfc_fixed_axioms, godel_unpair_value_pair]⟩
  | pairing =>
      exact ⟨godel_pair_value 0 2, by
        simp [fs_zfc_replacement_axiom_generate,
          fs_zfc_fixed_axioms, godel_unpair_value_pair]⟩
  | union =>
      exact ⟨godel_pair_value 0 3, by
        simp [fs_zfc_replacement_axiom_generate,
          fs_zfc_fixed_axioms, godel_unpair_value_pair]⟩
  | powerSet =>
      exact ⟨godel_pair_value 0 4, by
        simp [fs_zfc_replacement_axiom_generate,
          fs_zfc_fixed_axioms, godel_unpair_value_pair]⟩
  | infinity =>
      exact ⟨godel_pair_value 0 5, by
        simp [fs_zfc_replacement_axiom_generate,
          fs_zfc_fixed_axioms, godel_unpair_value_pair]⟩
  | foundation =>
      exact ⟨godel_pair_value 0 6, by
        simp [fs_zfc_replacement_axiom_generate,
          fs_zfc_fixed_axioms, godel_unpair_value_pair]⟩
  | choice =>
      exact ⟨godel_pair_value 0 7, by
        simp [fs_zfc_replacement_axiom_generate,
          fs_zfc_fixed_axioms, godel_unpair_value_pair]⟩
  | @separation parameterCount schema =>
      exact ⟨godel_pair_value 1 <|
          godel_pair_value 0 <|
            fs_zfc_schema_certificate parameterCount
              (nat_sequence_code_value
                (fs_project_hilbert_token_tree schema.body).tokens), by
        simp [fs_zfc_replacement_axiom_generate,
          godel_unpair_value_pair,
          fs_zfc_separation_generate_certificate,
          fs_zfc_replacement_separation_hilbertize_schema]⟩
  | @replacement parameterCount schema =>
      exact ⟨godel_pair_value 1 <|
          godel_pair_value 2 <|
            fs_zfc_schema_certificate parameterCount
              (nat_sequence_code_value
                (fs_project_hilbert_token_tree schema.body).tokens), by
        simp [fs_zfc_replacement_axiom_generate,
          godel_unpair_value_pair,
          fs_zfc_replacement_generate_certificate,
          fs_zfc_replacement_replacement_hilbertize_schema]⟩

def fs_zfc_replacement_embedded_hilbert_generator :
    HilbertTheoryGenerator
      (Theory.hilbertize
        Nonlogical.BasicSetTheory.SetSort.set
        (fs_embed_project_theory fs_zfc_replacement_project_base_theory)) where
  generate certificate :=
    (fs_zfc_replacement_axiom_generate certificate).map
      (fun sentence =>
        Formula.hilbertize
          Nonlogical.BasicSetTheory.SetSort.set
          (fs_embed_project_sentence sentence))
  generate_sound := by
    intro certificate formula hGenerate
    cases hSource : fs_zfc_replacement_axiom_generate certificate with
    | none =>
        simp [hSource] at hGenerate
    | some source =>
        simp only [hSource, Option.map_some,
          Option.some.injEq] at hGenerate
        subst formula
        exact Theory.hilbertize_mem
          (show fs_embed_project_theory
              fs_zfc_replacement_project_base_theory
              (fs_embed_project_sentence source) from
            ⟨source,
              fs_zfc_replacement_axiom_generate_sound hSource,
              rfl⟩)
  generate_complete := by
    intro formula hTheory
    rcases hTheory with ⟨source, hSource, rfl⟩
    rcases hSource with ⟨sentence, hAxiom, rfl⟩
    rcases fs_zfc_replacement_axiom_generate_complete_hilbert
      hAxiom with ⟨certificate, hCertificate⟩
    exact ⟨certificate, by simp [hCertificate]⟩

def fs_zfc_replacement_project_base_hilbert_generator :
    HilbertTheoryGenerator
      (Theory.hilbertize
        Nonlogical.BasicSetTheory.SetSort.set
        (fs_project_base_theory
          fs_zfc_replacement_project_base_theory)) := by
  change HilbertTheoryGenerator
    (Theory.hilbertize
      Nonlogical.BasicSetTheory.SetSort.set
      (Theory.union fs_project_definition_theory
        (fs_embed_project_theory
          fs_zfc_replacement_project_base_theory)))
  rw [theory_hilbertize_union]
  exact HilbertTheoryGenerator.union
    (HilbertTheoryGenerator.hilbertize
      Nonlogical.BasicSetTheory.SetSort.set
      (HilbertTheoryGenerator.ofFinite
        fs_project_definition_finite_presentation))
    fs_zfc_replacement_embedded_hilbert_generator

def fs_zfc_replacement_support_generate (certificate : Nat) :
    Option SetFormula :=
  let tagPayload := godel_unpair_value certificate
  if tagPayload.1 = 0 then
    (HilbertTheoryGenerator.hilbertize
      Nonlogical.BasicSetTheory.SetSort.set
      (HilbertTheoryGenerator.ofFinite
        fs_internal_encoding_finite_presentation)).generate
      tagPayload.2
  else if tagPayload.1 = 1 then
    fs_zfc_replacement_embedded_hilbert_generator.generate
      (godel_pair_value 1 tagPayload.2)
  else if tagPayload.1 = 2 then
    (HilbertTheoryGenerator.hilbertize
      Nonlogical.BasicSetTheory.SetSort.set
      (HilbertTheoryGenerator.ofFinite
        fs_project_definition_finite_presentation)).generate
      tagPayload.2
  else if tagPayload.1 = 3 then
    fs_zfc_replacement_embedded_hilbert_generator.generate
      (godel_pair_value 0 tagPayload.2)
  else
    none

def fs_zfc_replacement_support_generator :
    HilbertTheoryGenerator fs_zfc_replacement_support_theory where
  generate := fs_zfc_replacement_support_generate
  generate_sound := by
    intro certificate formula hGenerate
    change Theory.hilbertize
      Nonlogical.BasicSetTheory.SetSort.set
      (Theory.union fs_internal_encoding_theory
        (Theory.union fs_project_definition_theory
          (fs_embed_project_theory
            fs_zfc_replacement_project_base_theory))) formula
    rw [theory_hilbertize_union, theory_hilbertize_union]
    unfold fs_zfc_replacement_support_generate at hGenerate
    dsimp only at hGenerate
    split at hGenerate
    next hInternal =>
      exact Or.inl <|
        (HilbertTheoryGenerator.hilbertize
          Nonlogical.BasicSetTheory.SetSort.set
          (HilbertTheoryGenerator.ofFinite
            fs_internal_encoding_finite_presentation)).generate_sound
          hGenerate
    next hNotInternal =>
      split at hGenerate
      next hBase =>
        exact Or.inr <| Or.inr <|
          fs_zfc_replacement_embedded_hilbert_generator.generate_sound
            hGenerate
      next hNotBase =>
        split at hGenerate
        next hProject =>
          exact Or.inr <| Or.inl <|
            (HilbertTheoryGenerator.hilbertize
              Nonlogical.BasicSetTheory.SetSort.set
              (HilbertTheoryGenerator.ofFinite
                fs_project_definition_finite_presentation)).generate_sound
              hGenerate
        next hNotProject =>
          split at hGenerate
          next hFixed =>
            exact Or.inr <| Or.inr <|
              fs_zfc_replacement_embedded_hilbert_generator.generate_sound
                hGenerate
          next hNotFixed =>
            simp at hGenerate
  generate_complete := by
    intro formula hFormula
    change Theory.hilbertize
      Nonlogical.BasicSetTheory.SetSort.set
      (Theory.union fs_internal_encoding_theory
        (Theory.union fs_project_definition_theory
          (fs_embed_project_theory
            fs_zfc_replacement_project_base_theory))) formula at hFormula
    rw [theory_hilbertize_union, theory_hilbertize_union] at hFormula
    rcases hFormula with hInternal | hBase
    · rcases
        (HilbertTheoryGenerator.hilbertize
          Nonlogical.BasicSetTheory.SetSort.set
          (HilbertTheoryGenerator.ofFinite
            fs_internal_encoding_finite_presentation)).generate_complete
          hInternal with ⟨certificate, hCertificate⟩
      exact ⟨godel_pair_value 0 certificate, by
        simp [fs_zfc_replacement_support_generate,
          godel_unpair_value_pair, hCertificate]⟩
    · rcases hBase with hProject | hEmbedded
      · rcases
          (HilbertTheoryGenerator.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (HilbertTheoryGenerator.ofFinite
              fs_project_definition_finite_presentation)).generate_complete
            hProject with ⟨certificate, hCertificate⟩
        exact ⟨godel_pair_value 2 certificate, by
          simp [fs_zfc_replacement_support_generate,
            godel_unpair_value_pair, hCertificate]⟩
      · rcases hEmbedded with
          ⟨source, hSource, rfl⟩
        rcases hSource with ⟨sentence, hAxiom, rfl⟩
        cases hAxiom with
        | extensionality =>
            exact ⟨godel_pair_value 3 0, by
              simp [fs_zfc_replacement_support_generate,
                fs_zfc_replacement_embedded_hilbert_generator,
                fs_zfc_replacement_axiom_generate,
                fs_zfc_fixed_axioms,
                godel_unpair_value_pair]⟩
        | emptySet =>
            exact ⟨godel_pair_value 3 1, by
              simp [fs_zfc_replacement_support_generate,
                fs_zfc_replacement_embedded_hilbert_generator,
                fs_zfc_replacement_axiom_generate,
                fs_zfc_fixed_axioms,
                godel_unpair_value_pair]⟩
        | pairing =>
            exact ⟨godel_pair_value 3 2, by
              simp [fs_zfc_replacement_support_generate,
                fs_zfc_replacement_embedded_hilbert_generator,
                fs_zfc_replacement_axiom_generate,
                fs_zfc_fixed_axioms,
                godel_unpair_value_pair]⟩
        | union =>
            exact ⟨godel_pair_value 3 3, by
              simp [fs_zfc_replacement_support_generate,
                fs_zfc_replacement_embedded_hilbert_generator,
                fs_zfc_replacement_axiom_generate,
                fs_zfc_fixed_axioms,
                godel_unpair_value_pair]⟩
        | powerSet =>
            exact ⟨godel_pair_value 3 4, by
              simp [fs_zfc_replacement_support_generate,
                fs_zfc_replacement_embedded_hilbert_generator,
                fs_zfc_replacement_axiom_generate,
                fs_zfc_fixed_axioms,
                godel_unpair_value_pair]⟩
        | infinity =>
            exact ⟨godel_pair_value 3 5, by
              simp [fs_zfc_replacement_support_generate,
                fs_zfc_replacement_embedded_hilbert_generator,
                fs_zfc_replacement_axiom_generate,
                fs_zfc_fixed_axioms,
                godel_unpair_value_pair]⟩
        | foundation =>
            exact ⟨godel_pair_value 3 6, by
              simp [fs_zfc_replacement_support_generate,
                fs_zfc_replacement_embedded_hilbert_generator,
                fs_zfc_replacement_axiom_generate,
                fs_zfc_fixed_axioms,
                godel_unpair_value_pair]⟩
        | choice =>
            exact ⟨godel_pair_value 3 7, by
              simp [fs_zfc_replacement_support_generate,
                fs_zfc_replacement_embedded_hilbert_generator,
                fs_zfc_replacement_axiom_generate,
                fs_zfc_fixed_axioms,
                godel_unpair_value_pair]⟩
        | @separation parameterCount schema =>
            exact
              ⟨godel_pair_value 1 <|
                  godel_pair_value 0 <|
                    fs_zfc_schema_certificate parameterCount
                      (nat_sequence_code_value
                        (fs_project_hilbert_token_tree
                          schema.body).tokens), by
                simp [fs_zfc_replacement_support_generate,
                  fs_zfc_replacement_embedded_hilbert_generator,
                  fs_zfc_replacement_axiom_generate,
                  godel_unpair_value_pair,
                  fs_zfc_separation_generate_certificate,
                  fs_zfc_replacement_separation_hilbertize_schema]⟩
        | @replacement parameterCount schema =>
            exact
              ⟨godel_pair_value 1 <|
                  godel_pair_value 2 <|
                    fs_zfc_schema_certificate parameterCount
                      (nat_sequence_code_value
                        (fs_project_hilbert_token_tree
                          schema.body).tokens), by
                simp [fs_zfc_replacement_support_generate,
                  fs_zfc_replacement_embedded_hilbert_generator,
                  fs_zfc_replacement_axiom_generate,
                  godel_unpair_value_pair,
                  fs_zfc_replacement_generate_certificate,
                  fs_zfc_replacement_replacement_hilbertize_schema]⟩

@[simp]
theorem fs_zfc_replacement_support_generator_generate
    (certificate : Nat) :
    fs_zfc_replacement_support_generator.generate certificate =
      fs_zfc_replacement_support_generate certificate := by
  rfl

theorem fs_zfc_replacement_support_generate_admissible
    {certificate : Nat} {formula : SetFormula}
    (hGenerate :
      fs_zfc_replacement_support_generate certificate =
        some formula) :
    Formula.Admissible formula := by
  have hTheory :
      fs_zfc_replacement_support_theory formula :=
    fs_zfc_replacement_support_generator.generate_sound
      (by simpa using hGenerate)
  change Theory.hilbertize
    Nonlogical.BasicSetTheory.SetSort.set
    fs_zfc_replacement_support_raw_theory formula at hTheory
  rcases hTheory with ⟨source, hSource, rfl⟩
  exact Formula.Admissible.hilbertize
    (fs_zfc_replacement_support_raw_theory_sentence hSource).1

theorem fs_zfc_replacement_support_generate_hilbertize_eq_self
    {certificate : Nat} {formula : SetFormula}
    (hGenerate :
      fs_zfc_replacement_support_generate certificate =
        some formula) :
    Formula.hilbertize
      Nonlogical.BasicSetTheory.SetSort.set formula = formula := by
  have hTheory :
      fs_zfc_replacement_support_theory formula :=
    fs_zfc_replacement_support_generator.generate_sound
      (by simpa using hGenerate)
  change Theory.hilbertize
    Nonlogical.BasicSetTheory.SetSort.set
    fs_zfc_replacement_support_raw_theory formula at hTheory
  rcases hTheory with ⟨source, hSource, rfl⟩
  exact Formula.hilbertize_idempotent
    Nonlogical.BasicSetTheory.SetSort.set source

def fs_zfc_replacement_support_enumeration :
    HilbertTheoryEnumeration fs_zfc_replacement_support_theory :=
  HilbertTheoryGenerator.toEnumeration
    fs_zfc_replacement_support_generator
    GodelQuotation.SyntaxCoding.formula_encode
    GodelQuotation.SyntaxCoding.formula_encode_injective

end ProofCode
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
