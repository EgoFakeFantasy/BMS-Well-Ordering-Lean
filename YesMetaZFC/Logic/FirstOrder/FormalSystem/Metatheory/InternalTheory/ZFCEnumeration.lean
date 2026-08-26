import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ProjectTokenCoding
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFC
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.RecursiveEnumeration
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.SyntaxCoding
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SchemaPlugin

/-!
# ZFC 内部理论的构造性公理生成器

ZFC 的固定公理由有限列表生成；分离与收集模式由携带参数个数、Hilbert token
序列码的有限证书生成。整个生成器只做自然数与有限语法计算，不使用选择公理，也
不把 `ZFC sentence` 当作可判定黑箱。
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

/-! ## Project 层的 ZFC 公理生成 -/

/-- ZFC 的八条固定公理，schema 实例不在此列表中。 -/
def fs_zfc_fixed_axioms :
    List FsProjectSentence :=
  [ Axioms.extensionality,
    Axioms.emptySet,
    Axioms.pairing,
    Axioms.union,
    Axioms.powerSet,
    Axioms.infinity,
    Axioms.foundation,
    Axioms.choice ]

/-- schema 证书的公共 payload：参数个数与 body token 序列码。 -/
def fs_zfc_schema_certificate
    (parameterCount bodyTokenCode : Nat) :
    Nat :=
  godel_pair_value parameterCount
    bodyTokenCode

/-- 分离 schema payload 的有限解码与实例生成。 -/
def fs_zfc_separation_generate
    (payload : Nat) :
    Option FsProjectSentence :=
  let schemaPayload :=
    godel_unpair_value payload
  (fs_project_unary_schema_hilbert_decode
    schemaPayload.1
    schemaPayload.2).map
      Axioms.Schema.separation

/-- 收集 schema payload 的有限解码与实例生成。 -/
def fs_zfc_collection_generate
    (payload : Nat) :
    Option FsProjectSentence :=
  let schemaPayload :=
    godel_unpair_value payload
  (fs_project_binary_schema_hilbert_decode
    schemaPayload.1
    schemaPayload.2).map
      Axioms.Schema.collection

/-- replacement schema payload 的有限解码与实例生成。 -/
def fs_zfc_replacement_generate
    (payload : Nat) :
    Option FsProjectSentence :=
  let schemaPayload :=
    godel_unpair_value payload
  (fs_project_binary_schema_hilbert_decode
    schemaPayload.1
    schemaPayload.2).map
      Axioms.Schema.replacement

/-- 一元 schema 的规范 token payload 精确生成 Hilbert 化分离实例。 -/
@[simp]
theorem fs_zfc_separation_generate_certificate
    (parameterCount : Nat)
    (schema : Project.UnarySchema parameterCount) :
    fs_zfc_separation_generate
        (fs_zfc_schema_certificate
          parameterCount
          (nat_sequence_code_value
            (fs_project_hilbert_token_tree schema.body).tokens)) =
      some (Axioms.Schema.separation
        (fs_project_unary_schema_hilbertize schema)) := by
  unfold fs_zfc_separation_generate
  unfold fs_zfc_schema_certificate
  rw [godel_unpair_value_pair]
  dsimp only
  simp

/-- 二元 schema 的规范 token payload 精确生成 Hilbert 化收集实例。 -/
@[simp]
theorem fs_zfc_collection_generate_certificate
    (parameterCount : Nat)
    (schema : Project.BinarySchema parameterCount) :
    fs_zfc_collection_generate
        (fs_zfc_schema_certificate
          parameterCount
          (nat_sequence_code_value
            (fs_project_hilbert_token_tree schema.body).tokens)) =
      some (Axioms.Schema.collection
        (fs_project_binary_schema_hilbertize schema)) := by
  unfold fs_zfc_collection_generate
  unfold fs_zfc_schema_certificate
  rw [godel_unpair_value_pair]
  dsimp only
  simp

/-- 二元 schema 的规范 token payload 精确生成 Hilbert 化 replacement 实例。 -/
@[simp]
theorem fs_zfc_replacement_generate_certificate
    (parameterCount : Nat)
    (schema : Project.BinarySchema parameterCount) :
    fs_zfc_replacement_generate
        (fs_zfc_schema_certificate
          parameterCount
          (nat_sequence_code_value
            (fs_project_hilbert_token_tree schema.body).tokens)) =
      some (Axioms.Schema.replacement
        (fs_project_binary_schema_hilbertize schema)) := by
  unfold fs_zfc_replacement_generate
  unfold fs_zfc_schema_certificate
  rw [godel_unpair_value_pair]
  dsimp only
  simp

/-- 分离 schema 的外部生成器插件。 -/
def fs_zfc_separation_generator_plugin :
    ProofT.SchemaGeneratorPlugin FsProjectSentence where
  tag := 0
  generate := fs_zfc_separation_generate

/-- 收集 schema 的外部生成器插件。 -/
def fs_zfc_collection_generator_plugin :
    ProofT.SchemaGeneratorPlugin FsProjectSentence where
  tag := 1
  generate := fs_zfc_collection_generate

/-- replacement schema 的外部生成器插件。 -/
def fs_zfc_replacement_generator_plugin :
    ProofT.SchemaGeneratorPlugin FsProjectSentence where
  tag := 2
  generate := fs_zfc_replacement_generate

/-- 当前 ZFC presentation 启用的外部 schema 生成器。 -/
def fs_zfc_schema_generator_plugins :
    List (ProofT.SchemaGeneratorPlugin FsProjectSentence) :=
  [fs_zfc_separation_generator_plugin,
    fs_zfc_collection_generator_plugin]

/-- 以 replacement 取代 collection 的外部 schema 生成器表。 -/
def fs_zfc_replacement_schema_generator_plugins :
    List (ProofT.SchemaGeneratorPlugin FsProjectSentence) :=
  [fs_zfc_separation_generator_plugin,
    fs_zfc_replacement_generator_plugin]

@[simp]
theorem fs_zfc_schema_generator_plugins_tag_zero
    (payload : Nat) :
    ProofT.SchemaGeneratorPlugin.generate_list
        fs_zfc_schema_generator_plugins 0 payload =
      fs_zfc_separation_generate payload := by
  simp [ProofT.SchemaGeneratorPlugin.generate_list,
    fs_zfc_schema_generator_plugins,
    fs_zfc_separation_generator_plugin]

@[simp]
theorem fs_zfc_schema_generator_plugins_tag_one
    (payload : Nat) :
    ProofT.SchemaGeneratorPlugin.generate_list
        fs_zfc_schema_generator_plugins 1 payload =
      fs_zfc_collection_generate payload := by
  simp [ProofT.SchemaGeneratorPlugin.generate_list,
    fs_zfc_schema_generator_plugins,
    fs_zfc_separation_generator_plugin,
    fs_zfc_collection_generator_plugin]

@[simp]
theorem fs_zfc_replacement_schema_generator_plugins_tag_zero
    (payload : Nat) :
    ProofT.SchemaGeneratorPlugin.generate_list
        fs_zfc_replacement_schema_generator_plugins 0 payload =
      fs_zfc_separation_generate payload := by
  simp [ProofT.SchemaGeneratorPlugin.generate_list,
    fs_zfc_replacement_schema_generator_plugins,
    fs_zfc_separation_generator_plugin]

@[simp]
theorem fs_zfc_replacement_schema_generator_plugins_tag_two
    (payload : Nat) :
    ProofT.SchemaGeneratorPlugin.generate_list
        fs_zfc_replacement_schema_generator_plugins 2 payload =
      fs_zfc_replacement_generate payload := by
  simp [ProofT.SchemaGeneratorPlugin.generate_list,
    fs_zfc_replacement_schema_generator_plugins,
    fs_zfc_separation_generator_plugin,
    fs_zfc_replacement_generator_plugin]

/-- 对当前 ZFC 外部 schema 生成器表作穷尽消去。 -/
theorem fs_zfc_schema_generator_plugins_elim
    {P : ProofT.SchemaGeneratorPlugin FsProjectSentence → Prop}
    (hSeparation :
      P fs_zfc_separation_generator_plugin)
    (hCollection :
      P fs_zfc_collection_generator_plugin) :
    ∀ plugin, plugin ∈ fs_zfc_schema_generator_plugins →
      P plugin := by
  intro plugin hPlugin
  simp [fs_zfc_schema_generator_plugins] at hPlugin
  rcases hPlugin with rfl | rfl
  · exact hSeparation
  · exact hCollection

/-- 对 replacement presentation 的外部 schema 生成器表作穷尽消去。 -/
theorem fs_zfc_replacement_schema_generator_plugins_elim
    {P : ProofT.SchemaGeneratorPlugin FsProjectSentence → Prop}
    (hSeparation :
      P fs_zfc_separation_generator_plugin)
    (hReplacement :
      P fs_zfc_replacement_generator_plugin) :
    ∀ plugin,
      plugin ∈ fs_zfc_replacement_schema_generator_plugins →
        P plugin := by
  intro plugin hPlugin
  simp [fs_zfc_replacement_schema_generator_plugins] at hPlugin
  rcases hPlugin with rfl | rfl
  · exact hSeparation
  · exact hReplacement

/--
由固定公理表与任意 schema 生成器表合成 Project 公理生成器。

外层标签 `0` 选择固定公理列表；外层标签 `1` 选择 schema。schema 内层标签由
传入的插件表调度。
-/
def fs_zfc_axiom_generate_with_schema_plugins
    (plugins :
      List (ProofT.SchemaGeneratorPlugin FsProjectSentence))
    (certificate : Nat) :
    Option FsProjectSentence :=
  let tagPayload := godel_unpair_value certificate
  if tagPayload.1 = 0 then
    fs_zfc_fixed_axioms[tagPayload.2]?
  else if tagPayload.1 = 1 then
    let schemaTagPayload :=
      godel_unpair_value tagPayload.2
    ProofT.SchemaGeneratorPlugin.generate_list
      plugins
      schemaTagPayload.1 schemaTagPayload.2
  else
    none

@[simp]
theorem fs_zfc_axiom_generate_with_schema_plugins_eq
    (plugins :
      List (ProofT.SchemaGeneratorPlugin FsProjectSentence))
    (certificate : Nat) :
    fs_zfc_axiom_generate_with_schema_plugins
        plugins certificate =
      let tagPayload := godel_unpair_value certificate
      if tagPayload.1 = 0 then
        fs_zfc_fixed_axioms[tagPayload.2]?
      else if tagPayload.1 = 1 then
        let schemaTagPayload :=
          godel_unpair_value tagPayload.2
        ProofT.SchemaGeneratorPlugin.generate_list
          plugins schemaTagPayload.1 schemaTagPayload.2
      else
        none := by
  rfl

/-- 当前 ZFC presentation 的 Project 公理生成器：分离加收集。 -/
def fs_zfc_axiom_generate
    (certificate : Nat) :
    Option FsProjectSentence :=
  fs_zfc_axiom_generate_with_schema_plugins
    fs_zfc_schema_generator_plugins certificate

/-- replacement presentation 的 Project 公理生成器：分离加替换。 -/
def fs_zfc_replacement_axiom_generate
    (certificate : Nat) :
    Option FsProjectSentence :=
  fs_zfc_axiom_generate_with_schema_plugins
    fs_zfc_replacement_schema_generator_plugins certificate

@[simp]
theorem fs_zfc_replacement_axiom_generate_certificate
    (parameterCount : Nat)
    (schema : Project.BinarySchema parameterCount) :
    fs_zfc_replacement_axiom_generate
        (godel_pair_value 1 <|
          godel_pair_value 2 <|
            fs_zfc_schema_certificate
              parameterCount
              (nat_sequence_code_value
                (fs_project_hilbert_token_tree
                  schema.body).tokens)) =
      some (Axioms.Schema.replacement
        (fs_project_binary_schema_hilbertize schema)) := by
  simp [fs_zfc_replacement_axiom_generate,
    godel_unpair_value_pair,
    fs_zfc_replacement_generate_certificate]

/-- 固定公理列表中的每个元素都是 ZFC 公理。 -/
private theorem fs_zfc_fixed_axioms_sound
    {sentence : FsProjectSentence}
    (hMember : sentence ∈ fs_zfc_fixed_axioms) :
    _root_.YesMetaZFC.SetTheory.ZFC sentence := by
  simp [fs_zfc_fixed_axioms] at hMember
  rcases hMember with
    rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact .zf .extensionality
  · exact .zf .emptySet
  · exact .zf .pairing
  · exact .zf .union
  · exact .zf .powerSet
  · exact .zf .infinity
  · exact .zf .foundation
  · exact .choice

/-- 成功解码出的分离 schema payload 给出 ZFC 公理。 -/
private theorem fs_zfc_separation_generate_sound
    {payload : Nat}
    {sentence : FsProjectSentence}
    (hGenerate :
      fs_zfc_separation_generate payload =
        some sentence) :
    _root_.YesMetaZFC.SetTheory.ZFC sentence := by
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
      exact .zf (.separation schema)

/-- 成功解码出的收集 schema payload 给出 ZFC 公理。 -/
private theorem fs_zfc_collection_generate_sound
    {payload : Nat}
    {sentence : FsProjectSentence}
    (hGenerate :
      fs_zfc_collection_generate payload =
        some sentence) :
    _root_.YesMetaZFC.SetTheory.ZFC sentence := by
  unfold fs_zfc_collection_generate at hGenerate
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
      exact .zf (.collection schema)

/-- 任意成功生成的 Project 句都是 ZFC 公理。 -/
theorem fs_zfc_axiom_generate_sound
    {certificate : Nat}
    {sentence : FsProjectSentence}
    (hGenerate :
      fs_zfc_axiom_generate certificate =
        some sentence) :
    _root_.YesMetaZFC.SetTheory.ZFC sentence := by
  unfold fs_zfc_axiom_generate at hGenerate
  rw [fs_zfc_axiom_generate_with_schema_plugins_eq] at hGenerate
  dsimp only at hGenerate
  split at hGenerate
  next hFixed =>
    apply fs_zfc_fixed_axioms_sound
    exact List.mem_of_getElem? hGenerate
  next hNotFixed =>
    split at hGenerate
    next hSchema =>
      exact
        ProofT.SchemaGeneratorPlugin.generate_list_sound
          fs_zfc_schema_generator_plugins
          (godel_unpair_value
            (godel_unpair_value certificate).2).1
          (godel_unpair_value
            (godel_unpair_value certificate).2).2
          (fs_zfc_schema_generator_plugins_elim
            fs_zfc_separation_generate_sound
            fs_zfc_collection_generate_sound)
          hGenerate
    next hNotSchema =>
      simp at hGenerate

/-- 分离 schema 的 token 解码只改变了已经 Hilbert 归约的体。 -/
private theorem fs_zfc_separation_hilbertize_schema
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

/-- 收集 schema 的 token 解码只改变了已经 Hilbert 归约的体。 -/
private theorem fs_zfc_collection_hilbertize_schema
    {parameterCount : Nat}
    (schema : Project.BinarySchema parameterCount) :
    Formula.hilbertize
        Nonlogical.BasicSetTheory.SetSort.set
        (fs_embed_project_sentence
          (Axioms.Schema.collection
            (fs_project_binary_schema_hilbertize schema))) =
      Formula.hilbertize
        Nonlogical.BasicSetTheory.SetSort.set
          (fs_embed_project_sentence
            (Axioms.Schema.collection schema)) := by
  simp only [fs_embed_project_sentence]
  rw [← fs_embed_project_hilbertize,
    ← fs_embed_project_hilbertize]
  congr 1
  simp only [Axioms.Schema.collection,
    Project.Sentence.forallClosure]
  rw [fs_project_hilbertize_forallClosure,
    fs_project_hilbertize_forallClosure]
  simp [Axioms.Schema.collectionCore,
    fs_project_binary_schema_hilbertize,
    fs_project_hilbertize,
    fs_project_hilbertize_rename_idempotent,
    Project.Formula.forallMem,
    Project.Formula.existsMem]

/-- 每条 ZFC Project 公理都由某个自然数证书生成。 -/
theorem fs_zfc_axiom_generate_complete_hilbert
    {sentence : FsProjectSentence}
    (hZFC :
      _root_.YesMetaZFC.SetTheory.ZFC sentence) :
    ∃ certificate,
      (fs_zfc_axiom_generate certificate).map
          (fun generated =>
            Formula.hilbertize
              Nonlogical.BasicSetTheory.SetSort.set
              (fs_embed_project_sentence generated)) =
        some (Formula.hilbertize
          Nonlogical.BasicSetTheory.SetSort.set
          (fs_embed_project_sentence sentence)) := by
  cases hZFC with
  | zf hZF =>
      cases hZF with
      | extensionality =>
          exact
            ⟨godel_pair_value 0 0, by
              simp [fs_zfc_axiom_generate,
                fs_zfc_fixed_axioms,
                godel_unpair_value_pair]⟩
      | emptySet =>
          exact
            ⟨godel_pair_value 0 1, by
              simp [fs_zfc_axiom_generate,
                fs_zfc_fixed_axioms,
                godel_unpair_value_pair]⟩
      | pairing =>
          exact
            ⟨godel_pair_value 0 2, by
              simp [fs_zfc_axiom_generate,
                fs_zfc_fixed_axioms,
                godel_unpair_value_pair]⟩
      | union =>
          exact
            ⟨godel_pair_value 0 3, by
              simp [fs_zfc_axiom_generate,
                fs_zfc_fixed_axioms,
                godel_unpair_value_pair]⟩
      | powerSet =>
          exact
            ⟨godel_pair_value 0 4, by
              simp [fs_zfc_axiom_generate,
                fs_zfc_fixed_axioms,
                godel_unpair_value_pair]⟩
      | infinity =>
          exact
            ⟨godel_pair_value 0 5, by
              simp [fs_zfc_axiom_generate,
                fs_zfc_fixed_axioms,
                godel_unpair_value_pair]⟩
      | foundation =>
          exact
            ⟨godel_pair_value 0 6, by
              simp [fs_zfc_axiom_generate,
                fs_zfc_fixed_axioms,
                godel_unpair_value_pair]⟩
      | @separation parameterCount schema =>
          refine
            ⟨godel_pair_value 1 <|
                godel_pair_value 0 <|
                  fs_zfc_schema_certificate
                    parameterCount
                    (nat_sequence_code_value
                      (fs_project_hilbert_token_tree
                        schema.body).tokens),
              ?_⟩
          simp [fs_zfc_axiom_generate,
            godel_unpair_value_pair,
            fs_zfc_separation_generate_certificate,
            fs_zfc_separation_hilbertize_schema]
      | @collection parameterCount schema =>
          refine
            ⟨godel_pair_value 1 <|
                godel_pair_value 1 <|
                  fs_zfc_schema_certificate
                    parameterCount
                    (nat_sequence_code_value
                      (fs_project_hilbert_token_tree
                        schema.body).tokens),
              ?_⟩
          simp [fs_zfc_axiom_generate,
            godel_unpair_value_pair,
            fs_zfc_collection_generate_certificate,
            fs_zfc_collection_hilbertize_schema]
  | choice =>
      exact
        ⟨godel_pair_value 0 7, by
          simp [fs_zfc_axiom_generate,
            fs_zfc_fixed_axioms,
            godel_unpair_value_pair]⟩

/-! ## FormalSystem 嵌入 -/

/-- ZFC Project 公理嵌入后直接生成其 Hilbert 归约像。 -/
def fs_zfc_embedded_hilbert_generator :
    HilbertTheoryGenerator
      (Theory.hilbertize
        Nonlogical.BasicSetTheory.SetSort.set
        (fs_embed_project_theory
          _root_.YesMetaZFC.SetTheory.ZFC)) where
  generate certificate :=
    (fs_zfc_axiom_generate certificate).map
      (fun sentence =>
        Formula.hilbertize
          Nonlogical.BasicSetTheory.SetSort.set
          (fs_embed_project_sentence sentence))
  generate_sound := by
    intro certificate formula hGenerate
    cases hAxiom :
        fs_zfc_axiom_generate certificate with
    | none =>
        simp [hAxiom] at hGenerate
    | some sentence =>
        simp only [hAxiom, Option.map_some,
          Option.some.injEq] at hGenerate
        subst formula
        exact Theory.hilbertize_mem
          (show fs_embed_project_theory
              _root_.YesMetaZFC.SetTheory.ZFC
              (fs_embed_project_sentence sentence) from
            ⟨sentence,
              fs_zfc_axiom_generate_sound hAxiom,
              rfl⟩)
  generate_complete := by
    intro formula hTheory
    rcases hTheory with
      ⟨source, hSource, rfl⟩
    rcases hSource with
      ⟨sentence, hZFC, rfl⟩
    rcases fs_zfc_axiom_generate_complete_hilbert hZFC with
      ⟨certificate, hCertificate⟩
    exact ⟨certificate, by simp [hCertificate]⟩

/-! ## 内部支持理论的有限 presentation -/

/--
quotation 与 Hilbert 逻辑规则编码支持层的显式有限公理表。

该定义与现有 `fs_internal_encoding_theory_finitely_axiomatized` 使用同一结构展开，
但保留真实列表数据，后续生成器无需从存在性命题中抽取见证。
-/
def fs_internal_encoding_finite_presentation :
    HilbertFinitePresentation
      fs_internal_encoding_theory := by
  unfold fs_internal_encoding_theory
  apply HilbertFinitePresentation.union
  · apply HilbertFinitePresentation.union
    · unfold GodelQuotation.code_naming_theory
      repeat
        first
        | apply HilbertFinitePresentation.insert
        | apply HilbertFinitePresentation.union
        | exact HilbertFinitePresentation.singleton _
        | exact HilbertFinitePresentation.empty
        | unfold GodelQuotation.godel_quotation_theory
        | unfold GodelQuotation.standard_sequence_semantics_theory
        | unfold membership_irreflexive_theory
        | unfold finite_sequence_flatten_theory
        | unfold finite_sequence_space_theory
        | unfold infinity_theory
        | unfold empty_set_symbol_theory
        | unfold successor_operator_theory
        | unfold binary_union_operator_theory
        | unfold singleton_operator_theory
        | unfold ordered_pair_operator_theory
        | unfold function_application_theory
        | unfold natural_exponentiation_theory
        | unfold substitution_variable_theory
        | unfold formula_code_theory
        | unfold formula_constructor_theory
        | unfold symbol_code_operator_theory
        | unfold formal_language_encoding_theory
    · unfold godel_pairing_theory
      repeat
        first
        | apply HilbertFinitePresentation.insert
        | apply HilbertFinitePresentation.union
        | exact HilbertFinitePresentation.singleton _
        | exact HilbertFinitePresentation.empty
        | unfold omega_pair_order_theory
        | unfold natural_difference_theory
        | unfold omega_recursive_sequence_theory
        | unfold recursive_sequence_space_theory
        | unfold finite_sequence_space_theory
        | unfold cardinality_classification_theory
        | unfold countably_infinite_predicate_theory
        | unfold uncountable_predicate_theory
        | unfold countable_predicate_theory
        | unfold infinite_predicate_theory
        | unfold natural_exponentiation_theory
        | unfold natural_multiplication_theory
        | unfold natural_addition_theory
        | unfold natural_set_theory
        | unfold natural_subset_type_theory
        | unfold natural_order_type_theory
        | unfold bounded_subset_theory
        | unfold unbounded_subset_theory
        | unfold infinity_theory
        | unfold empty_set_theory
        | unfold extensionality_theory
  · unfold logical_rule_encoding_theory
    repeat
      first
      | apply HilbertFinitePresentation.insert
      | apply HilbertFinitePresentation.union
      | exact HilbertFinitePresentation.singleton _
      | exact HilbertFinitePresentation.empty
      | unfold logical_axiom_code_theory
      | unfold equality_axiom_schema_theory
      | unfold quantifier_axiom_schema_theory
      | unfold propositional_axiom_schema_theory
      | unfold substitutability_theory
      | unfold expression_encoding_theory
      | unfold occurrence_theory
      | unfold substitution_variable_theory
      | unfold formula_code_theory
      | unfold formula_constructor_theory
      | unfold symbol_code_operator_theory
      | unfold formal_language_encoding_theory

/-- Project 定义原子解释层的显式有限公理表。 -/
def fs_project_definition_finite_presentation :
    HilbertFinitePresentation
      fs_project_definition_theory := by
  unfold fs_project_definition_theory
  repeat
    first
    | apply HilbertFinitePresentation.union
    | apply HilbertFinitePresentation.insert
    | exact HilbertFinitePresentation.singleton _
    | exact HilbertFinitePresentation.empty
    | unfold subset_theory
    | unfold extensionality_theory

/-! ## ZFC 内部 Hilbert 理论的生成器与 verifier -/

/-- Project 定义层与 ZFC 公理像的联合生成器。 -/
def fs_zfc_project_base_hilbert_generator :
    HilbertTheoryGenerator
      (Theory.hilbertize
        Nonlogical.BasicSetTheory.SetSort.set
        (fs_project_base_theory
          _root_.YesMetaZFC.SetTheory.ZFC)) := by
  change HilbertTheoryGenerator
    (Theory.hilbertize
      Nonlogical.BasicSetTheory.SetSort.set
      (Theory.union
        fs_project_definition_theory
        (fs_embed_project_theory
          _root_.YesMetaZFC.SetTheory.ZFC)))
  rw [theory_hilbertize_union]
  exact HilbertTheoryGenerator.union
    (HilbertTheoryGenerator.hilbertize
      Nonlogical.BasicSetTheory.SetSort.set
      (HilbertTheoryGenerator.ofFinite
        fs_project_definition_finite_presentation))
    fs_zfc_embedded_hilbert_generator

/-!
完整支持理论使用扁平证书命名空间，避免 Project 定义与 schema 证书发生数值碰撞：

* `0`：内部编码有限表；
* `1`：嵌入 ZFC 的 schema，payload 仍由 schema 标签区分分离与收集；
* `2`：Project 定义有限表；
* `3`：嵌入 ZFC 的固定公理有限表。

这四个外层标签只服务于证书枚举，不改变对象理论或内部公式语言。
-/
def fs_zfc_support_generate (certificate : Nat) :
    Option SetFormula :=
  let tagPayload := godel_unpair_value certificate
  if tagPayload.1 = 0 then
    (HilbertTheoryGenerator.hilbertize
      Nonlogical.BasicSetTheory.SetSort.set
      (HilbertTheoryGenerator.ofFinite
        fs_internal_encoding_finite_presentation)).generate
      tagPayload.2
  else if tagPayload.1 = 1 then
    fs_zfc_embedded_hilbert_generator.generate
      (godel_pair_value 1 tagPayload.2)
  else if tagPayload.1 = 2 then
    (HilbertTheoryGenerator.hilbertize
      Nonlogical.BasicSetTheory.SetSort.set
      (HilbertTheoryGenerator.ofFinite
        fs_project_definition_finite_presentation)).generate
      tagPayload.2
  else if tagPayload.1 = 3 then
    fs_zfc_embedded_hilbert_generator.generate
      (godel_pair_value 0 tagPayload.2)
  else
    none

/-- 完整 ZFC 内部 Hilbert 理论的构造性公理生成器。 -/
def fs_zfc_support_generator :
    HilbertTheoryGenerator
      fs_zfc_support_theory :=
  {
    generate := fs_zfc_support_generate
    generate_sound := by
      intro certificate formula hGenerate
      change
        Theory.hilbertize
          Nonlogical.BasicSetTheory.SetSort.set
          (Theory.union
            fs_internal_encoding_theory
            (Theory.union
              fs_project_definition_theory
              (fs_embed_project_theory
                _root_.YesMetaZFC.SetTheory.ZFC))) formula
      rw [theory_hilbertize_union]
      rw [theory_hilbertize_union]
      unfold fs_zfc_support_generate at hGenerate
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
        next hSchema =>
          exact Or.inr <| Or.inr <|
            fs_zfc_embedded_hilbert_generator.generate_sound hGenerate
        next hNotSchema =>
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
                fs_zfc_embedded_hilbert_generator.generate_sound hGenerate
            next hNotFixed =>
              simp at hGenerate
    generate_complete := by
      intro formula hTheory
      change
        Theory.hilbertize
          Nonlogical.BasicSetTheory.SetSort.set
          (Theory.union
            fs_internal_encoding_theory
            (Theory.union
              fs_project_definition_theory
              (fs_embed_project_theory
                _root_.YesMetaZFC.SetTheory.ZFC))) formula at hTheory
      rw [theory_hilbertize_union] at hTheory
      rw [theory_hilbertize_union] at hTheory
      rcases hTheory with hInternal | hBase
      · rcases
          (HilbertTheoryGenerator.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (HilbertTheoryGenerator.ofFinite
              fs_internal_encoding_finite_presentation)).generate_complete
            hInternal with
          ⟨certificate, hCertificate⟩
        exact ⟨godel_pair_value 0 certificate, by
          simp [fs_zfc_support_generate,
            godel_unpair_value_pair, hCertificate]⟩
      · rcases hBase with hProject | hEmbedded
        · rcases
            (HilbertTheoryGenerator.hilbertize
              Nonlogical.BasicSetTheory.SetSort.set
              (HilbertTheoryGenerator.ofFinite
                fs_project_definition_finite_presentation)).generate_complete
              hProject with
            ⟨certificate, hCertificate⟩
          exact ⟨godel_pair_value 2 certificate, by
            simp [fs_zfc_support_generate,
              godel_unpair_value_pair, hCertificate]⟩
        · rcases hEmbedded with
            ⟨formulaSource, hSentence, hFormula⟩
          subst formula
          rcases hSentence with
            ⟨sentence, hZFC, rfl⟩
          cases hZFC with
          | zf hZF =>
              cases hZF with
              | extensionality =>
                  exact ⟨godel_pair_value 3 0, by
                    simp [fs_zfc_support_generate,
                      fs_zfc_embedded_hilbert_generator,
                      fs_zfc_axiom_generate, fs_zfc_fixed_axioms,
                      godel_unpair_value_pair]⟩
              | emptySet =>
                  exact ⟨godel_pair_value 3 1, by
                    simp [fs_zfc_support_generate,
                      fs_zfc_embedded_hilbert_generator,
                      fs_zfc_axiom_generate, fs_zfc_fixed_axioms,
                      godel_unpair_value_pair]⟩
              | pairing =>
                  exact ⟨godel_pair_value 3 2, by
                    simp [fs_zfc_support_generate,
                      fs_zfc_embedded_hilbert_generator,
                      fs_zfc_axiom_generate, fs_zfc_fixed_axioms,
                      godel_unpair_value_pair]⟩
              | union =>
                  exact ⟨godel_pair_value 3 3, by
                    simp [fs_zfc_support_generate,
                      fs_zfc_embedded_hilbert_generator,
                      fs_zfc_axiom_generate, fs_zfc_fixed_axioms,
                      godel_unpair_value_pair]⟩
              | powerSet =>
                  exact ⟨godel_pair_value 3 4, by
                    simp [fs_zfc_support_generate,
                      fs_zfc_embedded_hilbert_generator,
                      fs_zfc_axiom_generate, fs_zfc_fixed_axioms,
                      godel_unpair_value_pair]⟩
              | infinity =>
                  exact ⟨godel_pair_value 3 5, by
                    simp [fs_zfc_support_generate,
                      fs_zfc_embedded_hilbert_generator,
                      fs_zfc_axiom_generate, fs_zfc_fixed_axioms,
                      godel_unpair_value_pair]⟩
              | foundation =>
                  exact ⟨godel_pair_value 3 6, by
                    simp [fs_zfc_support_generate,
                      fs_zfc_embedded_hilbert_generator,
                      fs_zfc_axiom_generate, fs_zfc_fixed_axioms,
                      godel_unpair_value_pair]⟩
              | @separation parameterCount schema =>
                  exact
                    ⟨godel_pair_value 1
                        (godel_pair_value 0
                          (fs_zfc_schema_certificate
                            parameterCount
                            (nat_sequence_code_value
                              (fs_project_hilbert_token_tree
                                schema.body).tokens))), by
                      simp [fs_zfc_support_generate,
                        fs_zfc_embedded_hilbert_generator,
                        fs_zfc_axiom_generate,
                        godel_unpair_value_pair,
                        fs_zfc_separation_generate_certificate,
                        fs_zfc_separation_hilbertize_schema]⟩
              | @collection parameterCount schema =>
                  exact
                    ⟨godel_pair_value 1
                        (godel_pair_value 1
                          (fs_zfc_schema_certificate
                            parameterCount
                            (nat_sequence_code_value
                              (fs_project_hilbert_token_tree
                                schema.body).tokens))), by
                      simp [fs_zfc_support_generate,
                        fs_zfc_embedded_hilbert_generator,
                        fs_zfc_axiom_generate,
                        godel_unpair_value_pair,
                        fs_zfc_collection_generate_certificate,
                        fs_zfc_collection_hilbertize_schema]⟩
          | choice =>
              exact ⟨godel_pair_value 3 7, by
                simp [fs_zfc_support_generate,
                  fs_zfc_embedded_hilbert_generator,
                  fs_zfc_axiom_generate, fs_zfc_fixed_axioms,
                  godel_unpair_value_pair]⟩
  }

/--
支持理论生成器成功输出的公式必为 admissible。

这里仅使用生成器的 soundness 与支持理论本身是 raw 理论逐式 Hilbert 化这一
定义事实；枚举接口不附加其他闭性前提。
-/
theorem fs_zfc_support_generate_admissible
    {certificate : Nat}
    {formula : SetFormula}
    (hGenerate :
      fs_zfc_support_generate certificate =
        some formula) :
    Formula.Admissible formula := by
  have hTheory :
      fs_zfc_support_theory formula :=
    fs_zfc_support_generator.generate_sound hGenerate
  change
    Theory.hilbertize
      Nonlogical.BasicSetTheory.SetSort.set
      fs_zfc_support_raw_theory formula at hTheory
  rcases hTheory with ⟨source, hSource, rfl⟩
  exact Formula.Admissible.hilbertize
    (fs_zfc_support_raw_theory_sentence hSource).1

/-- 支持理论生成器的输出已经处于 Hilbert 核正规形。 -/
theorem fs_zfc_support_generate_hilbertize_eq_self
    {certificate : Nat}
    {formula : SetFormula}
    (hGenerate :
      fs_zfc_support_generate certificate =
        some formula) :
    Formula.hilbertize
        Nonlogical.BasicSetTheory.SetSort.set formula =
      formula := by
  have hTheory :
      fs_zfc_support_theory formula :=
    fs_zfc_support_generator.generate_sound hGenerate
  change
    Theory.hilbertize
      Nonlogical.BasicSetTheory.SetSort.set
      fs_zfc_support_raw_theory formula at hTheory
  rcases hTheory with ⟨source, hSource, rfl⟩
  exact Formula.hilbertize_idempotent
    Nonlogical.BasicSetTheory.SetSort.set source

/--
完整 ZFC 内部 Hilbert 理论的实际递归枚举实例。

固定证书验证只比较可计算公式码；公式码单射保证比较成功时候选公式与目标公式
相同。
-/
def fs_zfc_support_enumeration :
    HilbertTheoryEnumeration
      fs_zfc_support_theory :=
  HilbertTheoryGenerator.toEnumeration
    fs_zfc_support_generator
    GodelQuotation.SyntaxCoding.formula_encode
    GodelQuotation.SyntaxCoding.formula_encode_injective

end ProofCode
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
