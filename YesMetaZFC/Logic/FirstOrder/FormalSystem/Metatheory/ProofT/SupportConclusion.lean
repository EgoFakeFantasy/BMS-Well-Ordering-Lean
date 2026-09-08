import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SupportAssembly

/-! # 参数装配与原公理证书结论的精确连接 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.SupportConclusion
open Nonlogical.BasicSetTheory NatPacket SupportParameters SupportAssembly
set_option autoImplicit false

private theorem union_left_sentence {T U : SetTheory}
    {left : AxiomPresentation T} {right : AxiomPresentation U}
    (dl : AxiomDecoder left) (dr : AxiomDecoder right) (input : Tree) :
    (AxiomDecoder.union dl dr (.node 0 [input])).map (AxiomPresentation.union left right).sentence =
      (dl input).map left.sentence := by
  change ((dl input).map Sum.inl).map (Sum.elim left.sentence right.sentence) = _
  simp only [Option.map_map, Function.comp_def, Sum.elim_inl]

private theorem indexed_sentence {Index : Type} {family : Index → SetTheory}
    {ps : ∀ i, AxiomPresentation (family i)} (di : Tree → Option Index)
    (ds : ∀ i, AxiomDecoder (ps i)) (index input : Tree) :
    (AxiomDecoder.indexed di ds (.node 0 [index, input])).map (AxiomPresentation.indexed ps).sentence =
      (di index).bind (fun i => (ds i input).map (ps i).sentence) := by
  change ((di index).bind (fun i => (ds i input).bind
    (fun c => some (⟨i, c⟩ : (i : Index) × (ps i).Certificate)))).map
    (fun c => (ps c.1).sentence c.2) = _
  cases h : di index with
  | none => rfl
  | some i =>
    simp only [Option.bind_some]
    cases ds i input <;> rfl

private theorem singleton_sentence (φ : SetSentence) :
    (AxiomDecoder.singleton φ (leaf 0)).map (AxiomPresentation.singleton φ).sentence = some φ := rfl

attribute [local implicit_reducible] Theory.singleton Theory.union Kind.arity
attribute [local implicit_reducible]
  IntrinsicAxiomCertificate.presentation_relation_domain
  IntrinsicAxiomCertificate.presentation_relation_range
  IntrinsicAxiomCertificate.presentation_cartesian_product
  IntrinsicAxiomCertificate.presentation_relation_converse
  IntrinsicAxiomCertificate.presentation_relation_composition
  IntrinsicAxiomCertificate.presentation_identity
  IntrinsicAxiomCertificate.presentation_mapping_collection
  IntrinsicAxiomCertificate.presentation_index_order_separation
  IntrinsicAxiomCertificate.presentation_power_set_bijection_separation
  IntrinsicAxiomCertificate.presentation_symmetric_difference_separation
  IntrinsicAxiomCertificate.presentation_inductive_core_separation

/-- 原解码器实际产出的闭句，不经过新的参数装配函数。 -/
def actual (kind : Kind) (input : Tree) : Option SetSentence :=
  let branch := Tree.node 0 [input]
  match kind with
  | .domain => (IntrinsicAxiomDecode.decode_relation_domain branch).map
      IntrinsicAxiomCertificate.presentation_relation_domain.sentence
  | .range => (IntrinsicAxiomDecode.decode_relation_range branch).map
      IntrinsicAxiomCertificate.presentation_relation_range.sentence
  | .cartesianProduct => (IntrinsicAxiomDecode.decode_cartesian_product branch).map
      IntrinsicAxiomCertificate.presentation_cartesian_product.sentence
  | .converse => (IntrinsicAxiomDecode.decode_relation_converse branch).map
      IntrinsicAxiomCertificate.presentation_relation_converse.sentence
  | .composition => (IntrinsicAxiomDecode.decode_relation_composition branch).map
      IntrinsicAxiomCertificate.presentation_relation_composition.sentence
  | .identity => (IntrinsicAxiomDecode.decode_identity branch).map
      IntrinsicAxiomCertificate.presentation_identity.sentence
  | .mappingCollection => (IntrinsicAxiomDecode.decode_mapping_collection branch).map
      IntrinsicAxiomCertificate.presentation_mapping_collection.sentence
  | .indexOrder => (IntrinsicAxiomDecode.decode_index_order_separation branch).map
      IntrinsicAxiomCertificate.presentation_index_order_separation.sentence
  | .powerSetBijection => (IntrinsicAxiomDecode.decode_power_set_bijection_separation branch).map
      IntrinsicAxiomCertificate.presentation_power_set_bijection_separation.sentence
  | .symmetricDifference => (IntrinsicAxiomDecode.decode_symmetric_difference_separation branch).map
      IntrinsicAxiomCertificate.presentation_symmetric_difference_separation.sentence
  | .inductiveCore => (IntrinsicAxiomDecode.decode_inductive_core_separation branch).map
      IntrinsicAxiomCertificate.presentation_inductive_core_separation.sentence

theorem actual_isSome (kind : Kind) (input : Tree) :
    (actual kind input).isSome = SupportParameters.actual kind input := by
  cases kind <;> simp only [actual, SupportParameters.actual, Option.isSome_map]

/-- 每个类型正确的参数证书指定的恰是原理论中的同一公理闭句。 -/
theorem actual_encode (kind : Kind) (parameters : SyntaxParameters.Parameters kind.arity) :
    actual kind (SyntaxParameters.encode parameters) = some (sentence kind parameters) := by
  rcases parameters with ⟨free, args⟩
  cases kind
  case domain =>
    cases args with | cons relation tail0 =>
    cases tail0
    dsimp only [actual, SyntaxParameters.encode, SyntaxParameters.encodeTerms,
      IntrinsicAxiomDecode.decode_relation_domain, IntrinsicAxiomCertificate.presentation_relation_domain]
    rw [union_left_sentence]
    simp only [indexed_sentence, singleton_sentence,
      SyntaxEncode.context_roundtrip, SyntaxEncode.term_roundtrip, Option.bind_some]
    rfl
  case range =>
    cases args with | cons relation tail0 =>
    cases tail0
    dsimp only [actual, SyntaxParameters.encode, SyntaxParameters.encodeTerms,
      IntrinsicAxiomDecode.decode_relation_range, IntrinsicAxiomCertificate.presentation_relation_range]
    rw [union_left_sentence]
    simp only [indexed_sentence, singleton_sentence,
      SyntaxEncode.context_roundtrip, SyntaxEncode.term_roundtrip, Option.bind_some]
    rfl
  case cartesianProduct =>
    cases args with | cons left tail0 =>
    cases tail0 with | cons right tail1 =>
    cases tail1
    dsimp only [actual, SyntaxParameters.encode, SyntaxParameters.encodeTerms,
      IntrinsicAxiomDecode.decode_cartesian_product, IntrinsicAxiomCertificate.presentation_cartesian_product]
    rw [union_left_sentence]
    simp only [indexed_sentence, singleton_sentence,
      SyntaxEncode.context_roundtrip, SyntaxEncode.term_roundtrip, Option.bind_some]
    rfl
  case converse =>
    cases args with | cons relation tail0 =>
    cases tail0
    dsimp only [actual, SyntaxParameters.encode, SyntaxParameters.encodeTerms,
      IntrinsicAxiomDecode.decode_relation_converse, IntrinsicAxiomCertificate.presentation_relation_converse]
    rw [union_left_sentence]
    simp only [indexed_sentence, singleton_sentence,
      SyntaxEncode.context_roundtrip, SyntaxEncode.term_roundtrip, Option.bind_some]
    rfl
  case composition =>
    cases args with | cons first tail0 =>
    cases tail0 with | cons second tail1 =>
    cases tail1
    dsimp only [actual, SyntaxParameters.encode, SyntaxParameters.encodeTerms,
      IntrinsicAxiomDecode.decode_relation_composition, IntrinsicAxiomCertificate.presentation_relation_composition]
    rw [union_left_sentence]
    simp only [indexed_sentence, singleton_sentence,
      SyntaxEncode.context_roundtrip, SyntaxEncode.term_roundtrip, Option.bind_some]
    rfl
  case identity =>
    cases args with | cons source tail0 =>
    cases tail0
    dsimp only [actual, SyntaxParameters.encode, SyntaxParameters.encodeTerms,
      IntrinsicAxiomDecode.decode_identity, IntrinsicAxiomCertificate.presentation_identity]
    rw [union_left_sentence]
    simp only [indexed_sentence, singleton_sentence,
      SyntaxEncode.context_roundtrip, SyntaxEncode.term_roundtrip, Option.bind_some]
    rfl
  case mappingCollection =>
    cases args with | cons source tail0 =>
    cases tail0 with | cons target tail1 =>
    cases tail1
    dsimp only [actual, SyntaxParameters.encode, SyntaxParameters.encodeTerms,
      IntrinsicAxiomDecode.decode_mapping_collection, IntrinsicAxiomCertificate.presentation_mapping_collection]
    rw [union_left_sentence]
    simp only [indexed_sentence, singleton_sentence,
      SyntaxEncode.context_roundtrip, SyntaxEncode.term_roundtrip, Option.bind_some]
    rfl
  case indexOrder =>
    cases args with | cons sourceRelation tail0 =>
    cases tail0 with | cons sourceCarrier tail1 =>
    cases tail1 with | cons targetRelation tail2 =>
    cases tail2 with | cons targetCarrier tail3 =>
    cases tail3
    dsimp only [actual, SyntaxParameters.encode, SyntaxParameters.encodeTerms,
      IntrinsicAxiomDecode.decode_index_order_separation, IntrinsicAxiomCertificate.presentation_index_order_separation]
    rw [union_left_sentence]
    simp only [indexed_sentence, singleton_sentence,
      SyntaxEncode.context_roundtrip, SyntaxEncode.term_roundtrip, Option.bind_some]
    rfl
  case powerSetBijection =>
    cases args with | cons natural tail0 =>
    cases tail0
    dsimp only [actual, SyntaxParameters.encode, SyntaxParameters.encodeTerms,
      IntrinsicAxiomDecode.decode_power_set_bijection_separation, IntrinsicAxiomCertificate.presentation_power_set_bijection_separation]
    rw [union_left_sentence]
    simp only [indexed_sentence, singleton_sentence,
      SyntaxEncode.context_roundtrip, SyntaxEncode.term_roundtrip, Option.bind_some]
    rfl
  case symmetricDifference =>
    cases args with | cons left tail0 =>
    cases tail0 with | cons right tail1 =>
    cases tail1
    dsimp only [actual, SyntaxParameters.encode, SyntaxParameters.encodeTerms,
      IntrinsicAxiomDecode.decode_symmetric_difference_separation, IntrinsicAxiomCertificate.presentation_symmetric_difference_separation]
    rw [union_left_sentence]
    simp only [indexed_sentence, singleton_sentence,
      SyntaxEncode.context_roundtrip, SyntaxEncode.term_roundtrip, Option.bind_some]
    rfl
  case inductiveCore =>
    cases args with | cons source tail0 =>
    cases tail0
    dsimp only [actual, SyntaxParameters.encode, SyntaxParameters.encodeTerms,
      IntrinsicAxiomDecode.decode_inductive_core_separation, IntrinsicAxiomCertificate.presentation_inductive_core_separation]
    rw [union_left_sentence]
    simp only [indexed_sentence, singleton_sentence,
      SyntaxEncode.context_roundtrip, SyntaxEncode.term_roundtrip, Option.bind_some]
    rfl

/-- 所有原始输入上的结论一致性，失败由既有识别定理排除。 -/
theorem actual_eq_decode (kind : Kind) (input : Tree) :
    actual kind input = (SyntaxParameters.decode kind.arity input).map (sentence kind) := by
  cases h : SyntaxParameters.decode kind.arity input with
  | none =>
    have hSome : (actual kind input).isSome = false := by
      rw [actual_isSome, SupportParameters.actual_eq_decode, h]
      rfl
    exact Option.isNone_iff_eq_none.mp (Option.isSome_eq_false_iff.mp hSome)
  | some parameters =>
    rw [← SyntaxParameters.encode_of_decode h]
    exact actual_encode kind parameters

/-- 各族原有理论，保留其已经证明的公理呈现。 -/
def theory : Kind → SetTheory
  | .domain => relation_domain_theory
  | .range => relation_range_theory
  | .cartesianProduct => cartesian_product_theory
  | .converse => relation_converse_theory
  | .composition => relation_composition_theory
  | .identity => identity_theory
  | .mappingCollection => mapping_collection_theory
  | .indexOrder => index_order_separation_theory
  | .powerSetBijection => power_set_bijection_separation_theory
  | .symmetricDifference => symmetric_difference_separation_theory
  | .inductiveCore => inductive_core_separation_theory

/-- 实际解码成功的结论属于对应的原公理理论。 -/
theorem actual_sound (kind : Kind) (input : Tree) (φ : SetSentence)
    (h : actual kind input = some φ) : theory kind φ := by
  cases kind
  case domain =>
    obtain ⟨certificate, _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact IntrinsicAxiomCertificate.presentation_relation_domain.sound certificate
  case range =>
    obtain ⟨certificate, _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact IntrinsicAxiomCertificate.presentation_relation_range.sound certificate
  case cartesianProduct =>
    obtain ⟨certificate, _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact IntrinsicAxiomCertificate.presentation_cartesian_product.sound certificate
  case converse =>
    obtain ⟨certificate, _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact IntrinsicAxiomCertificate.presentation_relation_converse.sound certificate
  case composition =>
    obtain ⟨certificate, _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact IntrinsicAxiomCertificate.presentation_relation_composition.sound certificate
  case identity =>
    obtain ⟨certificate, _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact IntrinsicAxiomCertificate.presentation_identity.sound certificate
  case mappingCollection =>
    obtain ⟨certificate, _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact IntrinsicAxiomCertificate.presentation_mapping_collection.sound certificate
  case indexOrder =>
    obtain ⟨certificate, _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact IntrinsicAxiomCertificate.presentation_index_order_separation.sound certificate
  case powerSetBijection =>
    obtain ⟨certificate, _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact IntrinsicAxiomCertificate.presentation_power_set_bijection_separation.sound certificate
  case symmetricDifference =>
    obtain ⟨certificate, _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact IntrinsicAxiomCertificate.presentation_symmetric_difference_separation.sound certificate
  case inductiveCore =>
    obtain ⟨certificate, _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact IntrinsicAxiomCertificate.presentation_inductive_core_separation.sound certificate

theorem sentence_sound (kind : Kind) (parameters : SyntaxParameters.Parameters kind.arity) :
    theory kind (sentence kind parameters) :=
  actual_sound kind _ _ (actual_encode kind parameters)

/-- 装配所得闭句在原族理论中有普通 Hilbert 推导。 -/
theorem sentence_derives (kind : Kind) (parameters : SyntaxParameters.Parameters kind.arity) :
    Derives (theory kind) [] (sentence kind parameters) :=
  FirstOrder.Derives.theory_axiom (sentence_sound kind parameters)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.SupportConclusion
