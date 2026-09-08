import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.LogicalAxiomEncode
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SyntaxCanonical

/-! # 实际逻辑公理解码器的编码规范性 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.LogicalAxiomEncode
open Nonlogical.BasicSetTheory NatPacket
set_option autoImplicit false

theorem encode_of_decode (free : SetContext) (input : Tree) (result : LogicalAxiomDecode.Result free)
    (h : LogicalAxiomDecode.decode free input = some result) : encode result.2 = input := by
  unfold LogicalAxiomDecode.decode at h
  split at h
  · obtain ⟨a1, h1, hRest1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a2, h2, hRest2⟩ := Option.bind_eq_some_iff.mp hRest1
    obtain ⟨a3, h3, hRest3⟩ := Option.bind_eq_some_iff.mp hRest2
    cases hRest3
    simp only [LogicalAxiomDecode.pack, encode]
    rw [SyntaxDecode.formula_encode_of_decode _ _ _ _ h1, SyntaxDecode.formula_encode_of_decode _ _ _ _ h2, SyntaxDecode.formula_encode_of_decode _ _ _ _ h3]
  · obtain ⟨a1, h1, hRest1⟩ := Option.bind_eq_some_iff.mp h
    cases hRest1
    simp only [LogicalAxiomDecode.pack, encode]
    rw [SyntaxDecode.formula_encode_of_decode _ _ _ _ h1]
  · obtain ⟨a1, h1, hRest1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a2, h2, hRest2⟩ := Option.bind_eq_some_iff.mp hRest1
    cases hRest2
    simp only [LogicalAxiomDecode.pack, encode]
    rw [SyntaxDecode.formula_encode_of_decode _ _ _ _ h1, SyntaxDecode.formula_encode_of_decode _ _ _ _ h2]
  · obtain ⟨a1, h1, hRest1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a2, h2, hRest2⟩ := Option.bind_eq_some_iff.mp hRest1
    cases hRest2
    simp only [LogicalAxiomDecode.pack, encode]
    rw [SyntaxDecode.formula_encode_of_decode _ _ _ _ h1, SyntaxDecode.formula_encode_of_decode _ _ _ _ h2]
  · obtain ⟨a1, h1, hRest1⟩ := Option.bind_eq_some_iff.mp h
    cases hRest1
    simp only [LogicalAxiomDecode.pack, encode]
    rw [SyntaxDecode.formula_encode_of_decode _ _ _ _ h1]
  · obtain ⟨a1, h1, hRest1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a2, h2, hRest2⟩ := Option.bind_eq_some_iff.mp hRest1
    cases hRest2
    simp only [LogicalAxiomDecode.pack, encode]
    rw [SyntaxDecode.formula_encode_of_decode _ _ _ _ h1, SyntaxDecode.formula_encode_of_decode _ _ _ _ h2]
  · obtain ⟨a1, h1, hRest1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a2, h2, hRest2⟩ := Option.bind_eq_some_iff.mp hRest1
    cases hRest2
    simp only [LogicalAxiomDecode.pack, encode]
    rw [SyntaxDecode.formula_encode_of_decode _ _ _ _ h1, SyntaxDecode.formula_encode_of_decode _ _ _ _ h2]
  · cases h
    simp only [LogicalAxiomDecode.pack, encode]
  · obtain ⟨a1, h1, hRest1⟩ := Option.bind_eq_some_iff.mp h
    cases hRest1
    simp only [LogicalAxiomDecode.pack, encode]
    rw [SyntaxDecode.formula_encode_of_decode _ _ _ _ h1]
  · obtain ⟨a1, h1, hRest1⟩ := Option.bind_eq_some_iff.mp h
    cases hRest1
    simp only [LogicalAxiomDecode.pack, encode]
    rw [SyntaxDecode.formula_encode_of_decode _ _ _ _ h1]
  · obtain ⟨a1, h1, hRest1⟩ := Option.bind_eq_some_iff.mp h
    cases hRest1
    simp only [LogicalAxiomDecode.pack, encode]
    rw [SyntaxDecode.formula_encode_of_decode _ _ _ _ h1]
  · obtain ⟨a1, h1, hRest1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a2, h2, hRest2⟩ := Option.bind_eq_some_iff.mp hRest1
    cases hRest2
    simp only [LogicalAxiomDecode.pack, encode]
    rw [SyntaxDecode.formula_encode_of_decode _ _ _ _ h1, SyntaxDecode.formula_encode_of_decode _ _ _ _ h2]
  · obtain ⟨a1, h1, hRest1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a2, h2, hRest2⟩ := Option.bind_eq_some_iff.mp hRest1
    cases hRest2
    simp only [LogicalAxiomDecode.pack, encode]
    rw [SyntaxDecode.formula_encode_of_decode _ _ _ _ h1, SyntaxDecode.formula_encode_of_decode _ _ _ _ h2]
  · obtain ⟨a1, h1, hRest1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a2, h2, hRest2⟩ := Option.bind_eq_some_iff.mp hRest1
    cases hRest2
    simp only [LogicalAxiomDecode.pack, encode]
    rw [SyntaxDecode.formula_encode_of_decode _ _ _ _ h1, SyntaxDecode.formula_encode_of_decode _ _ _ _ h2]
  · obtain ⟨a1, h1, hRest1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a2, h2, hRest2⟩ := Option.bind_eq_some_iff.mp hRest1
    cases hRest2
    simp only [LogicalAxiomDecode.pack, encode]
    rw [SyntaxDecode.formula_encode_of_decode _ _ _ _ h1, SyntaxDecode.formula_encode_of_decode _ _ _ _ h2]
  · obtain ⟨a1, h1, hRest1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a2, h2, hRest2⟩ := Option.bind_eq_some_iff.mp hRest1
    cases hRest2
    simp only [LogicalAxiomDecode.pack, encode]
    rw [SyntaxDecode.formula_encode_of_decode _ _ _ _ h1, SyntaxDecode.formula_encode_of_decode _ _ _ _ h2]
  · obtain ⟨a1, h1, hRest1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a2, h2, hRest2⟩ := Option.bind_eq_some_iff.mp hRest1
    obtain ⟨a3, h3, hRest3⟩ := Option.bind_eq_some_iff.mp hRest2
    cases hRest3
    simp only [LogicalAxiomDecode.pack, encode]
    rw [SyntaxDecode.formula_encode_of_decode _ _ _ _ h1, SyntaxDecode.formula_encode_of_decode _ _ _ _ h2, SyntaxDecode.formula_encode_of_decode _ _ _ _ h3]
  · obtain ⟨a1, h1, hRest1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a2, h2, hRest2⟩ := Option.bind_eq_some_iff.mp hRest1
    cases hRest2
    simp only [LogicalAxiomDecode.pack, encode]
    rw [SyntaxDecode.formula_encode_of_decode _ _ _ _ h1, SyntaxDecode.formula_encode_of_decode _ _ _ _ h2]
  · obtain ⟨a1, h1, hRest1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a2, h2, hRest2⟩ := Option.bind_eq_some_iff.mp hRest1
    cases hRest2
    simp only [LogicalAxiomDecode.pack, encode]
    rw [SyntaxDecode.formula_encode_of_decode _ _ _ _ h1, SyntaxDecode.formula_encode_of_decode _ _ _ _ h2]
  · obtain ⟨a1, h1, hRest1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a2, h2, hRest2⟩ := Option.bind_eq_some_iff.mp hRest1
    cases hRest2
    simp only [LogicalAxiomDecode.pack, encode]
    rw [SyntaxDecode.formula_encode_of_decode _ _ _ _ h1, SyntaxDecode.formula_encode_of_decode _ _ _ _ h2]
  · obtain ⟨a1, h1, hRest1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a2, h2, hRest2⟩ := Option.bind_eq_some_iff.mp hRest1
    cases hRest2
    simp only [LogicalAxiomDecode.pack, encode]
    rw [SyntaxDecode.formula_encode_of_decode _ _ _ _ h1, SyntaxDecode.term_encode_of_decode _ _ _ _ h2]
  · obtain ⟨a1, h1, hRest1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a2, h2, hRest2⟩ := Option.bind_eq_some_iff.mp hRest1
    cases hRest2
    simp only [LogicalAxiomDecode.pack, encode]
    rw [SyntaxDecode.formula_encode_of_decode _ _ _ _ h1, SyntaxDecode.formula_encode_of_decode _ _ _ _ h2]
  · obtain ⟨a1, h1, hRest1⟩ := Option.bind_eq_some_iff.mp h
    cases hRest1
    simp only [LogicalAxiomDecode.pack, encode]
    rw [SyntaxDecode.formula_encode_of_decode _ _ _ _ h1]
  · obtain ⟨a1, h1, hRest1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a2, h2, hRest2⟩ := Option.bind_eq_some_iff.mp hRest1
    cases hRest2
    simp only [LogicalAxiomDecode.pack, encode]
    rw [SyntaxDecode.formula_encode_of_decode _ _ _ _ h1, SyntaxDecode.term_encode_of_decode _ _ _ _ h2]
  · obtain ⟨a1, h1, hRest1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a2, h2, hRest2⟩ := Option.bind_eq_some_iff.mp hRest1
    cases hRest2
    simp only [LogicalAxiomDecode.pack, encode]
    rw [SyntaxDecode.formula_encode_of_decode _ _ _ _ h1, SyntaxDecode.formula_encode_of_decode _ _ _ _ h2]
  · obtain ⟨a1, h1, hRest1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a2, h2, hRest2⟩ := Option.bind_eq_some_iff.mp hRest1
    obtain ⟨a3, h3, hRest3⟩ := Option.bind_eq_some_iff.mp hRest2
    cases hRest3
    simp only [LogicalAxiomDecode.pack, encode]
    rw [SyntaxDecode.term_encode_of_decode _ _ _ _ h1, SyntaxDecode.term_encode_of_decode _ _ _ _ h2, SyntaxDecode.formula_encode_of_decode _ _ _ _ h3]
  · obtain ⟨a1, h1, hRest1⟩ := Option.bind_eq_some_iff.mp h
    cases hRest1
    simp only [LogicalAxiomDecode.pack, encode]
    rw [SyntaxDecode.term_encode_of_decode _ _ _ _ h1]
  · cases h

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.LogicalAxiomEncode
