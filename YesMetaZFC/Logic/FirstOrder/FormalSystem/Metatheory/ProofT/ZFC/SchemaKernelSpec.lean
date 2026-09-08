import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaKernelJoin

/-! # 三种模式连接与实际类型化 schema 解码器逐项相等 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaKernelJoin
open Nonlogical.BasicSetTheory QuineEncoding NatPacket IntrinsicQuotation
open _root_.YesMetaZFC.Automation
open _root_.YesMetaZFC.SetTheory
open _root_.YesMetaZFC.SetTheory.Definitional
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

theorem run_separation {n : Nat} (schema : Project.UnarySchema n) :
    run .separation n (ProjectEncode.formula schema.body) =
      some (SyntaxEncode.formula (project_sentence (Axioms.Schema.separation schema))) := by
  rw [run, SchemaClosure.run_separation, Option.bind_some]
  exact KernelQuotation.project_formula_code _ _

theorem run_collection {n : Nat} (schema : Project.BinarySchema n) :
    run .collection n (ProjectEncode.formula schema.body) =
      some (SyntaxEncode.formula (project_sentence (Axioms.Schema.collection schema))) := by
  rw [run, SchemaClosure.run_collection, Option.bind_some]
  exact KernelQuotation.project_formula_code _ _

theorem run_replacement {n : Nat} (schema : Project.BinarySchema n) :
    run .replacement n (ProjectEncode.formula schema.body) =
      some (SyntaxEncode.formula (project_sentence (Axioms.Schema.replacement schema))) := by
  rw [run, SchemaClosure.run_replacement, Option.bind_some]
  exact KernelQuotation.project_formula_code _ _

/-- 任意原始正文，包括全部解码失败分支，都与实际一元 schema 解码器相等。 -/
theorem separation_decode (n : Nat) (input : Tree) :
    run .separation n input = (ProjectDecode.unarySchema n input).map
      (fun schema => SyntaxEncode.formula (project_sentence (Axioms.Schema.separation schema))) := by
  cases h : ProjectDecode.formula (n + 1) input with
  | none =>
    have hNone : SchemaClosure.run .separation n input = none := by
      apply Option.isNone_iff_eq_none.mp
      apply Option.isSome_eq_false_iff.mp
      rw [SchemaClosure.run_isSome]
      simp [SchemaBody.check, SchemaTemplate.Kind.sourceDepth, h]
    simp [run, hNone, ProjectDecode.unarySchema, h]
  | some body =>
    have hSpec := SchemaBody.decode_spec _ _ _ h
    let schema : Project.UnarySchema n := ⟨body, hSpec.1⟩
    have hInput : input = ProjectEncode.formula schema.body := hSpec.2.symm
    rw [hInput, ProjectEncode.unary_roundtrip, Option.map_some]
    exact run_separation schema

theorem collection_decode (n : Nat) (input : Tree) :
    run .collection n input = (ProjectDecode.binarySchema n input).map
      (fun schema => SyntaxEncode.formula (project_sentence (Axioms.Schema.collection schema))) := by
  cases h : ProjectDecode.formula (n + 2) input with
  | none =>
    have hNone : SchemaClosure.run .collection n input = none := by
      apply Option.isNone_iff_eq_none.mp
      apply Option.isSome_eq_false_iff.mp
      rw [SchemaClosure.run_isSome]
      simp [SchemaBody.check, SchemaTemplate.Kind.sourceDepth, h]
    simp [run, hNone, ProjectDecode.binarySchema, h]
  | some body =>
    have hSpec := SchemaBody.decode_spec _ _ _ h
    let schema : Project.BinarySchema n := ⟨body, hSpec.1⟩
    have hInput : input = ProjectEncode.formula schema.body := hSpec.2.symm
    rw [hInput, ProjectEncode.binary_roundtrip, Option.map_some]
    exact run_collection schema

theorem replacement_decode (n : Nat) (input : Tree) :
    run .replacement n input = (ProjectDecode.binarySchema n input).map
      (fun schema => SyntaxEncode.formula (project_sentence (Axioms.Schema.replacement schema))) := by
  cases h : ProjectDecode.formula (n + 2) input with
  | none =>
    have hNone : SchemaClosure.run .replacement n input = none := by
      apply Option.isNone_iff_eq_none.mp
      apply Option.isSome_eq_false_iff.mp
      rw [SchemaClosure.run_isSome]
      simp [SchemaBody.check, SchemaTemplate.Kind.sourceDepth, h]
    simp [run, hNone, ProjectDecode.binarySchema, h]
  | some body =>
    have hSpec := SchemaBody.decode_spec _ _ _ h
    let schema : Project.BinarySchema n := ⟨body, hSpec.1⟩
    have hInput : input = ProjectEncode.formula schema.body := hSpec.2.symm
    rw [hInput, ProjectEncode.binary_roundtrip, Option.map_some]
    exact run_replacement schema

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaKernelJoin
