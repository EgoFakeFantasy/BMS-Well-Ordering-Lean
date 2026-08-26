import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCObjectCertificateSchemaRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalFirstOrderFailureAdapter
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCSchemaCompositeConstructorDisjointness

/-!
# Project decoder 的宿主构造闭包

这些可计算引理只说明：Project decoder 成功解出子式时，相应复合公式也能被
Project decoder 解出。证明通过成功解码后的规范重编码完成，不承担对象层反演职责。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open _root_.YesMetaZFC.SetTheory
open _root_.YesMetaZFC.SetTheory.Definitional
open _root_.YesMetaZFC.SetTheory.Definitional.Project
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open ProofCode
open GodelQuotation

set_option autoImplicit false

private theorem fs_project_hilbert_tokens_decode_tokens_eq
    {depth : Nat} {tokens : List Nat}
    {body : Project.Formula 1 depth}
    (hDecode :
      fs_project_hilbert_tokens_decode depth tokens =
        some body) :
    tokens =
      (fs_project_hilbert_token_tree body).tokens := by
  unfold fs_project_hilbert_tokens_decode at hDecode
  cases hParse :
      GodelQuotation.RawHilbertTokenTree.parse? tokens with
  | none =>
      simp [hParse] at hDecode
  | some tree =>
      have hTreeDecode :
          fs_project_hilbert_token_tree_decode depth tree =
            some body := by
        simpa [hParse] using hDecode
      exact
        (GodelQuotation.RawHilbertTokenTree.parse?_sound hParse).symm.trans
          (fs_project_hilbert_token_tree_tokens_of_decode
            hTreeDecode)

private theorem fs_project_hilbert_tokens_decode_hilbertize_eq
    {depth : Nat} {tokens : List Nat}
    {body : Project.Formula 1 depth}
    (hDecode :
      fs_project_hilbert_tokens_decode depth tokens =
        some body) :
    fs_project_hilbertize body = body := by
  have hClosed :
      body.FreeClosed :=
    fs_project_hilbert_tokens_decode_freeClosed hDecode
  have hTokens :=
    fs_project_hilbert_tokens_decode_tokens_eq hDecode
  have hRecode :=
    fs_project_hilbert_tokens_decode_encode body hClosed
  rw [← hTokens, hDecode] at hRecode
  exact (Option.some.inj hRecode).symm

theorem fs_project_hilbert_tokens_decode_negation
    (depth : Nat) (bodyTokens : List Nat)
    {body : Project.Formula 1 depth}
    (hProject :
      fs_project_hilbert_tokens_decode depth bodyTokens =
        some body) :
    fs_project_hilbert_tokens_decode depth
        (Numbered.negation_tokens bodyTokens) =
      some (.neg body) := by
  have hTokens :=
    fs_project_hilbert_tokens_decode_tokens_eq hProject
  have hClosed :
      body.FreeClosed :=
    fs_project_hilbert_tokens_decode_freeClosed hProject
  have hFixed :
      fs_project_hilbertize body = body :=
    fs_project_hilbert_tokens_decode_hilbertize_eq hProject
  rw [hTokens]
  simpa [fs_project_hilbert_token_tree,
      fs_project_hilbertize, hFixed] using
    fs_project_hilbert_tokens_decode_encode
      (.neg body) (by
        simpa [Definitional.Formula.FreeClosed] using hClosed)

theorem fs_project_hilbert_tokens_decode_implication
    (depth : Nat) (leftTokens rightTokens : List Nat)
    {left right : Project.Formula 1 depth}
    (hLeftProject :
      fs_project_hilbert_tokens_decode depth leftTokens =
        some left)
    (hRightProject :
      fs_project_hilbert_tokens_decode depth rightTokens =
        some right) :
    fs_project_hilbert_tokens_decode depth
        (Numbered.implication_tokens
          leftTokens rightTokens) =
      some (.imp left right) := by
  have hLeftTokens :=
    fs_project_hilbert_tokens_decode_tokens_eq hLeftProject
  have hRightTokens :=
    fs_project_hilbert_tokens_decode_tokens_eq hRightProject
  have hLeftClosed :
      left.FreeClosed :=
    fs_project_hilbert_tokens_decode_freeClosed hLeftProject
  have hRightClosed :
      right.FreeClosed :=
    fs_project_hilbert_tokens_decode_freeClosed hRightProject
  have hLeftFixed :
      fs_project_hilbertize left = left :=
    fs_project_hilbert_tokens_decode_hilbertize_eq hLeftProject
  have hRightFixed :
      fs_project_hilbertize right = right :=
    fs_project_hilbert_tokens_decode_hilbertize_eq hRightProject
  rw [hLeftTokens, hRightTokens]
  simpa [fs_project_hilbert_token_tree,
      fs_project_hilbertize, hLeftFixed, hRightFixed] using
    fs_project_hilbert_tokens_decode_encode
      (.imp left right) (by
        simpa [Definitional.Formula.FreeClosed] using
          And.intro hLeftClosed hRightClosed)

theorem fs_project_hilbert_tokens_decode_universal
    (depth name : Nat) (bodyTokens : List Nat)
    {body : Project.Formula 1 (depth + 1)}
    (hName : name = GodelQuotation.bound_name depth)
    (hProject :
      fs_project_hilbert_tokens_decode
          (depth + 1) bodyTokens =
        some body) :
    fs_project_hilbert_tokens_decode depth
        (Numbered.universal_tokens name bodyTokens) =
      some (.forallE body) := by
  have hTokens :=
    fs_project_hilbert_tokens_decode_tokens_eq hProject
  have hClosed :
      body.FreeClosed :=
    fs_project_hilbert_tokens_decode_freeClosed hProject
  have hFixed :
      fs_project_hilbertize body = body :=
    fs_project_hilbert_tokens_decode_hilbertize_eq hProject
  rw [hName, hTokens]
  simpa [fs_project_hilbert_token_tree,
      fs_project_hilbertize, hFixed] using
    fs_project_hilbert_tokens_decode_encode
      (.forallE body) (by
        simpa [Definitional.Formula.FreeClosed] using hClosed)

theorem fs_project_hilbert_tokens_decode_canonical_atom_some
    (depth : Nat)
    (kind : CanonicalProjectAtomKind)
    (leftDepth rightDepth : Nat)
    (hLeftDepth : leftDepth < depth)
    (hRightDepth : rightDepth < depth) :
    ∃ formula : Project.Formula 1 depth,
      fs_project_hilbert_tokens_decode depth
          (CanonicalProjectTrace.canonical_project_atom_tokens
            kind leftDepth rightDepth) =
        some formula := by
  let leftEntry : Fin depth :=
    ⟨depth - leftDepth - 1, by omega⟩
  let rightEntry : Fin depth :=
    ⟨depth - rightDepth - 1, by omega⟩
  have hLeftToken :
      fs_project_bound_token leftEntry =
        Numbered.variable_token
          (GodelQuotation.bound_name leftDepth) := by
    rw [fs_project_bound_token_eq]
    congr 2
    dsimp [leftEntry]
    omega
  have hRightToken :
      fs_project_bound_token rightEntry =
        Numbered.variable_token
          (GodelQuotation.bound_name rightDepth) := by
    rw [fs_project_bound_token_eq]
    congr 2
    dsimp [rightEntry]
    omega
  cases kind with
  | equality =>
      let formula : Project.Formula 1 depth :=
        Project.Formula.extensionalEq
          (.bound leftEntry) (.bound rightEntry)
      refine ⟨formula, ?_⟩
      simpa [formula,
        CanonicalProjectTrace.canonical_project_atom_tokens,
        fs_project_hilbert_token_tree,
        fs_project_term_token_tree,
        fs_project_hilbertize,
        RawHilbertTokenTree.tokens,
        Numbered.equality_tokens,
        Project.Formula.extensionalEq,
        hLeftToken, hRightToken, List.append_assoc] using
        fs_project_hilbert_tokens_decode_encode formula (by
          simp [formula, Project.Formula.extensionalEq,
            Definitional.Formula.FreeClosed])
  | membership =>
      let formula : Project.Formula 1 depth :=
        .mem (.bound leftEntry) (.bound rightEntry)
      refine ⟨formula, ?_⟩
      simpa [formula,
        CanonicalProjectTrace.canonical_project_atom_tokens,
        fs_project_hilbert_token_tree,
        fs_project_term_token_tree,
        fs_project_hilbertize,
        RawHilbertTokenTree.tokens,
        Numbered.membership_tokens,
        hLeftToken, hRightToken, List.append_assoc] using
        fs_project_hilbert_tokens_decode_encode formula (by
          simp [formula, Definitional.Formula.FreeClosed])
  | subset =>
      let formula : Project.Formula 1 depth :=
        Project.Formula.subset
          (.bound leftEntry) (.bound rightEntry)
      refine ⟨formula, ?_⟩
      simpa [formula,
        CanonicalProjectTrace.canonical_project_atom_tokens,
        fs_project_hilbert_token_tree,
        fs_project_term_token_tree,
        fs_project_hilbertize,
        RawHilbertTokenTree.tokens,
        Numbered.predicate_application_tokens,
        Project.Formula.subset,
        hLeftToken, hRightToken, List.append_assoc] using
        fs_project_hilbert_tokens_decode_encode formula (by
          simp [formula, Project.Formula.subset,
            Definitional.Formula.FreeClosed])

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
