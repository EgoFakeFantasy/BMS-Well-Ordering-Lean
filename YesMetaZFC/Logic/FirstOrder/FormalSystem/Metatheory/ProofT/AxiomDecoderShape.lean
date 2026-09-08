import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.AxiomDecode
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SyntaxParameters

/-! # indexed 公理证书的接受形状

忘掉返回值后，原依赖解码器与普通形状检查交换。用于核对参数公理族的
真实证书入口，不改变它们的呈现、证书类型或所指定的公理。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.AxiomDecoderShape
open Nonlogical.BasicSetTheory NatPacket
set_option autoImplicit false

def singleton : Tree → Bool
  | .node 0 [] => true
  | _ => false

def indexed {Index : Type} (decodeIndex : Tree → Option Index) (checks : Index → Tree → Bool) : Tree → Bool
  | .node 0 [indexTree, child] => (decodeIndex indexTree).any (fun index => checks index child)
  | _ => false

theorem union_left_correct {T U : SetTheory} {left : AxiomPresentation T} {right : AxiomPresentation U}
    (decodeLeft : AxiomDecoder left) (decodeRight : AxiomDecoder right) (input : Tree) :
    (AxiomDecoder.union decodeLeft decodeRight (.node 0 [input])).isSome = (decodeLeft input).isSome := by
  change ((decodeLeft input).map (@Sum.inl left.Certificate right.Certificate)).isSome = _
  exact Option.isSome_map

theorem singleton_correct (formula : SetSentence) (input : Tree) :
    (AxiomDecoder.singleton formula input).isSome = singleton input := by
  unfold AxiomDecoder.singleton singleton
  cases input with
  | node tag children => cases tag <;> cases children <;> rfl

theorem indexed_correct {Index : Type} {family : Index → SetTheory}
    {presentations : ∀ index, AxiomPresentation (family index)}
    (decodeIndex : Tree → Option Index) (decoders : ∀ index, AxiomDecoder (presentations index)) (input : Tree) :
    (AxiomDecoder.indexed decodeIndex decoders input).isSome =
      indexed decodeIndex (fun index child => (decoders index child).isSome) input := by
  unfold AxiomDecoder.indexed indexed
  cases input with
  | node tag children =>
    cases tag with
    | succ _ => rfl
    | zero =>
      cases children with
      | nil => rfl
      | cons first rest =>
        cases rest with
        | nil => rfl
        | cons second tail =>
          cases tail with
          | nil =>
            change ((decodeIndex first).bind (fun index => (decoders index second).bind
              (fun certificate => some (⟨index, certificate⟩ : (i : Index) × (presentations i).Certificate)))).isSome = _
            simp [Option.isSome_bind, Option.any_true]
          | cons _ _ => rfl

def terms (free : SetContext) : Nat → Tree → Bool
  | 0 => singleton
  | n + 1 => indexed (SyntaxDecode.term [] free) (fun _ => terms free n)

def parameters (count : Nat) : Tree → Bool := indexed SyntaxDecode.context (fun free => terms free count)

theorem terms_correct (free sorts : SetContext) (input : Tree) :
    (SyntaxParameters.terms free sorts input).isSome = terms free sorts.length input := by
  induction sorts generalizing input with
  | nil =>
    rw [SyntaxParameters.terms.eq_def]
    simp only [List.length_nil, terms, singleton]
    cases input with
    | node tag children => cases tag <;> cases children <;> rfl
  | cons sort sorts ih =>
    cases sort
    rw [SyntaxParameters.terms.eq_def]
    simp only [List.length_cons, terms, indexed]
    cases input with
    | node tag children =>
      cases tag with
      | succ _ => rfl
      | zero =>
        cases children with
        | nil => rfl
        | cons first rest =>
          cases rest with
          | nil => rfl
          | cons second tail =>
            cases tail with
            | nil => simp [Option.isSome_bind, Option.any_true, ih]
            | cons _ _ => rfl

theorem parameters_correct (count : Nat) (input : Tree) :
    (SyntaxParameters.decode count input).isSome = parameters count input := by
  unfold SyntaxParameters.decode parameters indexed
  split
  · simp [Option.isSome_bind, Option.any_true]
    congr 1
    funext free
    simpa only [List.length_replicate] using terms_correct free (List.replicate count SetSort.set) _
  · split <;> simp_all

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.AxiomDecoderShape
