import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SyntaxCanonical

/-! # 参数化支撑公理的 indexed 数据外壳

原格式逐项携带自由上下文、项和剩余证书，末尾为 singleton 的零叶子。
此层恢复实际类型化项，尚不装配参数所指定的公理闭句。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.SyntaxParameters
open Nonlogical.BasicSetTheory NatPacket
set_option autoImplicit false

def encodeTerms {free sorts : SetContext} : Arguments signature [] free sorts → Tree
  | .nil => leaf 0
  | .cons head tail => .node 0 [SyntaxEncode.term head, encodeTerms tail]

def terms (free : SetContext) : (sorts : SetContext) → Tree → Option (Arguments signature [] free sorts)
  | [] , .node 0 [] => some .nil
  | .set :: sorts, .node 0 [head, tail] => do
      return .cons (← SyntaxDecode.term [] free head) (← terms free sorts tail)
  | _, _ => none

theorem terms_roundtrip {free sorts : SetContext} (args : Arguments signature [] free sorts) :
    terms free sorts (encodeTerms args) = some args := by
  cases args with
  | nil => rfl
  | @cons sort sorts head tail =>
    cases sort
    rw [encodeTerms, terms.eq_def]
    simp [terms_roundtrip tail]

theorem terms_encode_of_decode (free sorts : SetContext) (input : Tree)
    (args : Arguments signature [] free sorts) (h : terms free sorts input = some args) :
    encodeTerms args = input := by
  fun_cases terms free sorts input
  case case1 => cases h; rfl
  case case2 sorts head tail =>
    obtain ⟨headTerm, hHead, hRest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨tailTerms, hTail, hResult⟩ := Option.bind_eq_some_iff.mp hRest
    cases hResult
    simp only [encodeTerms]
    rw [SyntaxDecode.term_encode_of_decode [] free head headTerm hHead,
      terms_encode_of_decode free sorts tail tailTerms hTail]
  case case3 =>
    unfold terms at h
    split at h <;> simp_all
termination_by sorts.length

structure Parameters (count : Nat) where
  free : SetContext
  args : Arguments signature [] free (List.replicate count SetSort.set)

def encode {count : Nat} (parameters : Parameters count) : Tree :=
  .node 0 [SyntaxEncode.context parameters.free, encodeTerms parameters.args]

def decode (count : Nat) : Tree → Option (Parameters count)
  | .node 0 [contextTree, termsTree] => do
      let free ← SyntaxDecode.context contextTree
      let args ← terms free (List.replicate count SetSort.set) termsTree
      return ⟨free, args⟩
  | _ => none

@[simp] theorem decode_encode {count : Nat} (parameters : Parameters count) :
    decode count (encode parameters) = some parameters := by
  simp [decode, encode, SyntaxEncode.context_roundtrip, terms_roundtrip]

theorem encode_of_decode {count : Nat} {input : Tree} {parameters : Parameters count}
    (h : decode count input = some parameters) : encode parameters = input := by
  fun_cases decode count input
  case case1 contextTree termsTree =>
    obtain ⟨free, hFree, hRest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨args, hArgs, hResult⟩ := Option.bind_eq_some_iff.mp hRest
    cases hResult
    simp only [encode]
    rw [SyntaxDecode.context_encode_of_decode hFree, terms_encode_of_decode free _ termsTree args hArgs]
  case case2 =>
    unfold decode at h
    split at h <;> simp_all

theorem decode_eq_some_iff (count : Nat) (input : Tree) (parameters : Parameters count) :
    decode count input = some parameters ↔ encode parameters = input :=
  ⟨encode_of_decode, fun h => h ▸ decode_encode parameters⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.SyntaxParameters
