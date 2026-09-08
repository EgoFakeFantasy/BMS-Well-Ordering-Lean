import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaRename

/-!
# 三类公理模式的实际重命名表

六个正文位置共用有限表递归器，参数数目任意。这里证明它们与现有模式构造的
类型化映射相同；替换模式仍是单独的模式接口，不向 ZFC 公理证书增加构造子。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaRename
open Nonlogical.BasicSetTheory NatPacket
open _root_.YesMetaZFC.SetTheory
open _root_.YesMetaZFC.SetTheory.Definitional
set_option autoImplicit false

inductive Site where
  | separation
  | collectionPremise
  | collectionImage
  | replacementFirst
  | replacementSecond
  | replacementImage
  deriving DecidableEq, Repr

namespace Site
def sourceDepth (site : Site) (parameterCount : Nat) : Nat :=
  match site with
  | .separation => parameterCount + 1
  | _ => parameterCount + 2

def targetDepth (site : Site) (parameterCount : Nat) : Nat :=
  match site with
  | .collectionImage | .replacementImage => parameterCount + 4
  | _ => parameterCount + 3

/-- 主变量的短前缀与按位置平移的参数尾表，均为可计算的原始自然数数据。 -/
def table (site : Site) (parameterCount : Nat) : List Nat :=
  match site with
  | .separation => 0 :: List.ofFn (fun i : Fin parameterCount => i.val + 3)
  | .collectionPremise => 0 :: 1 :: List.ofFn (fun i : Fin parameterCount => i.val + 3)
  | .collectionImage => 0 :: 1 :: List.ofFn (fun i : Fin parameterCount => i.val + 4)
  | .replacementFirst => 1 :: 2 :: List.ofFn (fun i : Fin parameterCount => i.val + 3)
  | .replacementSecond => 0 :: 2 :: List.ofFn (fun i : Fin parameterCount => i.val + 3)
  | .replacementImage => 1 :: 0 :: List.ofFn (fun i : Fin parameterCount => i.val + 4)

def mapping (site : Site) (parameterCount : Nat) :
    Fin (site.sourceDepth parameterCount) → Fin (site.targetDepth parameterCount) :=
  match site with
  | .separation => BoundEmbedding.unaryUnderTwo
  | .collectionPremise => BoundEmbedding.binaryUnderOne
  | .collectionImage => BoundEmbedding.binaryUnderTwo
  | .replacementFirst => Axioms.Schema.ReplacementEmbedding.firstOutput
  | .replacementSecond => Axioms.Schema.ReplacementEmbedding.secondOutput
  | .replacementImage => Axioms.Schema.ReplacementEmbedding.imageBody

theorem table_eq_encodeMap (site : Site) (parameterCount : Nat) :
    site.table parameterCount = encodeMap (site.mapping parameterCount) := by
  cases site <;> simp [table, mapping, sourceDepth, encodeMap, List.ofFn_succ,
    BoundEmbedding.unaryUnderTwo, BoundEmbedding.binaryUnderOne, BoundEmbedding.binaryUnderTwo,
    Axioms.Schema.ReplacementEmbedding.firstOutput, Axioms.Schema.ReplacementEmbedding.secondOutput,
    Axioms.Schema.ReplacementEmbedding.imageBody]

@[simp] theorem table_length (site : Site) (parameterCount : Nat) :
    (site.table parameterCount).length = site.sourceDepth parameterCount := by
  rw [table_eq_encodeMap, encodeMap_length]

@[simp] theorem table_valid (site : Site) (parameterCount : Nat) :
    valid (site.targetDepth parameterCount) (site.table parameterCount) = true := by
  rw [table_eq_encodeMap, valid_encodeMap]

/-- 六个位置的原始输入识别都使用实际源作用域，没有额外的有限护栏。 -/
theorem run_isSome (site : Site) (parameterCount : Nat) (input : Tree) :
    (run (site.targetDepth parameterCount) (site.table parameterCount) input).isSome =
      SchemaBody.check (site.sourceDepth parameterCount) input := by
  rw [SchemaRename.run_isSome, table_valid, Bool.true_and]
  exact congrArg (fun depth => SchemaBody.check depth input) (table_length site parameterCount)

theorem run_encode (site : Site) (parameterCount : Nat)
    (body : Project.Formula 1 (site.sourceDepth parameterCount)) (hClosed : body.FreeClosed) :
    run (site.targetDepth parameterCount) (site.table parameterCount) (ProjectEncode.formula body) =
      some (ProjectEncode.formula (body.rename (site.mapping parameterCount))) := by
  rw [table_eq_encodeMap]
  exact run_encode_rename _ body hClosed

end Site
end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaRename
