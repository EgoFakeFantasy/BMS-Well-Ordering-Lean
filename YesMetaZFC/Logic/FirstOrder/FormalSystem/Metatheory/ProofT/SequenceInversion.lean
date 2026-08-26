import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CertifiedSequenceCodeEncoding
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.StandardTokenSequence

/-!
# `ProofT` 的有限序列编码反演核心

证明码规范化需要反演两层对象编码：自然数 token 序列，以及由 token 序列组成的
证明行序列。本接口只记录这两个可计算关系的规范唯一性，不要求宿主理论包含某个
固定的 ZFC 定义公理表。

实现者可以使用 PA 级有限递归、KPω 的有限序列设施，或当前 ZFC raw realization
建立这两条合同；上层 certified proof 反演只消费合同本身。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open ProofCode
open GodelQuotation

set_option autoImplicit false

/--
对象有限序列编码的规范反演接口。

字段中的新鲜性条件仅防止对象存在消去捕获调用方项或上下文，不增加理论强度。
-/
structure SequenceInversion (T : SetTheory) where
  /-- 自然数 token 序列由其规范 Gödel 码唯一决定。 -/
  nat_unique :
    ∀ {Γ : Context signature}
      (sequence code : SetTerm)
      (tokens : List Nat)
      (traceId indexId : FreeVarId),
      Term.Admissible sequence SetSort.set →
      Term.Admissible code SetSort.set →
      traceId ≠ indexId →
      (SetSort.set, traceId) ∉ Term.freeSupport sequence →
      (SetSort.set, indexId) ∉ Term.freeSupport sequence →
      (SetSort.set, indexId) ∉ Term.freeSupport code →
      (∀ formula, formula ∈ Γ →
        (SetSort.set, traceId) ∉ Formula.freeSupport formula) →
      Γ ⊢ₘ[T]
        nat_sequence_code_condition_with_ids
          sequence code traceId indexId →
      Γ ⊢ₘ[T]
        code ≐ₘ numₘ(nat_sequence_code_value tokens) →
      Γ ⊢ₘ[T]
        sequence ≐ₘ standard_token_sequence tokens
  /-- 二维证明行序列由其规范 Gödel 码唯一决定。 -/
  proof_unique :
    ∀ {Γ : Context signature}
      (sequence code : SetTerm)
      (rows : List (List Nat))
      (traceId indexId rowCodeId rowTraceId rowIndexId : FreeVarId),
      Term.Admissible sequence SetSort.set →
      Term.Admissible code SetSort.set →
      traceId ≠ indexId →
      traceId ≠ rowCodeId →
      traceId ≠ rowTraceId →
      indexId ≠ rowCodeId →
      indexId ≠ rowTraceId →
      indexId ≠ rowIndexId →
      rowCodeId ≠ rowTraceId →
      rowCodeId ≠ rowIndexId →
      rowTraceId ≠ rowIndexId →
      (SetSort.set, traceId) ∉ Term.freeSupport sequence →
      (SetSort.set, indexId) ∉ Term.freeSupport sequence →
      (SetSort.set, indexId) ∉ Term.freeSupport code →
      (SetSort.set, rowCodeId) ∉ Term.freeSupport sequence →
      (SetSort.set, rowCodeId) ∉ Term.freeSupport code →
      (SetSort.set, rowTraceId) ∉ Term.freeSupport sequence →
      (SetSort.set, rowTraceId) ∉ Term.freeSupport code →
      (SetSort.set, rowIndexId) ∉ Term.freeSupport sequence →
      (∀ formula, formula ∈ Γ →
        (SetSort.set, traceId) ∉ Formula.freeSupport formula) →
      (∀ formula, formula ∈ Γ →
        (SetSort.set, rowCodeId) ∉ Formula.freeSupport formula) →
      (∀ formula, formula ∈ Γ →
        (SetSort.set, rowTraceId) ∉ Formula.freeSupport formula) →
      Γ ⊢ₘ[T]
        proof_sequence_code_condition_with_ids
          sequence code traceId indexId
          rowCodeId rowTraceId rowIndexId →
      Γ ⊢ₘ[T]
        code ≐ₘ numₘ(proof_sequence_code_value rows) →
      Γ ⊢ₘ[T]
        sequence ≐ₘ
          standard_sequence
            (rows.map standard_token_sequence)

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
