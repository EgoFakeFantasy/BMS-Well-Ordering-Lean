import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SequenceCondition
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceGraph
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceDomainSemantics

/-!
# `ProofT` 的内在有限序列编码反演核心

证明序列直接表示为由外部 `List` 递归生成的有限函数图。作用域、排序和存在见证均由
内在类型及对象公式自身携带；公共反演接口不再暴露裸变量编号、自由支撑、
`Admissible` 或 token 序列。
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

set_option autoImplicit false

/-! ## 宿主侧规范有限图 -/

/-- 自然数列表对应的标准有限图。 -/
def nat_sequence_graph_term {bound free : SetContext}
    (tokens : List Nat) : SetTerm bound free :=
  standard_sequence_from 0 <|
    tokens.map fun token => numₘ(token)

/-- 二维自然数列表对应的标准有限图。 -/
def proof_sequence_graph_term {bound free : SetContext}
    (rows : List (List Nat)) : SetTerm bound free :=
  standard_sequence_from 0 <|
    rows.map fun row => nat_sequence_graph_term row

/-- 规范自然数序列图的定义域等于其外部长度 numeral。 -/
theorem nat_sequence_graph_domain_eq
    {T : SetTheory} (S : FiniteSequenceGraphSupport T)
    {free : SetContext} {Γ : Context signature free}
    (tokens : List Nat) :
    Γ ⊢ₘ[T]
      domₘ(nat_sequence_graph_term tokens) ≐ₘ numₘ(tokens.length) := by
  simpa [nat_sequence_graph_term, standard_sequence] using
    (standard_sequence_domain_eq
      (Γ := Γ) S
      (elements := tokens.map fun token => numₘ(token)))

/-- 规范证明行序列图的定义域等于其外部行数 numeral。 -/
theorem proof_sequence_graph_domain_eq
    {T : SetTheory} (S : FiniteSequenceGraphSupport T)
    {free : SetContext} {Γ : Context signature free}
    (rows : List (List Nat)) :
    Γ ⊢ₘ[T]
      domₘ(proof_sequence_graph_term rows) ≐ₘ numₘ(rows.length) := by
  simpa [proof_sequence_graph_term, standard_sequence] using
    (standard_sequence_domain_eq
      (Γ := Γ) S
      (elements := rows.map fun row => nat_sequence_graph_term row))

@[simp] theorem nat_sequence_graph_term_nil
    {bound free : SetContext} :
    nat_sequence_graph_term
        (bound := bound) (free := free) [] = ∅ₘ :=
  rfl

@[simp] theorem nat_sequence_graph_term_cons
    {bound free : SetContext}
    (token : Nat) (tokens : List Nat) :
      nat_sequence_graph_term
        (bound := bound) (free := free) (token :: tokens) =
      {⟨numₘ(0), numₘ(token)⟩ₘ}ₘ ∪ₘ
        standard_sequence_from 1
          (tokens.map fun item => numₘ(item)) :=
  rfl

@[simp] theorem proof_sequence_graph_term_nil
    {bound free : SetContext} :
    proof_sequence_graph_term
        (bound := bound) (free := free) [] = ∅ₘ :=
  rfl

@[simp] theorem proof_sequence_graph_term_cons
    {bound free : SetContext}
    (row : List Nat) (rows : List (List Nat)) :
      proof_sequence_graph_term
        (bound := bound) (free := free) (row :: rows) =
      {⟨numₘ(0), nat_sequence_graph_term row⟩ₘ}ₘ ∪ₘ
        standard_sequence_from 1
          (rows.map fun tail => nat_sequence_graph_term tail) :=
  rfl

/--
对象有限序列编码的规范反演接口。

两个字段只保留真正的数学义务：编码关系与标准宿主码共同决定唯一的有限图。
编码公式内部的 trace 和逐点见证已经由内在 free 上下文闭合。
-/
structure SequenceInversion (T : SetTheory) where
  /-- 自然数序列由其规范结构码唯一决定。 -/
  nat_unique :
    ∀ {free : SetContext}
      {Γ : Context signature free}
      (sequence code : SetOpenTerm free)
      (tokens : List Nat),
      Γ ⊢ₘ[T] nat_sequence_code_condition sequence code →
      Γ ⊢ₘ[T]
        code ≐ₘ numₘ(nat_sequence_code_value tokens) →
      Γ ⊢ₘ[T]
        sequence ≐ₘ nat_sequence_graph_term tokens
  /-- 证明行序列由其规范结构码唯一决定。 -/
  proof_unique :
    ∀ {free : SetContext}
      {Γ : Context signature free}
      (sequence code : SetOpenTerm free)
      (rows : List (List Nat)),
      Γ ⊢ₘ[T] proof_sequence_code_condition sequence code →
      Γ ⊢ₘ[T]
        code ≐ₘ numₘ(proof_sequence_code_value rows) →
      Γ ⊢ₘ[T]
        sequence ≐ₘ proof_sequence_graph_term rows

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
