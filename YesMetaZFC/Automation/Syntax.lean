import YesMetaZFC.Automation.LogicSoundness
/-!
# 深嵌入语法构造层
这里不再维护旧 MF1 的一阶语法 typeclass，而是直接围绕 `Logic.FirstOrder`
的深嵌入项/公式/理论对象提供轻量构造器。自动化后端和 tactic 层都应优先使用
这些深嵌入构造，而不是先走浅嵌入门户再反射回去。
Lean 的 parser 语法可以后续再补；当前先把可编程构造接口收拢到这里。
-/
namespace YesMetaZFC
namespace Automation
namespace DeepSyntax
open _root_.YesMetaZFC.Logic
open _root_.YesMetaZFC.Logic.FirstOrder
open _root_.YesMetaZFC.Automation.LogicSoundness
def bvar {σ : SetLevel.Signature} (sort : σ.SortSymbol) (idx : Nat) : SetLevel.Term σ :=
  .var (.bvar sort idx)
def fvar {σ : SetLevel.Signature} (sort : σ.SortSymbol) (id : FreeVarId) : SetLevel.Term σ :=
  .var (.fvar sort id)
def app {σ : SetLevel.Signature} (f : σ.FuncSymbol) (args : List (SetLevel.Term σ)) :
    SetLevel.Term σ :=
  .app f args
def rel {σ : SetLevel.Signature} (r : σ.RelSymbol) (args : List (SetLevel.Term σ)) :
    SetLevel.Formula σ :=
  .rel r args
def equal {σ : SetLevel.Signature} (left right : SetLevel.Term σ) :
    SetLevel.Formula σ :=
  .equal left right
def falsum {σ : SetLevel.Signature} : SetLevel.Formula σ := .falsum
def truth {σ : SetLevel.Signature} : SetLevel.Formula σ := .truth
def neg {σ : SetLevel.Signature} (φ : SetLevel.Formula σ) : SetLevel.Formula σ := .neg φ
def conj {σ : SetLevel.Signature} (φ ψ : SetLevel.Formula σ) : SetLevel.Formula σ := .conj φ ψ
def disj {σ : SetLevel.Signature} (φ ψ : SetLevel.Formula σ) : SetLevel.Formula σ := .disj φ ψ
def imp {σ : SetLevel.Signature} (φ ψ : SetLevel.Formula σ) : SetLevel.Formula σ := .imp φ ψ
def iff {σ : SetLevel.Signature} (φ ψ : SetLevel.Formula σ) : SetLevel.Formula σ := .iff φ ψ
def forallE {σ : SetLevel.Signature} (sort : σ.SortSymbol) (body : SetLevel.Formula σ) :
    SetLevel.Formula σ :=
  .forallE sort body
def existsE {σ : SetLevel.Signature} (sort : σ.SortSymbol) (body : SetLevel.Formula σ) :
    SetLevel.Formula σ :=
  .existsE sort body
def problem {σ : SetLevel.Signature} (premises : List (SetLevel.Formula σ)) (target : SetLevel.Formula σ) : SetLevel.DeepProblem σ where
  premises := premises
  target := target
def valid {σ : SetLevel.Signature} [DecidableEq σ.SortSymbol] (target : SetLevel.Formula σ) (cert : SetLevel.SemanticCertificate SetLevel.Theory.empty target) :
    SetLevel.CheckedValidCertificate (σ := σ) where
  target := target
  cert := cert
def checked {σ : SetLevel.Signature} [DecidableEq σ.SortSymbol] (problem : SetLevel.DeepProblem σ) (cert : SetLevel.DeepProblem.Certificate problem) :
    SetLevel.CheckedCertificate (σ := σ) where
  problem := problem
  cert := cert
end DeepSyntax
end Automation
end YesMetaZFC
