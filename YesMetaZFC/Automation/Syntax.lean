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
def bvar {σ : SetLevel.Signature} {bound free : SortContext σ}
    {sort : σ.SortSymbol} (entry : Variable bound sort) :
    Term σ bound free sort :=
  .bvar entry
def fvar {σ : SetLevel.Signature} {bound free : SortContext σ}
    {sort : σ.SortSymbol} (entry : Variable free sort) :
    Term σ bound free sort :=
  .fvar entry
def app {σ : SetLevel.Signature} {bound free : SortContext σ}
    (f : σ.FuncSymbol) (args : Arguments σ bound free (σ.funcDomain f)) :
    Term σ bound free (σ.funcCodomain f) :=
  .app f args
def rel {σ : SetLevel.Signature} {bound free : SortContext σ}
    (r : σ.RelSymbol) (args : Arguments σ bound free (σ.relDomain r)) :
    Formula σ bound free :=
  .rel r args
def equal {σ : SetLevel.Signature} {bound free : SortContext σ}
    {sort : σ.SortSymbol} (left right : Term σ bound free sort) :
    Formula σ bound free :=
  .equal left right
def falsum {σ : SetLevel.Signature} {bound free : SortContext σ} :
    Formula σ bound free := .falsum
def truth {σ : SetLevel.Signature} {bound free : SortContext σ} :
    Formula σ bound free := .truth
def neg {σ : SetLevel.Signature} {bound free : SortContext σ}
    (φ : Formula σ bound free) : Formula σ bound free := .neg φ
def conj {σ : SetLevel.Signature} {bound free : SortContext σ}
    (φ ψ : Formula σ bound free) : Formula σ bound free := .conj φ ψ
def disj {σ : SetLevel.Signature} {bound free : SortContext σ}
    (φ ψ : Formula σ bound free) : Formula σ bound free := .disj φ ψ
def imp {σ : SetLevel.Signature} {bound free : SortContext σ}
    (φ ψ : Formula σ bound free) : Formula σ bound free := .imp φ ψ
def iff {σ : SetLevel.Signature} {bound free : SortContext σ}
    (φ ψ : Formula σ bound free) : Formula σ bound free := .iff φ ψ
def forallE {σ : SetLevel.Signature} {bound free : SortContext σ}
    (sort : σ.SortSymbol) (body : Formula σ (sort :: bound) free) :
    Formula σ bound free :=
  .forallE sort body
def existsE {σ : SetLevel.Signature} {bound free : SortContext σ}
    (sort : σ.SortSymbol) (body : Formula σ (sort :: bound) free) :
    Formula σ bound free :=
  .existsE sort body
def problem {σ : SetLevel.Signature} (premises : List (SetLevel.Sentence σ))
    (target : SetLevel.Sentence σ) : SetLevel.DeepProblem σ where
  premises := premises
  target := target
def valid {σ : SetLevel.Signature} (target : SetLevel.Sentence σ)
    (cert : SetLevel.SemanticCertificate SetLevel.Theory.empty target) :
    SetLevel.CheckedValidCertificate (σ := σ) where
  target := target
  cert := cert
def checked {σ : SetLevel.Signature} (problem : SetLevel.DeepProblem σ)
    (cert : SetLevel.DeepProblem.Certificate problem) :
    SetLevel.CheckedCertificate (σ := σ) where
  problem := problem
  cert := cert
end DeepSyntax
end Automation
end YesMetaZFC
