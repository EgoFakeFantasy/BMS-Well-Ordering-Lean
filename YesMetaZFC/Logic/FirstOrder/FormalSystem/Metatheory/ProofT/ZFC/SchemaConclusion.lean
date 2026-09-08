import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicQuotationEvaluation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicKernel

/-!
# 三类已解析公理模式的结论比较表示

输入是带实际参数和闭性证明的模式体，输出为当前 AST 的模式实例。
本层完成此输出与任意目标闭句之间的正负对象表达，作为模式检查器的最后一步。
尚未把原始自然数中的参数、body 与输出连接为一个统一对象图；不把本层的类型化
输入误记为任意自然数公理证书的完整正负表示。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaConclusion
open Nonlogical.BasicSetTheory QuineEncoding.SyntaxCoding
open _root_.YesMetaZFC.SetTheory.Definitional
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
set_option autoImplicit false

/-- 替换只作为待检查的模式实例进入本类型，不改变原 ZFC 公理呈现。 -/
inductive Instance where
  | separation {n : Nat} (schema : Project.UnarySchema n)
  | collection {n : Nat} (schema : Project.BinarySchema n)
  | replacement {n : Nat} (schema : Project.BinarySchema n)

def sourceSentence : Instance → Project.Sentence
  | .separation schema => _root_.YesMetaZFC.SetTheory.Axioms.Schema.separation schema
  | .collection schema => _root_.YesMetaZFC.SetTheory.Axioms.Schema.collection schema
  | .replacement schema => _root_.YesMetaZFC.SetTheory.Axioms.Schema.replacement schema

def conclusion (candidate : Instance) : SetSentence :=
  QuineEncoding.project_sentence (sourceSentence candidate)

/-- 结论检查保留原始 AST 的精确相等标准。 -/
def check (candidate : Instance) (target : SetSentence) : Bool :=
  decide (formula_code (conclusion candidate) = formula_code target)

@[simp] theorem check_eq_true_iff (candidate : Instance) (target : SetSentence) :
    check candidate target = true ↔ conclusion candidate = target := by
  simp only [check, decide_eq_true_eq]
  exact ⟨fun h => formula_code_injective h, congrArg formula_code⟩

/-- 单一二元 Δ₀ 模板只检查两个已经得到的公式码是否相等。 -/
def condition : FormulaTemplate.Binary where
  body := .equal (.fvar .here) (.fvar (.there .here))

theorem condition_delta0 {bound free : SetContext} (expected target : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound (condition expected target) :=
  Formula.IsDelta0.equal expected target

/-- 三类模式的正确结论均获得真实对象推导。 -/
theorem positive (candidate : Instance) (target : SetSentence)
    (h : check candidate target = true) :
    Derives intrinsic_zfc_theory []
      (condition (IntrinsicQuotation.quote (conclusion candidate))
        (IntrinsicQuotation.quote target)) := by
  have hEq := (check_eq_true_iff candidate target).mp h
  rw [← hEq]
  exact Metatheory.Derives.equality_refl _

/-- 任意错误结论的码相等条件均可在原支撑理论内否定，无一致性假设。 -/
theorem negative (candidate : Instance) (target : SetSentence)
    (h : check candidate target = false) :
    Derives intrinsic_zfc_theory []
      (¬ₘ condition (IntrinsicQuotation.quote (conclusion candidate))
        (IntrinsicQuotation.quote target)) := by
  apply IntrinsicQuotation.quote_ne intrinsic_zfc_certificate_core
  intro hEq
  have hTrue := (check_eq_true_iff candidate target).mpr hEq
  rw [h] at hTrue
  contradiction

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaConclusion
