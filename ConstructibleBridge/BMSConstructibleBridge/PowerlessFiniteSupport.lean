import BMSConstructibleBridge.PowerlessTheory
import YesMetaZFC.Automation.SyntaxNatCoding
import YesMetaZFC.Logic.FirstOrder.Completeness.StrongCompleteness

/-!
# 原纯集合语言中语义结论的有限公理支持

固定纯签名的公平调度，经过原签名强完备性取得真正 Hilbert 推导，
再沿推导提取有限公理列表。不是检查 Lean 定理依赖，也不只考察标准模型。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteSupport

open Logic FirstOrder
open _root_.YesMetaZFC.Automation.SyntaxNatCoding

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

def symbols_m : SymbolCoding ℒ where
  sort := ⟨fun _ => 0, by intro a b _; cases a; cases b; rfl⟩
  function := ⟨(fun a => nomatch a), by intro a; nomatch a⟩
  relation := ⟨fun _ => 0, by intro a b _; cases a; cases b; rfl⟩

noncomputable def schedule_m : Completeness.Henkin.Schedule ℒ := schedule symbols_m

theorem derives_m {T : Theory ℒ} {φ : Sentence ℒ}
    (h : Theory.SemanticallyEntails.{0, 0, 0, 0} T φ) : Derives T [] φ :=
  Completeness.strong_completeness schedule_m h

theorem finite_m {T : Theory ℒ} {φ : Sentence ℒ}
    (h : Theory.SemanticallyEntails.{0, 0, 0, 0} T φ) :
    Nonempty (Derives.FiniteTheorySupport T [] φ) :=
  Derives.finiteTheorySupport (derives_m h)

theorem models_l {T : Theory ℒ} {φ : Sentence ℒ}
    (h : Theory.SemanticallyEntails.{0, 0, 0, 0} T φ) :
    ∃ Γ : List (Sentence ℒ), (∀ ψ ∈ Γ, T ψ) ∧
      Theory.SemanticallyEntails.{0, 0, 0, u} (Theory.ofList Γ) φ := by
  obtain ⟨S⟩ := finite_m h
  exact ⟨S.sentences, S.subset, S.derivation.semantically_entails⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteSupport
