import BMSConstructibleBridge.PowerlessBMSWellOrder
import BMSConstructibleBridge.PowerlessFiniteSupport

/-!
# 固定行数 BMS 结论在无幂集理论中的对象证明

原二阶目标 `closed_m H` 经既有关系式算术翻译进入纯隶属语言 ℒ。句子全称
量化 ω 与零，背景仍为明确含 Collection 的 `PowerlessTheory.theory_m`。
本模块交付原推导核的对象证明及其有限公理支持的存在性；它不声称支持已在
Z₂ 中得到解释，也不把外部 H 模式改为一个内部统一的良序断言。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSObjectProof

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessArithmetic.structure_l

universe u

/-- 算术闭句的纯集合翻译，绑定槽依次为零与 ω。 -/
def body_m (φ : Sentence SecondOrderSyntax.signature_m) : Formula ℒ [.set, .set] [] :=
  PowerlessArithmeticTranslation.formula_m (Γ := []) (Δ := [])
    (.bvar (.there .here)) (.bvar .here) (fun v => nomatch v) (fun v => nomatch v) φ

/-- 对同一闭句显式量化 ω 与零。 -/
def closure_m (φ : Sentence SecondOrderSyntax.signature_m) : Sentence ℒ :=
  .forallE .set (.forallE .set (.imp
    (SecondOrderOmegaSyntax.omega_m (.bvar (.there .here)))
    (.imp (.forallE .set (.neg (SecondOrderObjectSyntax.member_m
      (.bvar .here) (.bvar (.there .here))))) (body_m φ))))

theorem closure_formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (φ : Sentence SecondOrderSyntax.signature_m) :
    (closure_m φ).TrueIn ℳ ↔ ∀ ω e : carrier_l ℳ, omega_l ω → PowerlessNatural.zero_l e →
      (body_m φ).satisfies (((Env.empty (M := ℳ)).pushBound ω).pushBound e) := by
  simp only [closure_m, Formula.TrueIn, Formula.satisfies, omega_formula_l]
  rfl

theorem closure_models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (φ : Sentence SecondOrderSyntax.signature_m)
    (hφ : ∀ {ω e : carrier_l ℳ}, omega_l ω →
      ∀ (he : PowerlessNatural.zero_l e) (h₀ : member_l ℳ e ω)
        (F : PowerlessArithmetic.operations_l ω e),
        φ.TrueIn (PowerlessArithmetic.structure_l he h₀ F)) :
    (closure_m φ).TrueIn ℳ := by
  apply (closure_formula_l φ).mpr
  intro ω e hω he
  have h₀ := PowerlessNatural.zero_mem_l hℳ hω he
  obtain ⟨F⟩ := PowerlessArithmetic.operations_exists_l hℳ hω he
  have h := hφ hω he h₀ F
  exact (PowerlessArithmeticTranslation.formula_l hℳ hω
    (he := he) (h₀ := h₀) (F := F) Env.empty
    (((Env.empty (M := ℳ)).pushBound ω).pushBound e)
    (.bvar (.there .here)) (.bvar .here) (fun v => nomatch v) (fun v => nomatch v)
    rfl rfl (fun v => nomatch v) (fun v => nomatch v)
    φ).mpr h

/-- 每个固定外部 H 对应原目标的实际纯集合闭句。 -/
def sentence_m (H : Nat) : Sentence ℒ := closure_m (SecondOrderConcreteFormula.closed_m H)

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (H : Nat) :
    (sentence_m H).TrueIn ℳ :=
  closure_models_l hℳ (SecondOrderConcreteFormula.closed_m H)
    (fun hω he h₀ F => PowerlessBMSWellOrder.models_l hℳ hω (he := he) (h₀ := h₀) (F := F) H)

/-- 完整原背景中的固定高度对象推导，不是仅有模型语义结论。 -/
theorem derives_m (H : Nat) :
    Derives PowerlessTheory.theory_m [] (sentence_m H) :=
  PowerlessFiniteSupport.derives_m (fun _ hℳ => models_l hℳ H)

/-- 实际对象推导只需原背景的有限支持；不在 Type 中选择固定支持列表。 -/
theorem finite_m (H : Nat) :
    Nonempty (Derives.FiniteTheorySupport PowerlessTheory.theory_m [] (sentence_m H)) :=
  Derives.finiteTheorySupport (derives_m H)

/-- 支持的模型可处于任意宇宙；其可靠性直接来自同一个有限 Hilbert 推导。 -/
theorem finite_models_l (H : Nat) :
    ∃ Γ : List (Sentence ℒ), (∀ φ ∈ Γ, PowerlessTheory.theory_m φ) ∧
      Theory.SemanticallyEntails.{0, 0, 0, u} (Theory.ofList Γ) (sentence_m H) := by
  obtain ⟨S⟩ := finite_m H
  exact ⟨S.sentences, S.subset, S.derivation.semantically_entails⟩

#print axioms derives_m
#print axioms finite_m
#print axioms finite_models_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSObjectProof
