import BMSConstructibleBridge.PowerlessRelativeSourceFamilyHistory
import BMSConstructibleBridge.PowerlessRelativeSourceFamilyCodedCapture

/-! # 实际共同请求闭包上的全部局部前史捕获

原十七式与两个完整覆盖模板一起生成同一请求族、同一图族及同一个 I。
旧自由上下文增加一个 ω 槽；原历史接口通过子族读取，旧签名不改动。
沿实际存在树保留八项旧正文、全部元素性和参数成员性，再追加：若 W
确为首 Ω 截断源，则每个 x∈I 的十七见证同属这个 I，完整资格在同一
MemberW 中成立。外部 W／Ω 不加入捕获模板，I 不假定传递或外延。
正式出口为原 Z₂ 核中的图翻译 Derives；仍未认同任意捕获图的原 Def，
也未证明全局弱凝聚、完整 Collection、无首 Ω 分支或最终 hSources。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceFamilyCodedCoverage

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open SecondOrderObjectSyntax (member_m)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)
open PowerlessRelativeSourceFamilyClosedImage (term_m frame_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l PowerlessMemberStructure.type_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev Entry (Ε : SortContext ℒ) := Term ℒ [] Ε .set × Term ℒ [] Ε .set
/-- B/D/A/U/ω 五槽；额外原上下文保持不变。 -/
abbrev context_m (Δ : SortContext ℒ) := PowerlessRelativeSourceFamilyHistory.context_m (.set :: Δ)

def family_m (Δ : SortContext ℒ) : PowerlessRelativeFiniteElementarity.family_m (context_m Δ) :=
  PowerlessRelativeSourceFamilyHistory.family_m (.set :: Δ) ++
    PowerlessRelativeFiniteHullCodedCoverage.family_m (context_m Δ)

theorem history_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ Ε : SortContext ℒ} (ζ : Env 𝒩 [] Ε) (I W : Term ℒ [] Ε .set)
    (τ : Variable (context_m Δ) .set → Term ℒ [] Ε .set)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ) :
    (PowerlessRelativeFiniteElementarity.form_m
      (PowerlessRelativeSourceFamilyHistory.family_m (.set :: Δ)) I W τ).satisfies ζ :=
  ((PowerlessRelativeFiniteElementarity.append_formula_l _ _ ζ I W τ).mp h).1

theorem coverage_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ Ε : SortContext ℒ} (ζ : Env 𝒩 [] Ε) (I W : Term ℒ [] Ε .set)
    (τ : Variable (context_m Δ) .set → Term ℒ [] Ε .set)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ) :
    (PowerlessRelativeFiniteElementarity.form_m
      (PowerlessRelativeFiniteHullCodedCoverage.family_m (context_m Δ)) I W τ).satisfies ζ :=
  ((PowerlessRelativeFiniteElementarity.append_formula_l _ _ ζ I W τ).mp h).2

private def omega_m {Δ : SortContext ℒ} : Variable (context_m Δ) .set :=
  .there (.there (.there (.there .here)))

private theorem subset_l (Δ : SortContext ℒ) :
    ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m (context_m Δ), p ∈ family_m Δ :=
  fun _ h => List.mem_append_right _ h

def terminal_m {Θ Δ Ε : SortContext ℒ}
    (B C W ω Q e t₀ t₁ t₂ a P : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m (family_m Δ)) .set →
      Term ℒ [] Θ .set)
    (σ : Variable Θ .set → Term ℒ [] Ε .set) (J : List (Entry Ε)) : Formula ℒ [] Ε :=
  PowerlessRelativeSourceFamilyCodedCapture.terminal_m (family_m Δ) .here omega_m B C W ω Q e t₀ t₁ t₂ a P τ σ J

def conclusion_m {Θ Δ : SortContext ℒ}
    (B C W ω Q e t₀ t₁ t₂ a P R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m (family_m Δ)) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  PowerlessRelativeSourceFamilyCodedCapture.conclusion_m (family_m Δ) .here omega_m B C W ω Q e t₀ t₁ t₂ a P R τ

def schema_m {Θ Δ : SortContext ℒ}
    (B β C W ω Q G e t₀ t₁ t₂ a S P R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m (family_m Δ)) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  PowerlessRelativeSourceFamilyCodedCapture.schema_m (family_m Δ) .here omega_m B β C W ω Q G e t₀ t₁ t₂ a S P R τ

def sentence_m {Θ Δ : SortContext ℒ}
    (B β C W ω Q G e t₀ t₁ t₂ a S P R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m (family_m Δ)) .set →
      Term ℒ [] Θ .set) : Sentence ℒ :=
  PowerlessRelativeSourceFamilyCodedCapture.sentence_m (family_m Δ) .here omega_m B β C W ω Q G e t₀ t₁ t₂ a S P R τ

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem terminal_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (K : source_coding_l hℳ) {Θ Δ Ε : SortContext ℒ}
    (B C W ω Q e t₀ t₁ t₂ a P : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m (family_m Δ)) .set →
      Term ℒ [] Θ .set)
    (σ : Variable Θ .set → Term ℒ [] Ε .set) (J : List (Entry Ε))
    (ζ : Env (SecondOrderQuotient.structure_l hℳ) [] Ε)
    (h : (PowerlessRelativeSourceFamilyElementaryImage.terminal_m (family_m Δ)
      B C W ω Q e t₀ t₁ t₂ a P τ σ J).satisfies ζ) :
    (terminal_m (Δ := Δ) B C W ω Q e t₀ t₁ t₂ a P τ σ J).satisfies ζ :=
  PowerlessRelativeSourceFamilyCodedCapture.terminal_l hℳ K (family_m Δ) (subset_l Δ) .here omega_m
    B C W ω Q e t₀ t₁ t₂ a P τ σ J ζ h

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Θ Δ : SortContext ℒ}
    (B β C W ω Q G e t₀ t₁ t₂ a S P R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m (family_m Δ)) .set →
      Term ℒ [] Θ .set) :
    (sentence_m (Δ := Δ) B β C W ω Q G e t₀ t₁ t₂ a S P R τ).TrueIn
      (SecondOrderQuotient.structure_l hℳ) :=
  PowerlessRelativeSourceFamilyCodedCapture.models_l hℳ (family_m Δ) (subset_l Δ) .here omega_m
    B β C W ω Q G e t₀ t₁ t₂ a S P R τ

theorem derives_m {Θ Δ : SortContext ℒ}
    (B β C W ω Q G e t₀ t₁ t₂ a S P R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m (family_m Δ)) .set →
      Term ℒ [] Θ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m (Δ := Δ) B β C W ω Q G e t₀ t₁ t₂ a S P R τ)) :=
  PowerlessRelativeSourceFamilyCodedCapture.derives_m (family_m Δ) (subset_l Δ) .here omega_m
    B β C W ω Q G e t₀ t₁ t₂ a S P R τ

#print axioms history_l
#print axioms coverage_l
#print axioms terminal_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceFamilyCodedCoverage
