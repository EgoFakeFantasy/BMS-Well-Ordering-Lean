import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.DefinitionContracts
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.FormulaConstruction
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.StandardTokenSequence

/-!
# `ProofT` 的对象 replay 接口

对象 replay 的定义展开与有限证书算术彼此独立。本接口只记录宿主理论对 Gödel
quotation 和逻辑规则编码理论的包含关系；标准有限序列语义已是 quotation 理论的
子层，不单独增加冗余字段。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open GodelQuotation

set_option autoImplicit false

/-- 对象 replay 所需的两条定义理论包含关系。 -/
structure ObjectReplay (T : SetTheory) where
  /-- 宿主理论包含 Gödel quotation 定义层。 -/
  godel_quotation :
    ∀ {formula : SetFormula},
      godel_quotation_theory formula → T formula
  /-- 宿主理论包含对象 Hilbert 逻辑规则编码层。 -/
  logical_rules :
    ∀ {formula : SetFormula},
      logical_rule_encoding_theory formula → T formula

namespace ObjectReplay

/-- 标准有限序列语义经 quotation 理论的首分支进入宿主理论。 -/
theorem standard_sequence
    {T : SetTheory}
    (R : ObjectReplay T)
    {formula : SetFormula}
    (hFormula : standard_sequence_semantics_theory formula) :
    T formula :=
  R.godel_quotation (Or.inl hFormula)

/-- 规范 token 序列的定义域等于其外部列表长度。 -/
theorem standard_token_sequence_domain
    {T : SetTheory}
    (R : ObjectReplay T)
    {Γ : Context signature}
    (tokens : List Nat) :
    Γ ⊢ₘ[T]
      domₘ(standard_token_sequence tokens) ≐ₘ
        numₘ(tokens.length) := by
  apply FirstOrder.Derives.context_weaken
    (Γ := [])
    (Δ := Γ)
    (by simp)
  exact FirstOrder.Derives.theory_weaken
    (fun _ hFormula => R.standard_sequence hFormula)
    (standard_token_sequence_domain_eq_length tokens)

end ObjectReplay
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
