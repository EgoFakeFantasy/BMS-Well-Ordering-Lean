import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Language

/-!
# FormalSystem 签名的 Quine 编码实例

函数与关系符号直接使用宿主枚举的构造子编号；原生隶属关系使用专用节点，其余
关系统一进入谓词节点。该实例不再依赖 token、名字或边界谓词。
-/

namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding

open Nonlogical.BasicSetTheory
open scoped FormalSystem.Symbols

def fs_relation_kind : RelationSymbol → QuotationRelationKind
  | .membership => .membership
  | _ => .predicate

instance fs_quotation_numbering : QuotationNumbering signature where
  objectSort := SetSort.set
  sort_eq_object := by
    intro sort
    cases sort
    rfl
  function_number := FunctionSymbol.ctorIdx
  relation_number := RelationSymbol.ctorIdx
  function_number_injective := by
    intro left right hEqual
    cases left <;> cases right <;>
      simp_all [FunctionSymbol.ctorIdx]
  relation_number_injective := by
    intro left right hEqual
    cases left <;> cases right <;>
      simp_all [RelationSymbol.ctorIdx]
  relation_kind := fs_relation_kind
  membership_domain := by
    intro relation hKind
    cases relation <;> simp [fs_relation_kind] at hKind
    rfl
  membership_unique := by
    intro left right hLeft hRight
    cases left <;> cases right <;>
      simp_all [fs_relation_kind]

@[simp]
theorem fs_function_number_eq_ctorIdx (function : FunctionSymbol) :
    fs_quotation_numbering.function_number function = function.ctorIdx :=
  rfl

@[simp]
theorem fs_relation_number_eq_ctorIdx (relation : RelationSymbol) :
    fs_quotation_numbering.relation_number relation = relation.ctorIdx :=
  rfl

@[simp]
theorem fs_membership_relation_kind :
    fs_quotation_numbering.relation_kind RelationSymbol.membership =
      QuotationRelationKind.membership :=
  rfl

theorem fs_relation_kind_eq_predicate
    {relation : RelationSymbol} (hRelation : relation ≠ .membership) :
    fs_quotation_numbering.relation_kind relation =
      QuotationRelationKind.predicate := by
  change fs_relation_kind relation = QuotationRelationKind.predicate
  cases relation <;> simp_all [fs_relation_kind]

@[simp] theorem quote_negation (formula : SetSentence) :
    quote (Formula.neg formula) = neg_codeₘ(quote formula) :=
  rfl

@[simp] theorem quote_implication (left right : SetSentence) :
    quote (Formula.imp left right) =
      imp_codeₘ(quote left, quote right) :=
  rfl

abbrev fs_quote {bound free : SortContext signature}
    (formula : Formula signature bound free) : Code :=
  quote formula

end YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding
