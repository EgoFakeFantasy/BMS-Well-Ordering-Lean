import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding
import YesMetaZFC.SetTheory.Language

/-!
# 纯集合论签名的 Quine 编码实例

纯集合论只有隶属关系，因此结构码实例不需要函数编号或普通谓词编号。
-/

namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding

open Nonlogical.BasicSetTheory

instance pure_set_quotation_numbering : QuotationNumbering ℒ where
  objectSort := SetTheory.SetSort.set
  sort_eq_object := by
    intro sort
    cases sort
    rfl
  function_number := fun function => nomatch function
  relation_number
    | SetTheory.RelationSymbol.membership => 0
  function_number_injective := by
    intro function
    exact nomatch function
  relation_number_injective := by
    intro left right _
    cases left
    cases right
    rfl
  relation_kind
    | SetTheory.RelationSymbol.membership => .membership
  membership_domain := by
    intro relation _
    cases relation
    rfl
  membership_unique := by
    intro left right _ _
    cases left
    cases right
    rfl

@[simp]
theorem pure_set_relation_kind :
    pure_set_quotation_numbering.relation_kind
        SetTheory.RelationSymbol.membership =
      QuotationRelationKind.membership :=
  rfl

@[simp]
theorem pure_set_relation_number :
    pure_set_quotation_numbering.relation_number
        SetTheory.RelationSymbol.membership = 0 :=
  rfl

abbrev pure_code := Code

abbrev pure_quote_term {bound free : SortContext ℒ}
    {sort : SetTheory.SetSort} (term : Term ℒ bound free sort) : pure_code :=
  quote_term term

abbrev pure_quote {bound free : SortContext ℒ}
    (formula : Formula ℒ bound free) : pure_code :=
  quote formula

end YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding
