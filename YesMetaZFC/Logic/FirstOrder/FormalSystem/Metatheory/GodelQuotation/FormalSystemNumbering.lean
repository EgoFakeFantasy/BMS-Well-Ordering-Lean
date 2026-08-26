import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.Numbered
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Language
/-!
# FormalSystem 扩展签名的 quotation 编号
基本集合论/形式系统语言的函数与关系符号都是有限枚举。这里把构造子次序固定为
Gödel quotation 的稳定编号；原生 `membership` 继续使用文献专用的隶属符号编码，
其余关系进入普通谓词符号族。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.GodelQuotation
open Nonlogical.BasicSetTheory
/-- 扩展签名中只有原生隶属关系使用专用编码。 -/
def fs_relation_kind : RelationSymbol → QuotationRelationKind
  | .membership => .membership
  | _ => .predicate
/-- FormalSystem 扩展签名的稳定可编号单排序 quotation 实例。 -/
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
  relation_nonempty := by
    intro relation
    cases relation <;> simp [signature]
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
/-- 非隶属扩展关系统一进入普通谓词符号族。 -/
theorem fs_relation_kind_eq_predicate
    {relation : RelationSymbol} (hRelation : relation ≠ .membership) :
    fs_quotation_numbering.relation_kind relation =
      QuotationRelationKind.predicate := by
  change fs_relation_kind relation = QuotationRelationKind.predicate
  cases relation <;> simp_all [fs_relation_kind]
/-- FormalSystem 的每个 admissible 公式都有规范 Gödel quotation。 -/
theorem fs_quote?_exists {formula : Formula signature} (hFormula : Formula.Admissible formula) :
    ∃ code, Numbered.quote? formula = some code :=
  Numbered.quote?_exists hFormula
end YesMetaZFC.Logic.FirstOrder.FormalSystem.GodelQuotation
