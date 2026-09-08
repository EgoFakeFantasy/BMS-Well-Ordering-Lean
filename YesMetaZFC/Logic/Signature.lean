/-!
# 通用逻辑签名
这一层只描述对象语言的符号表，不携带任何章节语义。
函数与关系的参数排序列表直接索引内在语法中的异质参数列；非法元数和非法排序
不再进入语法类型。
-/
namespace YesMetaZFC
namespace Logic
universe u v w
-- 各字段（或其签名别名）保留独立宇宙；结构类型的 max 不是冗余参数。
set_option linter.checkUnivs false in
/-- 多排序一阶签名。函数和关系的参数排序列表是语法构造子的类型索引。 -/
structure Signature where
  SortSymbol : Type u
  FuncSymbol : Type v
  RelSymbol : Type w
  funcDomain : FuncSymbol → List SortSymbol
  funcCodomain : FuncSymbol → SortSymbol
  relDomain : RelSymbol → List SortSymbol
namespace Signature
/-- 函数字符的元数。 -/
def funcArity (σ : Signature) (f : σ.FuncSymbol) : Nat := (σ.funcDomain f).length
/-- 关系字符的元数。 -/
def relArity (σ : Signature) (r : σ.RelSymbol) : Nat := (σ.relDomain r).length
end Signature
end Logic
end YesMetaZFC
