import YesMetaZFC.SetTheory.Definitional.Project.Syntax

/-!
# Jech 风格可定义类的纯语法层

类不是对象语言中的新对象；这里只把它表示为带一个额外 bound 位置的项目公式。
本模块不引入结构、环境或满足关系。
-/

namespace YesMetaZFC
namespace SetTheory
namespace Definitional
namespace Project

/-- 带 `depth` 个外层 bound 参数的可定义类。 -/
abbrev DefinableClass (depth : Nat) := Formula 1 (depth + 1)

namespace DefinableClass

/-- 类公式中代表当前元素的项。 -/
def element {depth : Nat} : Term (depth + 1) :=
  Term.newest

/-- 把一个集合项视为由其元素定义的类。 -/
def ofSet {depth : Nat} (set : Term depth) : DefinableClass depth :=
  .mem element set.weaken

/-- 全类。 -/
def universal {depth : Nat} : DefinableClass depth :=
  Formula.extensionalEq element element

/-- 类的补。 -/
def complement {depth : Nat} (collection : DefinableClass depth) :
    DefinableClass depth :=
  .neg collection

/-- 类的交。 -/
def inter {depth : Nat} (left right : DefinableClass depth) :
    DefinableClass depth :=
  .conj left right

/-- 类的并。 -/
def union {depth : Nat} (left right : DefinableClass depth) :
    DefinableClass depth :=
  .disj left right

/-- 类的差。 -/
def diff {depth : Nat} (left right : DefinableClass depth) :
    DefinableClass depth :=
  .conj left (.neg right)

/-- 一个项属于公式定义的类。 -/
def contains {depth : Nat} (collection : DefinableClass depth)
    (term : Term depth) : Formula 1 depth :=
  collection.instantiateTop term

/-- 两个类逐点等价。 -/
def equal {depth : Nat} (left right : DefinableClass depth) :
    Formula 1 depth :=
  .forallE (.iff left right)

/-- 类包含。 -/
def subset {depth : Nat} (left right : DefinableClass depth) :
    Formula 1 depth :=
  .forallE (.imp left right)

private def atInnermost {depth : Nat} (collection : DefinableClass depth) :
    Formula 1 ((depth + 1) + 1) :=
  collection.bind <| Fin.cases Term.newest fun parameter =>
    .bound parameter.succ.succ

/-- Jech 的并类。 -/
def sUnion {depth : Nat} (collection : DefinableClass depth) :
    DefinableClass depth :=
  .existsE <|
    .conj (.mem element.weaken Term.newest)
      collection.atInnermost

end DefinableClass
end Project
end Definitional
end SetTheory
end YesMetaZFC
