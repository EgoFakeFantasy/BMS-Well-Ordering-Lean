import YesMetaZFC.SetTheory.Definitional.Project.Syntax

/-!
# 项目集合论理论的纯语法层

本模块只定义项目句子理论及其有限集合构造，不引入结构、解释或语义蕴涵。
-/

namespace YesMetaZFC
namespace SetTheory

/-- 项目原子核理论是项目句子的谓词。 -/
abbrev Theory :=
  Definitional.Project.Theory

namespace Theory

def empty : Theory :=
  fun _ => False

def singleton (sentence : Definitional.Project.Sentence) : Theory :=
  fun candidate => candidate = sentence

def insert (sentence : Definitional.Project.Sentence)
    (theory : Theory) : Theory :=
  fun candidate => candidate = sentence ∨ theory candidate

def union (left right : Theory) : Theory :=
  fun sentence => left sentence ∨ right sentence

end Theory
end SetTheory
end YesMetaZFC
