import YesMetaZFC.SetTheory.Definitional.Language

/-!
# 带定义原子理论的纯语法层

本模块只定义理论作为句子谓词及其有限集合构造，不引入模型或语义蕴涵。
-/

namespace YesMetaZFC
namespace SetTheory
namespace Definitional

universe u

/-- 新核理论是新核句子的谓词。 -/
abbrev Theory (σ : AtomSignature.{u}) :=
  Sentence σ → Prop

namespace Theory

/-- 空理论。 -/
def empty {σ : AtomSignature.{u}} : Theory σ :=
  fun _ => False

/-- 单句理论。 -/
def singleton {σ : AtomSignature.{u}} (sentence : Sentence σ) :
    Theory σ :=
  fun candidate => candidate = sentence

/-- 向理论加入一个句子。 -/
def insert {σ : AtomSignature.{u}}
    (sentence : Sentence σ) (theory : Theory σ) : Theory σ :=
  fun candidate => candidate = sentence ∨ theory candidate

end Theory
end Definitional
end SetTheory
end YesMetaZFC
