import YesMetaZFC.BMS.FiniteElementarity
import YesMetaZFC.BMS.FiniteReflection
import YesMetaZFC.SetTheory.Language

/-!
# Hunter 有限反射的内在成员语言接口

新版 YesMetaZFC 的公式由 bound/free 排序上下文索引，不再允许用任意自然数充当
自由变量。因此反射证书显式保存公式的两个上下文和源环境；嵌入将整个环境逐项
送到目标结构。这一点不可退化成闭句：Hunter Lemma 2.6 必须固定有限输入中的
下方参数。每个有限输入给出一个具体纯成员公式、它的有限 Lévy 复杂度、目标层
真值，以及从源层真值提取 Lemma 2.6 见证的证明。
-/

namespace YesMetaZFC
namespace BMS

universe u

open Logic FirstOrder

namespace StabilityFrame

/-- 纯成员语言的标准 Lévy 有界关系。 -/
def membershipLevyBound : Formula.LevyBound SetTheory.signature where
  sort := SetTheory.SetSort.set
  relation := SetTheory.RelationSymbol.membership
  domains := rfl

/--
一次有限反射的内在开放公式证书。`sourceEnv` 固定全部外部参数；`extract`
不是附加反射公理，而必须从同一环境下的实际真值构造论文要求的见证。
-/
structure OrdinalElementarityWitness {Label : Type u}
    {frame : StabilityFrame Label} {lowerCount upperCount : Nat}
    (input : FiniteReflectionInput frame lowerCount upperCount) where
  source : FirstOrder.Structure.{0, 0, 0, u} SetTheory.signature
  target : FirstOrder.Structure.{0, 0, 0, u} SetTheory.signature
  embedding : Formula.LevyEmbedding membershipLevyBound source target
  boundContext : FirstOrder.SortContext SetTheory.signature
  freeContext : FirstOrder.SortContext SetTheory.signature
  formula : FirstOrder.Formula SetTheory.signature boundContext freeContext
  sourceEnv : FirstOrder.Env source boundContext freeContext
  formulaLevel : Nat
  formula_isSigma :
    Formula.IsSigmaFinite membershipLevyBound formulaLevel formula
  target_satisfies :
    Formula.satisfies (embedding.mapEnv sourceEnv) formula
  reflects_formula :
    Formula.satisfies (embedding.mapEnv sourceEnv) formula →
      Formula.satisfies sourceEnv formula
  extract :
    Formula.satisfies sourceEnv formula →
      Nonempty (FiniteReflectionWitness input)

namespace OrdinalElementarityWitness

/-- 有限 Lévy 初等性把大结构中的闭句见证反射到小结构并提取 Lemma 2.6。 -/
theorem reflects {Label : Type u} {frame : StabilityFrame Label}
    {lowerCount upperCount : Nat}
    {input : FiniteReflectionInput frame lowerCount upperCount}
    (witness : OrdinalElementarityWitness input) :
    Nonempty (FiniteReflectionWitness input) := by
  apply witness.extract
  exact witness.reflects_formula witness.target_satisfies

end OrdinalElementarityWitness

/-- 每个有限输入都有一个上述内在开放公式反射证书。 -/
def OrdinalElementarityReflectionProperty {Label : Type u}
    (frame : StabilityFrame Label) : Prop :=
  ∀ {lowerCount upperCount : Nat}
    (input : FiniteReflectionInput frame lowerCount upperCount),
      Nonempty (OrdinalElementarityWitness input)

/-- 内在成员公式反射证书统一给出 Hunter Lemma 2.6。 -/
theorem finiteReflectionPrinciple_of_ordinalElementarity
    {Label : Type u} {frame : StabilityFrame Label}
    (hReflection : OrdinalElementarityReflectionProperty frame) :
    FiniteReflectionPrinciple frame := by
  intro lowerCount upperCount input
  rcases hReflection input with ⟨witness⟩
  exact witness.reflects

end StabilityFrame
end BMS
end YesMetaZFC
