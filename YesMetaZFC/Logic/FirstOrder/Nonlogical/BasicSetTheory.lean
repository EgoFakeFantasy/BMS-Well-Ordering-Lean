import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Language
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Axioms
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Basic
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Separation
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.EmptySet
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.PowerSet
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Pairing
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Union
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Successor
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Intersection
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.RelationFunction
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.CartesianProduct
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Relation
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.RelationProperties
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.RelationComposition
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Function
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.FunctionProperties
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.NaturalDiscreteLinearOrder
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.FiniteOrdinal
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.NaturalNumeral
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.OrderOperators
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.WellOrderComparison
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Ordinal
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Foundation
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.NaturalOrderAlgebra
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.OrderProductMapping
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.IndexOrder
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.PowerSetCoding
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.SymmetricDifference
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.BasicFiniteTheory
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Infinity
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.NaturalSetTheory
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.NaturalArithmetic
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.HypertransfiniteRecursion
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.HereditarilyFinite
/-!
# 基本集合论非逻辑层入口
该入口导出具体签名、数学记号、首组定义公理、分离模式、空集、幂集、配对、
单点集、并集、二元并、后继、一元交、二元交、有序对与投影、笛卡尔积，以及
关系、定义域、值域、关系平方界、关系逆、关系复合、等价关系、函数、映射与
函数求值，以及单射、满射、双射、恒等映射、映射收集、传递集和成员关系限制
的定义与理论基础设施；最后导出线性序、序同构、序嵌入、自然离散线性序、
良序、有限自然数项、关系像分离、映像、函数限制以及最小/最大元算子层。
最后加入严格初始段原子项、关系限制与良序比较的基础理论接口。
随后导出规范良序比较映射、序数与自然数谓词、成员序极值合同，以及解除文献
有限编号护栏后的通用 ε-极小公理模式。
最后导出自然离散线性序的序和与词典序积运算，以及对应的定义公理和理论链。
随后导出映射直积、最小差异点、指数序、幂集二值编码双射与对称差的函数项、
分离规格和理论链；纸面第一分歧点、典型对应与序搬运证明辅助式只留文档索引，
不进入公共签名。最后导出基本有穷理论中的有穷性、等势和基数比较定义设施；
相关闭性与康托尔型结论暂留文档索引。最后导出无穷公理、归纳集、归纳核与
`ω` 常元的定义设施；随后导出自然数集合中的有界/无界子集、自然序型与子集
序型函数项定义设施；随后导出自然数加法、乘法、幂、截断减法、有限/递归序列、
无限与可数性谓词、`ω × ω` 典型序以及 Gödel 配对定义设施；无穷性与自然数
相关定理暂留后续证明层。最后导出替换公理模式与参数化的超限递归定义契约；
映像存在与递归定理暂留后续证明层。最后导出有限层级递归序列、`V_ω`、传递闭包、遗传
有限谓词与有限子集收集的定义设施；自然数成员序、有限编码、有限层级闭性和典型列举
定理暂留后续证明层。
-/
