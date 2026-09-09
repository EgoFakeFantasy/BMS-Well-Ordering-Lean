import BMSConstructibleBridge.StageStructure

/-!
# 外部可构造宇宙公式到 YesMetaZFC 公式的翻译

`lean-constructible-universe` 的 `FOFormula n` 以 `Fin n` 同时表示参数和逐层
加入的量词变量；YesMetaZFC 则区分自由变量与 de Bruijn bound 栈。本模块把
外部公式的全部当前变量按逆序放进 bound 栈，并证明两套 Tarski 语义逐公式
一致。这是复用外部库反射定理所需的内核检查边界。
-/

open Set

universe u

namespace YesMetaZFC
namespace BMS
namespace ConstructibleBridge

open Logic FirstOrder

/-- 外部公式元数对应的单排序 bound 上下文。递归方向与外部存在量词一致。 -/
def externalBoundContext : Nat → FirstOrder.SortContext SetTheory.signature
  | 0 => []
  | n + 1 => SetTheory.SetSort.set :: externalBoundContext n

/--
外部语法在元组尾部加入量词变量，内在语法在 bound 栈头部加入变量；这个映射
把外部坐标反向送入内在 de Bruijn 上下文。
-/
def externalBoundVariable : {n : Nat} → Fin n →
    FirstOrder.Variable (externalBoundContext n) SetTheory.SetSort.set
  | 0, index => Fin.elim0 index
  | n + 1, index =>
      Fin.lastCases (.here : FirstOrder.Variable
        (externalBoundContext (n + 1)) SetTheory.SetSort.set)
        (fun prior => .there (externalBoundVariable prior)) index

@[simp]
theorem externalBoundVariable_last (n : Nat) :
    externalBoundVariable (Fin.last n) =
      (.here : FirstOrder.Variable
        (externalBoundContext (n + 1)) SetTheory.SetSort.set) := by
  exact Fin.lastCases_last

@[simp]
theorem externalBoundVariable_castSucc {n : Nat} (index : Fin n) :
    externalBoundVariable index.castSucc =
      .there (externalBoundVariable index) := by
  exact Fin.lastCases_castSucc index

/-- 外部 `FOFormula` 到纯成员语言公式的结构递归翻译。 -/
def translateExternalFormula : {n : Nat} → Constructible.FOFormula n →
    FirstOrder.Formula SetTheory.signature (externalBoundContext n) []
  | _, .mem left right =>
      .rel SetTheory.RelationSymbol.membership
        (.cons (.bvar (externalBoundVariable left))
          (.cons (.bvar (externalBoundVariable right)) .nil))
  | _, .eq left right =>
      .equal
        (.bvar (externalBoundVariable left))
        (.bvar (externalBoundVariable right))
  | _, .neg formula => .neg (translateExternalFormula formula)
  | _, .conj left right =>
      .conj (translateExternalFormula left) (translateExternalFormula right)
  | _, .ex body =>
      .existsE SetTheory.SetSort.set (translateExternalFormula body)

/-- 从 YesMetaZFC 的逆序 bound 栈读出外部公式所需的 `Fin n` 赋值。 -/
def externalBoundTuple {alpha : Ordinal.{u}}
    {hNonempty : Nonempty (StageCarrier alpha)}
    {n : Nat}
    (env : FirstOrder.Env (lStageStructure alpha hNonempty)
      (externalBoundContext n) []) :
    Constructible.Tuple (StageCarrier alpha) n :=
  fun index => env.boundVal (externalBoundVariable index)

/-- 从外部元组规范地构造逆序 bound 环境。 -/
def externalEnvOfTuple {alpha : Ordinal.{u}}
    (hNonempty : Nonempty (StageCarrier alpha)) :
    {n : Nat} → Constructible.Tuple (StageCarrier alpha) n →
      FirstOrder.Env (lStageStructure alpha hNonempty)
        (externalBoundContext n) []
  | 0, _ => FirstOrder.Env.empty
  | n + 1, tuple =>
      (externalEnvOfTuple hNonempty (Fin.init tuple)).pushBound
        (tuple (Fin.last n))

/-- 压入一个 bound 值正好对应在外部赋值末尾追加该值。 -/
theorem externalBoundTuple_pushBound {alpha : Ordinal.{u}}
    {hNonempty : Nonempty (StageCarrier alpha)}
    {n : Nat}
    (env : FirstOrder.Env (lStageStructure alpha hNonempty)
      (externalBoundContext n) [])
    (value : StageCarrier alpha) :
    externalBoundTuple
        (env.pushBound value) =
      Constructible.snoc (externalBoundTuple env) value := by
  funext index
  refine Fin.lastCases ?_ (fun prior => ?_) index
  · simp [externalBoundTuple, Constructible.snoc]
    rfl
  · simp [externalBoundTuple, Constructible.snoc]
    rfl

/-- 规范环境重新读出原外部元组。 -/
@[simp]
theorem externalBoundTuple_externalEnvOfTuple
    {alpha : Ordinal.{u}} (hNonempty : Nonempty (StageCarrier alpha))
    {n : Nat} (tuple : Constructible.Tuple (StageCarrier alpha) n) :
    externalBoundTuple (externalEnvOfTuple hNonempty tuple) = tuple := by
  induction n with
  | zero =>
      funext index
      exact Fin.elim0 index
  | succ n ih =>
      rw [externalEnvOfTuple, externalBoundTuple_pushBound, ih]
      funext index
      refine Fin.lastCases ?_ (fun prior => ?_) index
      · rw [Constructible.snoc_last]
      · rw [Constructible.snoc_castSucc]
        rfl

/-- 翻译保持 `L_alpha` 上的 Tarski 满足关系。 -/
theorem satisfies_translateExternalFormula_iff
    {alpha : Ordinal.{u}}
    {hNonempty : Nonempty (StageCarrier alpha)}
    {arity : Nat} (formula : Constructible.FOFormula arity)
    (env : FirstOrder.Env (lStageStructure alpha hNonempty)
      (externalBoundContext arity) []) :
    FirstOrder.Formula.satisfies env
        (translateExternalFormula formula) ↔
      Constructible.FOFormula.Satisfies
        (fun left right : StageCarrier alpha => left.1 ∈ right.1)
        formula (externalBoundTuple env) := by
  induction formula with
  | mem left right =>
      rfl
  | eq left right =>
      rfl
  | neg formula ih =>
      exact not_congr (ih env)
  | conj left right ihLeft ihRight =>
      exact and_congr (ihLeft env) (ihRight env)
  | ex body ih =>
      simp only [translateExternalFormula,
        FirstOrder.Formula.satisfies,
        Constructible.FOFormula.Satisfies]
      constructor
      · rintro ⟨value, hBody⟩
        refine ⟨value, ?_⟩
        rw [← externalBoundTuple_pushBound env value]
        exact (ih (env.pushBound value)).mp hBody
      · rintro ⟨value, hBody⟩
        refine ⟨value, ?_⟩
        apply (ih (env.pushBound value)).mpr
        rw [externalBoundTuple_pushBound env value]
        exact hBody

/-- 语义桥的 raw `L_alpha` 版本。 -/
theorem satisfies_translateExternalFormula_iff_satisfiesIn
    {alpha : Ordinal.{u}}
    {hNonempty : Nonempty (StageCarrier alpha)}
    {n : Nat} (formula : Constructible.FOFormula n)
    (env : FirstOrder.Env (lStageStructure alpha hNonempty)
      (externalBoundContext n) []) :
    FirstOrder.Formula.satisfies env
        (translateExternalFormula formula) ↔
      Constructible.Model.SatisfiesIn
        (Constructible.LStageZF alpha : Set ZFSet.{u}) formula
        (fun index => (externalBoundTuple env index).1) := by
  rw [satisfies_translateExternalFormula_iff]
  exact Constructible.Model.satisfies_stageCarrier_iff_satisfiesIn
    formula (externalBoundTuple env)

end ConstructibleBridge
end BMS
end YesMetaZFC
