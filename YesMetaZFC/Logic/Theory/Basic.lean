import YesMetaZFC.Logic.Syntax
/-!
# 一阶理论的纯语法基本层

理论保持为公式谓词；本模块只给出外延构造与有限公理化性质，不引入结构、满足关系
或语义蕴涵。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
universe u v w x
/-- 理论是公式谓词。这里保持 extensional 表示，方便章节公理和搜索证书注入。 -/
abbrev Theory (σ : Signature.{u, v, w}) := Formula σ → Prop
namespace Theory
def empty {σ : Signature.{u, v, w}} : Theory σ :=
  fun _ => False
def singleton {σ : Signature.{u, v, w}} (φ : Formula σ) : Theory σ :=
  fun ψ => ψ = φ
def insert {σ : Signature.{u, v, w}} (φ : Formula σ) (T : Theory σ) : Theory σ :=
  fun ψ => ψ = φ ∨ T ψ
def union {σ : Signature.{u, v, w}} (T U : Theory σ) : Theory σ :=
  fun φ => T φ ∨ U φ
/--
一个理论是有限公理化的，当且仅当其字面公理谓词对应有限集合。
这里保留理论的外延谓词表示，同时要求存在一张逐点精确的有限公理表；具体公理表
只在需要构造对象编码时选择，不把某个全局枚举固定进逻辑内核。
-/
def FinitelyAxiomatized {σ : Signature.{u, v, w}} (T : Theory σ) : Prop :=
  ∃ axioms : List (Formula σ),
    ∀ φ, T φ ↔ φ ∈ axioms
/-- 空理论是有限公理化的。 -/
theorem finitely_axiomatized_empty
    {σ : Signature.{u, v, w}} :
    FinitelyAxiomatized (empty : Theory σ) := by
  refine ⟨[], ?_⟩
  intro φ
  simp [empty]
/-- 单例理论是有限公理化的。 -/
theorem finitely_axiomatized_singleton
    {σ : Signature.{u, v, w}} (φ : Formula σ) :
    FinitelyAxiomatized (singleton φ) := by
  refine ⟨[φ], ?_⟩
  intro ψ
  simp [singleton]
/-- 在有限公理化理论上插入一条公理仍然有限公理化。 -/
theorem finitely_axiomatized_insert
    {σ : Signature.{u, v, w}}
    {φ : Formula σ} {T : Theory σ} (hT : FinitelyAxiomatized T) :
    FinitelyAxiomatized (insert φ T) := by
  rcases hT with ⟨axioms, hAxioms⟩
  refine ⟨φ :: axioms, ?_⟩
  intro ψ
  simp [insert, hAxioms]
/-- 两个有限公理化理论的并仍然有限公理化。 -/
theorem finitely_axiomatized_union
    {σ : Signature.{u, v, w}}
    {T U : Theory σ} (hT : FinitelyAxiomatized T) (hU : FinitelyAxiomatized U) :
    FinitelyAxiomatized (union T U) := by
  rcases hT with ⟨leftAxioms, hLeft⟩
  rcases hU with ⟨rightAxioms, hRight⟩
  refine ⟨leftAxioms ++ rightAxioms, ?_⟩
  intro φ
  simp [union, hLeft, hRight]
end Theory
end FirstOrder
end Logic
end YesMetaZFC
