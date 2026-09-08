import YesMetaZFC.Logic.Syntax

/-!
# 闭句理论

可信理论只由闭句组成。开放公式属于证明前端或 schema 接口，不再混入理论成员关系，
因此理论公理进入任意自由变量上下文时不需要额外的闭合性证明。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder

universe u v w

/-- 一阶理论是闭句上的外延谓词。 -/
abbrev Theory (σ : Signature.{u, v, w}) := Sentence σ → Prop

namespace Theory

/-- 空理论。 -/
def empty {σ : Signature.{u, v, w}} : Theory σ :=
  fun _ => False

/-- 单公理理论。 -/
def singleton {σ : Signature.{u, v, w}}
    (sentence : Sentence σ) : Theory σ :=
  fun candidate => candidate = sentence

/-- 向理论加入一条闭句公理。 -/
def insert {σ : Signature.{u, v, w}}
    (sentence : Sentence σ) (T : Theory σ) : Theory σ :=
  fun candidate => candidate = sentence ∨ T candidate

/-- 两个理论的并。 -/
def union {σ : Signature.{u, v, w}}
    (T U : Theory σ) : Theory σ :=
  fun sentence => T sentence ∨ U sentence

/-- 理论包含关系。 -/
def Extends {σ : Signature.{u, v, w}}
    (strong weak : Theory σ) : Prop :=
  ∀ {sentence}, weak sentence → strong sentence

/-- 理论外延相等。 -/
@[ext] theorem ext {σ : Signature.{u, v, w}}
    {T U : Theory σ}
    (h : ∀ sentence, T sentence ↔ U sentence) : T = U := by
  funext sentence
  exact propext (h sentence)

/-- 有限公理化只枚举闭句。 -/
def FinitelyAxiomatized {σ : Signature.{u, v, w}}
    (T : Theory σ) : Prop :=
  ∃ axioms : List (Sentence σ),
    ∀ sentence, T sentence ↔ sentence ∈ axioms

/-- 空理论是有限公理化的。 -/
theorem finitely_axiomatized_empty
    {σ : Signature.{u, v, w}} :
    FinitelyAxiomatized (empty : Theory σ) := by
  refine ⟨[], ?_⟩
  intro sentence
  simp [empty]

/-- 单公理理论是有限公理化的。 -/
theorem finitely_axiomatized_singleton
    {σ : Signature.{u, v, w}} (sentence : Sentence σ) :
    FinitelyAxiomatized (singleton sentence) := by
  refine ⟨[sentence], ?_⟩
  intro candidate
  simp [singleton]

/-- 在有限公理化理论中加入闭句仍然有限公理化。 -/
theorem finitely_axiomatized_insert
    {σ : Signature.{u, v, w}}
    {sentence : Sentence σ} {T : Theory σ}
    (hT : FinitelyAxiomatized T) :
    FinitelyAxiomatized (insert sentence T) := by
  rcases hT with ⟨axioms, hAxioms⟩
  refine ⟨sentence :: axioms, ?_⟩
  intro candidate
  simp [insert, hAxioms]

/-- 有限公理化理论的并仍然有限公理化。 -/
theorem finitely_axiomatized_union
    {σ : Signature.{u, v, w}}
    {T U : Theory σ}
    (hT : FinitelyAxiomatized T)
    (hU : FinitelyAxiomatized U) :
    FinitelyAxiomatized (union T U) := by
  rcases hT with ⟨left, hLeft⟩
  rcases hU with ⟨right, hRight⟩
  refine ⟨left ++ right, ?_⟩
  intro sentence
  simp [union, hLeft, hRight]

end Theory
end FirstOrder
end Logic
end YesMetaZFC
