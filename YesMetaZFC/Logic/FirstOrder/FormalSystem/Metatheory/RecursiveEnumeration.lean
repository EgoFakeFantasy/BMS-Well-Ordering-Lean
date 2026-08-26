import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CertifiedProofCode
import YesMetaZFC.Logic.FirstOrder.Hilbert.Translation

/-!
# 递归枚举理论的构造性数据层

Rosser 证明只需要目标理论递归可枚举。为了避免从
`Theory.FinitelyAxiomatized : Prop` 中非构造地抽取公理表，本模块提供两层数据：

* `HilbertFinitePresentation` 显式保存一张有限公理表；
* `HilbertTheoryGenerator` 用自然数证书生成候选公理。

生成器只承担外部有限计算。公式相等由调用方提供的单射自然数编码判定，因此公共
接口不要求 `Formula` 具有 `DecidableEq`，也不使用选择公理。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofCode

universe u v w

set_option autoImplicit false

/-- 理论的一张构造性有限公理表。 -/
structure HilbertFinitePresentation
    {σ : Signature.{u, v, w}}
    (theory : Theory σ) where
  axioms : List (Formula σ)
  membership :
    ∀ formula, theory formula ↔ formula ∈ axioms

namespace HilbertFinitePresentation

/-- 空理论的空公理表。 -/
def empty
    {σ : Signature.{u, v, w}} :
    HilbertFinitePresentation (Theory.empty : Theory σ) where
  axioms := []
  membership := by
    intro formula
    simp [Theory.empty]

/-- 单例理论的单元素公理表。 -/
def singleton
    {σ : Signature.{u, v, w}}
    (formula : Formula σ) :
    HilbertFinitePresentation (Theory.singleton formula) where
  axioms := [formula]
  membership := by
    intro candidate
    simp [Theory.singleton]

/-- 在有限 presentation 前端插入一条公理。 -/
def insert
    {σ : Signature.{u, v, w}}
    {theory : Theory σ}
    (formula : Formula σ)
    (presentation : HilbertFinitePresentation theory) :
    HilbertFinitePresentation
      (Theory.insert formula theory) where
  axioms := formula :: presentation.axioms
  membership := by
    intro candidate
    simp [Theory.insert, presentation.membership]

/-- 两张有限公理表按理论并集拼接。 -/
def union
    {σ : Signature.{u, v, w}}
    {leftTheory rightTheory : Theory σ}
    (left : HilbertFinitePresentation leftTheory)
    (right : HilbertFinitePresentation rightTheory) :
    HilbertFinitePresentation
      (Theory.union leftTheory rightTheory) where
  axioms := left.axioms ++ right.axioms
  membership := by
    intro formula
    simp [Theory.union, left.membership, right.membership]

/-- 有限公理表逐项执行 Hilbert 归约。 -/
def hilbertize
    {σ : Signature.{u, v, w}}
    {theory : Theory σ}
    (anchorSort : σ.SortSymbol)
    (presentation : HilbertFinitePresentation theory) :
    HilbertFinitePresentation
      (Theory.hilbertize anchorSort theory) where
  axioms :=
    presentation.axioms.map
      (Formula.hilbertize anchorSort)
  membership := by
    intro formula
    constructor
    · rintro ⟨source, hSource, rfl⟩
      exact List.mem_map.mpr
        ⟨source,
          (presentation.membership source).mp hSource,
          rfl⟩
    · intro hFormula
      rcases List.mem_map.mp hFormula with
        ⟨source, hSource, rfl⟩
      exact
        ⟨source,
          (presentation.membership source).mpr hSource,
          rfl⟩

end HilbertFinitePresentation

/-- Hilbert 归约与理论并集逐点交换。 -/
theorem theory_hilbertize_union
    {σ : Signature.{u, v, w}}
    (anchorSort : σ.SortSymbol)
    (left right : Theory σ) :
    Theory.hilbertize anchorSort (Theory.union left right) =
      Theory.union
  (Theory.hilbertize anchorSort left)
        (Theory.hilbertize anchorSort right) := by
  funext formula
  apply propext
  constructor
  · rintro ⟨source, hSource, rfl⟩
    rcases hSource with hLeft | hRight
    · exact Or.inl ⟨source, hLeft, rfl⟩
    · exact Or.inr ⟨source, hRight, rfl⟩
  · intro hFormula
    rcases hFormula with hLeft | hRight
    · rcases hLeft with ⟨source, hSource, rfl⟩
      exact ⟨source, Or.inl hSource, rfl⟩
    · rcases hRight with ⟨source, hSource, rfl⟩
      exact ⟨source, Or.inr hSource, rfl⟩

/-- 自然数证书到理论公理的可计算生成器。 -/
structure HilbertTheoryGenerator
    {σ : Signature.{u, v, w}}
    (theory : Theory σ) where
  generate : Nat → Option (Formula σ)
  generate_sound :
    ∀ {certificate formula},
      generate certificate = some formula →
        theory formula
  generate_complete :
    ∀ {formula},
      theory formula →
        ∃ certificate,
          generate certificate = some formula

namespace HilbertTheoryGenerator

/-- 列表成员总能由某个 `getElem?` 下标读取。 -/
private theorem list_getElem?_exists_of_mem
    {α : Type u}
    {element : α}
    {elements : List α}
    (hMember : element ∈ elements) :
    ∃ index : Nat, elements[index]? = some element := by
  induction elements with
  | nil =>
      simp at hMember
  | cons head tail ih =>
      rcases List.mem_cons.mp hMember with
        rfl | hTail
      · exact ⟨0, by simp⟩
      · rcases ih hTail with ⟨index, hIndex⟩
        exact ⟨index + 1, by simpa using hIndex⟩

/-- 有限公理表按列表下标生成公理。 -/
def ofFinite
    {σ : Signature.{u, v, w}}
    {theory : Theory σ}
    (presentation : HilbertFinitePresentation theory) :
    HilbertTheoryGenerator theory where
  generate certificate :=
    presentation.axioms[certificate]?
  generate_sound := by
    intro certificate formula hGenerate
    apply (presentation.membership formula).mpr
    exact List.mem_of_getElem? hGenerate
  generate_complete := by
    intro formula hTheory
    have hMember :
        formula ∈ presentation.axioms :=
      (presentation.membership formula).mp hTheory
    exact list_getElem?_exists_of_mem hMember

/-- 两个生成器通过外层配对标签生成理论并集。 -/
def union
    {σ : Signature.{u, v, w}}
    {leftTheory rightTheory : Theory σ}
    (left : HilbertTheoryGenerator leftTheory)
    (right : HilbertTheoryGenerator rightTheory) :
    HilbertTheoryGenerator
      (Theory.union leftTheory rightTheory) where
  generate certificate :=
    let tagPayload := godel_unpair_value certificate
    if tagPayload.1 = 0 then
      left.generate tagPayload.2
    else if tagPayload.1 = 1 then
      right.generate tagPayload.2
    else
      none
  generate_sound := by
    intro certificate formula hGenerate
    simp only at hGenerate ⊢
    split at hGenerate
    next hTag =>
      exact Or.inl <| left.generate_sound hGenerate
    next hNotLeft =>
      split at hGenerate
      next hTag =>
        exact Or.inr <| right.generate_sound hGenerate
      next hNotRight =>
        simp at hGenerate
  generate_complete := by
    intro formula hTheory
    rcases hTheory with hLeft | hRight
    · rcases left.generate_complete hLeft with
        ⟨certificate, hCertificate⟩
      refine
        ⟨godel_pair_value 0 certificate, ?_⟩
      simp [godel_unpair_value_pair, hCertificate]
    · rcases right.generate_complete hRight with
        ⟨certificate, hCertificate⟩
      refine
        ⟨godel_pair_value 1 certificate, ?_⟩
      simp [godel_unpair_value_pair, hCertificate]

/-- 生成器逐项执行 Hilbert 归约。 -/
def hilbertize
    {σ : Signature.{u, v, w}}
    {theory : Theory σ}
    (anchorSort : σ.SortSymbol)
    (generator : HilbertTheoryGenerator theory) :
    HilbertTheoryGenerator
      (Theory.hilbertize anchorSort theory) where
  generate certificate :=
    (generator.generate certificate).map
      (Formula.hilbertize anchorSort)
  generate_sound := by
    intro certificate formula hGenerate
    cases hSource :
        generator.generate certificate with
    | none =>
        simp [hSource] at hGenerate
    | some source =>
        simp only [hSource, Option.map_some,
          Option.some.injEq] at hGenerate
        subst formula
        exact Theory.hilbertize_mem <|
          generator.generate_sound hSource
  generate_complete := by
    intro formula hTheory
    rcases hTheory with ⟨source, hSource, rfl⟩
    rcases generator.generate_complete hSource with
      ⟨certificate, hCertificate⟩
    exact ⟨certificate, by simp [hCertificate]⟩

/-- 用单射自然数编码把候选生成器收紧为布尔 verifier。 -/
def toEnumeration
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {theory : Theory σ}
    (generator : HilbertTheoryGenerator theory)
    (formulaEncode : Formula σ → Nat)
    (formulaEncode_injective :
      Function.Injective formulaEncode) :
    HilbertTheoryEnumeration theory where
  certificate_verifier certificate formula :=
    match generator.generate certificate with
    | none => false
    | some candidate =>
        decide
          (formulaEncode candidate =
            formulaEncode formula)
  certificate_sound := by
    intro certificate formula hVerifier
    cases hGenerate :
        generator.generate certificate with
    | none =>
        simp [hGenerate] at hVerifier
    | some candidate =>
        simp only [hGenerate] at hVerifier
        have hCode :
            formulaEncode candidate =
              formulaEncode formula := by
          exact of_decide_eq_true hVerifier
        have hFormula :
            candidate = formula :=
          formulaEncode_injective hCode
        subst formula
        exact generator.generate_sound hGenerate
  certificate_complete := by
    intro formula hTheory
    rcases generator.generate_complete hTheory with
      ⟨certificate, hGenerate⟩
    refine ⟨certificate, ?_⟩
    simp [hGenerate]

end HilbertTheoryGenerator

end ProofCode
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
