import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.SyntaxCoding
import YesMetaZFC.Logic.FirstOrder.Derivation

/-!
# 理论公理的显式证书

证书携带公理分支及其语法参数，不携带待检查的理论成员证明。
`sound` 与 `complete` 保证证书恰好覆盖原理论；`check` 通过可计算的
结构语法相等检查结论，不借助经典可判定性。
本层只处理公理行，尚不声称给出完整证明码的 Delta1 表示。
-/

namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT

open Nonlogical.BasicSetTheory QuineEncoding.SyntaxCoding

set_option autoImplicit false

/-- 原理论公理的显式语法证书族。 -/
structure AxiomPresentation (T : SetTheory) where
  Certificate : Type
  sentence : Certificate → SetSentence
  sound : ∀ certificate, T (sentence certificate)
  complete : ∀ {formula}, T formula → ∃ certificate, sentence certificate = formula

namespace AxiomPresentation

/-- 一条固定公理用唯一证书命名。 -/
def singleton (formula : SetSentence) :
    AxiomPresentation (Theory.singleton formula) where
  Certificate := Unit
  sentence := fun _ => formula
  sound := fun _ => rfl
  complete := by
    intro target hTarget
    exact ⟨(), hTarget.symm⟩

/-- 理论并用带标签的证书和保持两个分支的身份。 -/
def union {T U : SetTheory}
    (left : AxiomPresentation T) (right : AxiomPresentation U) :
    AxiomPresentation (Theory.union T U) where
  Certificate := Sum left.Certificate right.Certificate
  sentence := Sum.elim left.sentence right.sentence
  sound := by
    intro certificate
    cases certificate with
    | inl value => exact Or.inl (left.sound value)
    | inr value => exact Or.inr (right.sound value)
  complete := by
    intro formula hFormula
    cases hFormula with
    | inl hLeft =>
        obtain ⟨certificate, hCertificate⟩ := left.complete hLeft
        exact ⟨.inl certificate, hCertificate⟩
    | inr hRight =>
        obtain ⟨certificate, hCertificate⟩ := right.complete hRight
        exact ⟨.inr certificate, hCertificate⟩

/-- 加入固定公理时同步扩张证书分支。 -/
def insert (formula : SetSentence) {T : SetTheory}
    (presentation : AxiomPresentation T) :
    AxiomPresentation (Theory.insert formula T) :=
  union (singleton formula) presentation

/-- 参数化公理族保留参数及该参数分支的证书。 -/
def indexed {Index : Type} {family : Index → SetTheory}
    (presentations : ∀ index, AxiomPresentation (family index)) :
    AxiomPresentation (fun formula => ∃ index, family index formula) where
  Certificate := (index : Index) × (presentations index).Certificate
  sentence := fun certificate => (presentations certificate.1).sentence certificate.2
  sound := fun certificate =>
    ⟨certificate.1, (presentations certificate.1).sound certificate.2⟩
  complete := by
    rintro formula ⟨index, hFormula⟩
    obtain ⟨certificate, hCertificate⟩ := (presentations index).complete hFormula
    exact ⟨⟨index, certificate⟩, hCertificate⟩

/-- 证书指定的公理与待检查闭句作可计算结构比较。 -/
def check {T : SetTheory} (presentation : AxiomPresentation T)
    (certificate : presentation.Certificate) (formula : SetSentence) : Bool :=
  decide (formula_code (presentation.sentence certificate) = formula_code formula)

@[simp] theorem check_eq_true_iff {T : SetTheory}
    (presentation : AxiomPresentation T)
    (certificate : presentation.Certificate) (formula : SetSentence) :
    presentation.check certificate formula = true ↔
      presentation.sentence certificate = formula := by
  simp only [check, decide_eq_true_eq]
  exact ⟨fun hCode => formula_code_injective hCode,
    fun hFormula => congrArg formula_code hFormula⟩

theorem check_sound {T : SetTheory} (presentation : AxiomPresentation T)
    {certificate : presentation.Certificate} {formula : SetSentence}
    (hChecked : presentation.check certificate formula = true) : T formula := by
  rw [← (presentation.check_eq_true_iff certificate formula).mp hChecked]
  exact presentation.sound certificate

theorem check_complete {T : SetTheory} (presentation : AxiomPresentation T)
    {formula : SetSentence} (hFormula : T formula) :
    ∃ certificate, presentation.check certificate formula = true := by
  obtain ⟨certificate, hCertificate⟩ := presentation.complete hFormula
  exact ⟨certificate, (presentation.check_eq_true_iff certificate formula).mpr hCertificate⟩

/-- 通过公理检查的闭句直接进入既有推导核。 -/
theorem check_derives {T : SetTheory} (presentation : AxiomPresentation T)
    {certificate : presentation.Certificate} {formula : SetSentence}
    (hChecked : presentation.check certificate formula = true) :
    Derives T [] formula := by
  exact Derives.theory_axiom (presentation.check_sound hChecked)

end AxiomPresentation
end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT
