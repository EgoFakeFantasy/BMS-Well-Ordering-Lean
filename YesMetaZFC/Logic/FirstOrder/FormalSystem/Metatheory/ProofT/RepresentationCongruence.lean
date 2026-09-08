import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Delta1ProofPresentation
import YesMetaZFC.Logic.FirstOrder.Derivation.Consistency

/-!
# 正负表示的 quotation 相容性

同一个对象代码不能同时获得接受和拒绝的表示。该必要条件只使用对象理论一致性，
与图的复杂度、检查器的可靠性及完备性无关。旧 `QuineEncoding.quote` 先做 Hilbert 化，
因此原始 AST 的精确相等检查不能直接作为这个 quotation 的正负表示关系。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT
open Nonlogical.BasicSetTheory QuineEncoding
set_option autoImplicit false

/-- 同一 quotation 上的两个不同检查结果不能在一致理论中同时表示。 -/
theorem inconsistent_of_quote_collision
    {T : SetTheory} (condition : FormulaTemplate.Binary)
    {code : Nat} {left right : SetSentence}
    (hQuote : quote left = quote right)
    (hPositive : Derives T [] (condition (finite_numeral_term code) (quote left)))
    (hNegative : Derives T [] (.neg (condition (finite_numeral_term code) (quote right)))) :
    ¬ Derives.Consistent T ([] : Context signature []) := by
  intro hConsistent
  rw [hQuote] at hPositive
  exact hConsistent (Derives.neg_elim hPositive hNegative)

/-- 任意统一 quotation 上的正负表示都必须满足同码同值。 -/
theorem checked_congr_of_representation
    {T : SetTheory} (condition : FormulaTemplate.Binary)
    (quotation : SetSentence → Code) (checked : Nat → SetSentence → Bool)
    (positive : ∀ n φ, checked n φ = true →
      Derives T [] (condition (finite_numeral_term n) (quotation φ)))
    (negative : ∀ n φ, checked n φ = false →
      Derives T [] (.neg (condition (finite_numeral_term n) (quotation φ))))
    (hConsistent : Derives.Consistent T ([] : Context signature []))
    {left right : SetSentence} (hQuote : quotation left = quotation right) (code : Nat) :
    checked code left = checked code right := by
  cases hLeft : checked code left <;> cases hRight : checked code right
  · rfl
  · have hP := positive code right hRight
    have hN := negative code left hLeft
    rw [hQuote] at hN
    exact False.elim (hConsistent (Derives.neg_elim hP hN))
  · have hP := positive code left hLeft
    have hN := negative code right hRight
    rw [hQuote] at hP
    exact False.elim (hConsistent (Derives.neg_elim hP hN))
  · rfl

/-- Hilbert 化不改变旧 `QuineEncoding.quote`；新 `IntrinsicQuotation.quote` 不具此性质。 -/
@[simp] theorem quote_hilbertize (formula : SetSentence) :
    quote (Formula.hilbertize SetSort.set formula) = quote formula := by
  simp only [quote, Formula.hilbertize_idempotent]

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT
