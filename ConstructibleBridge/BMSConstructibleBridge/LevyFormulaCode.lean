import BMSConstructibleBridge.ExternalLevyHierarchy
import ConstructibleUniverse.SetTheory.ZFC.Constructible.FormulaSyntaxCode

/-!
# 外部公式码的有限 Lévy 规格

本模块把结构公式证书降到 `FormulaSyntaxCode` 的自然数 Gödel 码。这里给出的
仍是 Lean 中的精确规格；下一层对象语言分类器必须表示这些谓词，而不能改用
textbook `E` 的构造深度。编码器的左逆定理保证有效公式码不会混淆。
-/

namespace YesMetaZFC
namespace BMS
namespace ConstructibleBridge

open Constructible

/-- 固定元数的公式码解码为一个外部 `Sigma_level` 公式。 -/
def externalSigmaCodeAt_l (level arity code : Nat) : Prop :=
  exists formula : FOFormula arity,
    FOFormulaCode.formulaNatDecode arity code = some formula /\
      ExternalIsSigmaFinite level formula

/-- 固定元数的公式码解码为一个外部 `Pi_level` 公式。 -/
def externalPiCodeAt_l (level arity code : Nat) : Prop :=
  exists formula : FOFormula arity,
    FOFormulaCode.formulaNatDecode arity code = some formula /\
      ExternalIsPiFinite level formula

/-- 在规范 Gödel 码处，`Sigma` 码规格精确退化为结构证书。 -/
theorem formulaNatCode_externalSigma_iff_l
    {arity level : Nat} (formula : FOFormula arity) :
    externalSigmaCodeAt_l level arity
        (FOFormulaCode.formulaNatCode formula) <->
      ExternalIsSigmaFinite level formula := by
  constructor
  · rintro ⟨decoded, hDecode, hDecoded⟩
    have hFormula : decoded = formula := by
      simpa using hDecode.symm
    simpa [hFormula] using hDecoded
  · intro hFormula
    exact ⟨formula, FOFormulaCode.formulaNatDecode_formulaNatCode formula,
      hFormula⟩

/-- 在规范 Gödel 码处，`Pi` 码规格精确退化为结构证书。 -/
theorem formulaNatCode_externalPi_iff_l
    {arity level : Nat} (formula : FOFormula arity) :
    externalPiCodeAt_l level arity
        (FOFormulaCode.formulaNatCode formula) <->
      ExternalIsPiFinite level formula := by
  constructor
  · rintro ⟨decoded, hDecode, hDecoded⟩
    have hFormula : decoded = formula := by
      simpa using hDecode.symm
    simpa [hFormula] using hDecoded
  · intro hFormula
    exact ⟨formula, FOFormulaCode.formulaNatDecode_formulaNatCode formula,
      hFormula⟩

/-- 每个规范外部公式码都在某个有限层同时满足两个极性规格。 -/
theorem exists_formulaNatCode_finiteLevyLevel_l
    {arity : Nat} (formula : FOFormula arity) :
    exists level,
      externalSigmaCodeAt_l level arity
          (FOFormulaCode.formulaNatCode formula) /\
      externalPiCodeAt_l level arity
          (FOFormulaCode.formulaNatCode formula) := by
  rcases exists_externalFiniteLevyLevel_l formula with
    ⟨level, hSigma, hPi⟩
  exact ⟨level,
    (formulaNatCode_externalSigma_iff_l formula).mpr hSigma,
    (formulaNatCode_externalPi_iff_l formula).mpr hPi⟩

end ConstructibleBridge
end BMS
end YesMetaZFC
