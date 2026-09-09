import BMSConstructibleBridge.TextbookFormulaCode

/-!
# Textbook E 公式码的有限 Lévy 证书

这些证书直接作用于 `E` 使用的自然数码，并保留公式元数。原子分支携带
`Fin arity`，存在量词分支把子公式元数提升一，因此不合法的自由变量码不会
混入反射范围。证书规则与外部结构公式的有限 `Sigma` / `Pi` 规则逐项同构。
-/

namespace YesMetaZFC
namespace BMS
namespace ConstructibleBridge

open Constructible

mutual
  /-- 自然数 `code` 是一个 `arity` 元外部 `Sigma_level` 公式的规范 E 码。 -/
  inductive TextbookIsSigmaCode : Nat -> Nat -> Nat -> Prop where
    | mem {level arity : Nat} (left right : Fin arity) :
        TextbookIsSigmaCode level arity
          (textbookECode left.1 right.1 0)
    | eq {level arity : Nat} (left right : Fin arity) :
        TextbookIsSigmaCode level arity
          (textbookECode left.1 right.1 1)
    | neg {level arity code : Nat} :
        TextbookIsPiCode level arity code ->
          TextbookIsSigmaCode level arity (textbookECode code 0 2)
    | conj {level arity leftCode rightCode : Nat} :
        TextbookIsSigmaCode level arity leftCode ->
        TextbookIsSigmaCode level arity rightCode ->
          TextbookIsSigmaCode level arity
            (textbookECode leftCode rightCode 3)
    | ex {level arity code : Nat} :
        TextbookIsSigmaCode level (arity + 1) code ->
          TextbookIsSigmaCode level arity (textbookECode code 0 4)
    | lift {level arity code : Nat} :
        TextbookIsSigmaCode level arity code ->
          TextbookIsSigmaCode (level + 1) arity code
    | ofPi {level arity code : Nat} :
        TextbookIsPiCode level arity code ->
          TextbookIsSigmaCode (level + 1) arity code

  /-- 自然数 `code` 是一个 `arity` 元外部 `Pi_level` 公式的规范 E 码。 -/
  inductive TextbookIsPiCode : Nat -> Nat -> Nat -> Prop where
    | mem {level arity : Nat} (left right : Fin arity) :
        TextbookIsPiCode level arity
          (textbookECode left.1 right.1 0)
    | eq {level arity : Nat} (left right : Fin arity) :
        TextbookIsPiCode level arity
          (textbookECode left.1 right.1 1)
    | neg {level arity code : Nat} :
        TextbookIsSigmaCode level arity code ->
          TextbookIsPiCode level arity (textbookECode code 0 2)
    | conj {level arity leftCode rightCode : Nat} :
        TextbookIsPiCode level arity leftCode ->
        TextbookIsPiCode level arity rightCode ->
          TextbookIsPiCode level arity
            (textbookECode leftCode rightCode 3)
    | lift {level arity code : Nat} :
        TextbookIsPiCode level arity code ->
          TextbookIsPiCode (level + 1) arity code
    | ofSigma {level arity code : Nat} :
        TextbookIsSigmaCode level arity code ->
          TextbookIsPiCode (level + 1) arity code
end

/-- 外部 `Sigma` 证书编译成同层、同元数的 E 码证书。 -/
theorem textbookFormulaCode_isSigma_l
    {arity level : Nat} {formula : FOFormula arity}
    (hFormula : ExternalIsSigmaFinite level formula) :
    TextbookIsSigmaCode level arity (textbookFormulaCode_l formula) := by
  exact ExternalIsSigmaFinite.rec
    (motive_1 := fun level formula _ =>
      TextbookIsSigmaCode level _ (textbookFormulaCode_l formula))
    (motive_2 := fun level formula _ =>
      TextbookIsPiCode level _ (textbookFormulaCode_l formula))
    (fun left right => .mem left right)
    (fun left right => .eq left right)
    (fun _ hBody => .neg hBody)
    (fun _ _ hLeft hRight => .conj hLeft hRight)
    (fun _ hBody => .ex hBody)
    (fun _ hBody => .lift hBody)
    (fun _ hBody => .ofPi hBody)
    (fun left right => .mem left right)
    (fun left right => .eq left right)
    (fun _ hBody => .neg hBody)
    (fun _ _ hLeft hRight => .conj hLeft hRight)
    (fun _ hBody => .lift hBody)
    (fun _ hBody => .ofSigma hBody)
    hFormula

/-- 外部 `Pi` 证书编译成同层、同元数的 E 码证书。 -/
theorem textbookFormulaCode_isPi_l
    {arity level : Nat} {formula : FOFormula arity}
    (hFormula : ExternalIsPiFinite level formula) :
    TextbookIsPiCode level arity (textbookFormulaCode_l formula) := by
  exact ExternalIsPiFinite.rec
    (motive_1 := fun level formula _ =>
      TextbookIsSigmaCode level _ (textbookFormulaCode_l formula))
    (motive_2 := fun level formula _ =>
      TextbookIsPiCode level _ (textbookFormulaCode_l formula))
    (fun left right => .mem left right)
    (fun left right => .eq left right)
    (fun _ hBody => .neg hBody)
    (fun _ _ hLeft hRight => .conj hLeft hRight)
    (fun _ hBody => .ex hBody)
    (fun _ hBody => .lift hBody)
    (fun _ hBody => .ofPi hBody)
    (fun left right => .mem left right)
    (fun left right => .eq left right)
    (fun _ hBody => .neg hBody)
    (fun _ _ hLeft hRight => .conj hLeft hRight)
    (fun _ hBody => .lift hBody)
    (fun _ hBody => .ofSigma hBody)
    hFormula

/-- 每个外部公式的规范 E 码在某一有限层同时具有两个极性证书。 -/
theorem exists_textbookFormulaCode_finiteLevyLevel_l
    {arity : Nat} (formula : FOFormula arity) :
    exists level,
      TextbookIsSigmaCode level arity (textbookFormulaCode_l formula) /\
      TextbookIsPiCode level arity (textbookFormulaCode_l formula) := by
  rcases exists_externalFiniteLevyLevel_l formula with
    ⟨level, hSigma, hPi⟩
  exact ⟨level, textbookFormulaCode_isSigma_l hSigma,
    textbookFormulaCode_isPi_l hPi⟩

/-- 每个 `Sigma` E 码证书都带有一个正确解码公式。 -/
theorem TextbookIsSigmaCode.decode_l
    {level arity code : Nat}
    (hCode : TextbookIsSigmaCode level arity code) :
    exists formula : FOFormula arity,
      textbookFormulaCode_l formula = code /\
        ExternalIsSigmaFinite level formula := by
  exact TextbookIsSigmaCode.rec
    (motive_1 := fun level arity code _ =>
      exists formula : FOFormula arity,
        textbookFormulaCode_l formula = code /\
          ExternalIsSigmaFinite level formula)
    (motive_2 := fun level arity code _ =>
      exists formula : FOFormula arity,
        textbookFormulaCode_l formula = code /\
          ExternalIsPiFinite level formula)
    (fun left right =>
      ⟨.mem left right, rfl, .mem left right⟩)
    (fun left right =>
      ⟨.eq left right, rfl, .eq left right⟩)
    (fun _ ⟨formula, hFormula, hPi⟩ =>
      ⟨.neg formula, by simp [textbookFormulaCode_l, hFormula], .neg hPi⟩)
    (fun _ _ ⟨left, hLeft, hLeftSigma⟩
        ⟨right, hRight, hRightSigma⟩ =>
      ⟨.conj left right,
        by simp [textbookFormulaCode_l, hLeft, hRight],
        .conj hLeftSigma hRightSigma⟩)
    (fun _ ⟨formula, hFormula, hSigma⟩ =>
      ⟨.ex formula, by simp [textbookFormulaCode_l, hFormula], .ex hSigma⟩)
    (fun _ ⟨formula, hFormula, hSigma⟩ =>
      ⟨formula, hFormula, .lift hSigma⟩)
    (fun _ ⟨formula, hFormula, hPi⟩ =>
      ⟨formula, hFormula, .ofPi hPi⟩)
    (fun left right =>
      ⟨.mem left right, rfl, .mem left right⟩)
    (fun left right =>
      ⟨.eq left right, rfl, .eq left right⟩)
    (fun _ ⟨formula, hFormula, hSigma⟩ =>
      ⟨.neg formula, by simp [textbookFormulaCode_l, hFormula],
        .neg hSigma⟩)
    (fun _ _ ⟨left, hLeft, hLeftPi⟩
        ⟨right, hRight, hRightPi⟩ =>
      ⟨.conj left right,
        by simp [textbookFormulaCode_l, hLeft, hRight],
        .conj hLeftPi hRightPi⟩)
    (fun _ ⟨formula, hFormula, hPi⟩ =>
      ⟨formula, hFormula, .lift hPi⟩)
    (fun _ ⟨formula, hFormula, hSigma⟩ =>
      ⟨formula, hFormula, .ofSigma hSigma⟩)
    hCode

/-- 每个 `Pi` E 码证书都带有一个正确解码公式。 -/
theorem TextbookIsPiCode.decode_l
    {level arity code : Nat}
    (hCode : TextbookIsPiCode level arity code) :
    exists formula : FOFormula arity,
      textbookFormulaCode_l formula = code /\
        ExternalIsPiFinite level formula := by
  exact TextbookIsPiCode.rec
    (motive_1 := fun level arity code _ =>
      exists formula : FOFormula arity,
        textbookFormulaCode_l formula = code /\
          ExternalIsSigmaFinite level formula)
    (motive_2 := fun level arity code _ =>
      exists formula : FOFormula arity,
        textbookFormulaCode_l formula = code /\
          ExternalIsPiFinite level formula)
    (fun left right =>
      ⟨.mem left right, rfl, .mem left right⟩)
    (fun left right =>
      ⟨.eq left right, rfl, .eq left right⟩)
    (fun _ ⟨formula, hFormula, hPi⟩ =>
      ⟨.neg formula, by simp [textbookFormulaCode_l, hFormula], .neg hPi⟩)
    (fun _ _ ⟨left, hLeft, hLeftSigma⟩
        ⟨right, hRight, hRightSigma⟩ =>
      ⟨.conj left right,
        by simp [textbookFormulaCode_l, hLeft, hRight],
        .conj hLeftSigma hRightSigma⟩)
    (fun _ ⟨formula, hFormula, hSigma⟩ =>
      ⟨.ex formula, by simp [textbookFormulaCode_l, hFormula], .ex hSigma⟩)
    (fun _ ⟨formula, hFormula, hSigma⟩ =>
      ⟨formula, hFormula, .lift hSigma⟩)
    (fun _ ⟨formula, hFormula, hPi⟩ =>
      ⟨formula, hFormula, .ofPi hPi⟩)
    (fun left right =>
      ⟨.mem left right, rfl, .mem left right⟩)
    (fun left right =>
      ⟨.eq left right, rfl, .eq left right⟩)
    (fun _ ⟨formula, hFormula, hSigma⟩ =>
      ⟨.neg formula, by simp [textbookFormulaCode_l, hFormula],
        .neg hSigma⟩)
    (fun _ _ ⟨left, hLeft, hLeftPi⟩
        ⟨right, hRight, hRightPi⟩ =>
      ⟨.conj left right,
        by simp [textbookFormulaCode_l, hLeft, hRight],
        .conj hLeftPi hRightPi⟩)
    (fun _ ⟨formula, hFormula, hPi⟩ =>
      ⟨formula, hFormula, .lift hPi⟩)
    (fun _ ⟨formula, hFormula, hSigma⟩ =>
      ⟨formula, hFormula, .ofSigma hSigma⟩)
    hCode

/-- `Sigma` E 码证书精确等价于某个已分类结构公式的编译像。 -/
theorem textbookIsSigmaCode_iff_l
    {level arity code : Nat} :
    TextbookIsSigmaCode level arity code <->
      exists formula : FOFormula arity,
        textbookFormulaCode_l formula = code /\
          ExternalIsSigmaFinite level formula := by
  constructor
  · intro hCode
    exact hCode.decode_l
  · rintro ⟨formula, rfl, hFormula⟩
    exact textbookFormulaCode_isSigma_l hFormula

/-- `Pi` E 码证书精确等价于某个已分类结构公式的编译像。 -/
theorem textbookIsPiCode_iff_l
    {level arity code : Nat} :
    TextbookIsPiCode level arity code <->
      exists formula : FOFormula arity,
        textbookFormulaCode_l formula = code /\
          ExternalIsPiFinite level formula := by
  constructor
  · intro hCode
    exact hCode.decode_l
  · rintro ⟨formula, rfl, hFormula⟩
    exact textbookFormulaCode_isPi_l hFormula

end ConstructibleBridge
end BMS
end YesMetaZFC
