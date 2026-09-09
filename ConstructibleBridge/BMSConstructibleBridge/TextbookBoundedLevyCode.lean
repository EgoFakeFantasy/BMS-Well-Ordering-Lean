import BMSConstructibleBridge.TextbookFormulaCode
import BMSConstructibleBridge.ExternalBoundedLevyHierarchy

/-!
# 真正有界有限 Lévy 层的规范 E 码

`TextbookIsDelta0Code_l` 记录 `Delta0Formula` 的有界量词树；其上的互递归
`Sigma`/`Pi` 码与外部真正有界层级逐项对应。后续对象语言分类器只需验证
有限推导图，不需要枚举固定层的全部公式。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible

/-- `Delta0Formula` 的规范 textbook E 码。 -/
inductive TextbookIsDelta0Code_l : Nat → Nat → Prop where
  | mem {arity : Nat} (left right : Fin arity) :
      TextbookIsDelta0Code_l arity (textbookECode left.1 right.1 0)
  | eq {arity : Nat} (left right : Fin arity) :
      TextbookIsDelta0Code_l arity (textbookECode left.1 right.1 1)
  | neg {arity code : Nat} :
      TextbookIsDelta0Code_l arity code →
        TextbookIsDelta0Code_l arity (textbookECode code 0 2)
  | conj {arity leftCode rightCode : Nat} :
      TextbookIsDelta0Code_l arity leftCode →
      TextbookIsDelta0Code_l arity rightCode →
        TextbookIsDelta0Code_l arity
          (textbookECode leftCode rightCode 3)
  | boundedEx {arity code : Nat} (bound : Fin arity) :
      TextbookIsDelta0Code_l (arity + 1) code →
        TextbookIsDelta0Code_l arity
          (textbookECode
            (textbookECode (textbookECode arity bound.1 0) code 3) 0 4)

mutual
  /-- `code` 是一个 `arity` 元真正有界 `Sigma_level` 公式码。 -/
  inductive TextbookBoundedIsSigmaCode_l : Nat → Nat → Nat → Prop where
    | delta0 {level arity code : Nat} :
        TextbookIsDelta0Code_l arity code →
          TextbookBoundedIsSigmaCode_l level arity code
    | neg {level arity code : Nat} :
        TextbookBoundedIsPiCode_l level arity code →
          TextbookBoundedIsSigmaCode_l level arity
            (textbookECode code 0 2)
    | conj {level arity leftCode rightCode : Nat} :
        TextbookBoundedIsSigmaCode_l level arity leftCode →
        TextbookBoundedIsSigmaCode_l level arity rightCode →
          TextbookBoundedIsSigmaCode_l level arity
            (textbookECode leftCode rightCode 3)
    | ex {level arity code : Nat} :
        TextbookBoundedIsSigmaCode_l level (arity + 1) code →
          TextbookBoundedIsSigmaCode_l level arity
            (textbookECode code 0 4)
    | lift {level arity code : Nat} :
        TextbookBoundedIsSigmaCode_l level arity code →
          TextbookBoundedIsSigmaCode_l (level + 1) arity code
    | ofPi {level arity code : Nat} :
        TextbookBoundedIsPiCode_l level arity code →
          TextbookBoundedIsSigmaCode_l (level + 1) arity code

  /-- `code` 是一个 `arity` 元真正有界 `Pi_level` 公式码。 -/
  inductive TextbookBoundedIsPiCode_l : Nat → Nat → Nat → Prop where
    | delta0 {level arity code : Nat} :
        TextbookIsDelta0Code_l arity code →
          TextbookBoundedIsPiCode_l level arity code
    | neg {level arity code : Nat} :
        TextbookBoundedIsSigmaCode_l level arity code →
          TextbookBoundedIsPiCode_l level arity
            (textbookECode code 0 2)
    | conj {level arity leftCode rightCode : Nat} :
        TextbookBoundedIsPiCode_l level arity leftCode →
        TextbookBoundedIsPiCode_l level arity rightCode →
          TextbookBoundedIsPiCode_l level arity
            (textbookECode leftCode rightCode 3)
    | lift {level arity code : Nat} :
        TextbookBoundedIsPiCode_l level arity code →
          TextbookBoundedIsPiCode_l (level + 1) arity code
    | ofSigma {level arity code : Nat} :
        TextbookBoundedIsSigmaCode_l level arity code →
          TextbookBoundedIsPiCode_l (level + 1) arity code
end

/-- 有界公式编译成 `Delta0` 码证书。 -/
theorem textbookFormulaCode_isDelta0_l
    {arity : Nat} (formula : Delta0Formula arity) :
    TextbookIsDelta0Code_l arity
      (textbookFormulaCode_l formula.toFO) := by
  induction formula with
  | mem left right => exact .mem left right
  | eq left right => exact .eq left right
  | neg body ih => exact .neg ih
  | conj left right ihLeft ihRight => exact .conj ihLeft ihRight
  | @boundedEx arity bound body ih =>
      simpa [Delta0Formula.toFO, FOFormula.boundedEx,
        textbookFormulaCode_l] using TextbookIsDelta0Code_l.boundedEx bound ih

/-- `Delta0` 码证书精确解码回一个有界公式。 -/
theorem TextbookIsDelta0Code_l.decode
    {arity code : Nat} (hCode : TextbookIsDelta0Code_l arity code) :
    ∃ formula : Delta0Formula arity,
      textbookFormulaCode_l formula.toFO = code := by
  induction hCode with
  | mem left right => exact ⟨.mem left right, rfl⟩
  | eq left right => exact ⟨.eq left right, rfl⟩
  | neg hBody ih =>
      rcases ih with ⟨body, rfl⟩
      exact ⟨.neg body, rfl⟩
  | conj hLeft hRight ihLeft ihRight =>
      rcases ihLeft with ⟨left, rfl⟩
      rcases ihRight with ⟨right, rfl⟩
      exact ⟨.conj left right, rfl⟩
  | @boundedEx arity code bound hBody ih =>
      rcases ih with ⟨body, rfl⟩
      refine ⟨.boundedEx bound body, ?_⟩
      simp [Delta0Formula.toFO, FOFormula.boundedEx,
        textbookFormulaCode_l]

/-! 因为两个层级是互递归定义，编译证明必须显式使用共同递归子。 -/

/-- 真正有界 `Sigma` 证书编译成同层、同元数的 E 码证书。 -/
theorem textbookFormulaCode_bounded_isSigma_l
    {arity level : Nat} {formula : FOFormula arity}
    (hFormula : ExternalBoundedIsSigmaFinite_l level formula) :
    TextbookBoundedIsSigmaCode_l level arity
      (textbookFormulaCode_l formula) := by
  exact ExternalBoundedIsSigmaFinite_l.rec
    (motive_1 := fun {arity} level formula _ =>
      TextbookBoundedIsSigmaCode_l level arity
        (textbookFormulaCode_l formula))
    (motive_2 := fun {arity} level formula _ =>
      TextbookBoundedIsPiCode_l level arity
        (textbookFormulaCode_l formula))
    (fun formula => .delta0 (textbookFormulaCode_isDelta0_l formula))
    (fun _ hBody => .neg hBody)
    (fun _ _ hLeft hRight => .conj hLeft hRight)
    (fun _ _ hLeft hRight => by
      simpa [FOFormula.disj, textbookFormulaCode_l] using
        TextbookBoundedIsSigmaCode_l.neg
          (TextbookBoundedIsPiCode_l.conj
            (TextbookBoundedIsPiCode_l.neg hLeft)
            (TextbookBoundedIsPiCode_l.neg hRight)))
    (fun _ _ hLeft hRight => by
      simpa [FOFormula.imp, FOFormula.disj, textbookFormulaCode_l] using
        TextbookBoundedIsSigmaCode_l.neg
          (TextbookBoundedIsPiCode_l.conj
            (TextbookBoundedIsPiCode_l.neg
              (TextbookBoundedIsSigmaCode_l.neg hLeft))
            (TextbookBoundedIsPiCode_l.neg hRight)))
    (fun _ hBody => .ex hBody)
    (fun _ hBody => .lift hBody)
    (fun _ hBody => .ofPi hBody)
    (fun formula => .delta0 (textbookFormulaCode_isDelta0_l formula))
    (fun _ hBody => .neg hBody)
    (fun _ _ hLeft hRight => .conj hLeft hRight)
    (fun _ _ hLeft hRight => by
      simpa [FOFormula.disj, textbookFormulaCode_l] using
        TextbookBoundedIsPiCode_l.neg
          (TextbookBoundedIsSigmaCode_l.conj
            (TextbookBoundedIsSigmaCode_l.neg hLeft)
            (TextbookBoundedIsSigmaCode_l.neg hRight)))
    (fun _ _ hLeft hRight => by
      simpa [FOFormula.imp, FOFormula.disj, textbookFormulaCode_l] using
        TextbookBoundedIsPiCode_l.neg
          (TextbookBoundedIsSigmaCode_l.conj
            (TextbookBoundedIsSigmaCode_l.neg
              (TextbookBoundedIsPiCode_l.neg hLeft))
            (TextbookBoundedIsSigmaCode_l.neg hRight)))
    (fun _ hBody => by
      simpa [FOFormula.all, textbookFormulaCode_l] using
        TextbookBoundedIsPiCode_l.neg
          (TextbookBoundedIsSigmaCode_l.ex
            (TextbookBoundedIsSigmaCode_l.neg hBody)))
    (fun _ hBody => .lift hBody)
    (fun _ hBody => .ofSigma hBody)
    hFormula

/-- 真正有界 `Pi` 证书编译成同层、同元数的 E 码证书。 -/
theorem textbookFormulaCode_bounded_isPi_l
    {arity level : Nat} {formula : FOFormula arity}
    (hFormula : ExternalBoundedIsPiFinite_l level formula) :
    TextbookBoundedIsPiCode_l level arity
      (textbookFormulaCode_l formula) := by
  exact ExternalBoundedIsPiFinite_l.rec
    (motive_1 := fun {arity} level formula _ =>
      TextbookBoundedIsSigmaCode_l level arity
        (textbookFormulaCode_l formula))
    (motive_2 := fun {arity} level formula _ =>
      TextbookBoundedIsPiCode_l level arity
        (textbookFormulaCode_l formula))
    (fun formula => .delta0 (textbookFormulaCode_isDelta0_l formula))
    (fun _ hBody => .neg hBody)
    (fun _ _ hLeft hRight => .conj hLeft hRight)
    (fun _ _ hLeft hRight => by
      simpa [FOFormula.disj, textbookFormulaCode_l] using
        TextbookBoundedIsSigmaCode_l.neg
          (TextbookBoundedIsPiCode_l.conj
            (TextbookBoundedIsPiCode_l.neg hLeft)
            (TextbookBoundedIsPiCode_l.neg hRight)))
    (fun _ _ hLeft hRight => by
      simpa [FOFormula.imp, FOFormula.disj, textbookFormulaCode_l] using
        TextbookBoundedIsSigmaCode_l.neg
          (TextbookBoundedIsPiCode_l.conj
            (TextbookBoundedIsPiCode_l.neg
              (TextbookBoundedIsSigmaCode_l.neg hLeft))
            (TextbookBoundedIsPiCode_l.neg hRight)))
    (fun _ hBody => .ex hBody)
    (fun _ hBody => .lift hBody)
    (fun _ hBody => .ofPi hBody)
    (fun formula => .delta0 (textbookFormulaCode_isDelta0_l formula))
    (fun _ hBody => .neg hBody)
    (fun _ _ hLeft hRight => .conj hLeft hRight)
    (fun _ _ hLeft hRight => by
      simpa [FOFormula.disj, textbookFormulaCode_l] using
        TextbookBoundedIsPiCode_l.neg
          (TextbookBoundedIsSigmaCode_l.conj
            (TextbookBoundedIsSigmaCode_l.neg hLeft)
            (TextbookBoundedIsSigmaCode_l.neg hRight)))
    (fun _ _ hLeft hRight => by
      simpa [FOFormula.imp, FOFormula.disj, textbookFormulaCode_l] using
        TextbookBoundedIsPiCode_l.neg
          (TextbookBoundedIsSigmaCode_l.conj
            (TextbookBoundedIsSigmaCode_l.neg
              (TextbookBoundedIsPiCode_l.neg hLeft))
            (TextbookBoundedIsSigmaCode_l.neg hRight)))
    (fun _ hBody => by
      simpa [FOFormula.all, textbookFormulaCode_l] using
        TextbookBoundedIsPiCode_l.neg
          (TextbookBoundedIsSigmaCode_l.ex
            (TextbookBoundedIsSigmaCode_l.neg hBody)))
    (fun _ hBody => .lift hBody)
    (fun _ hBody => .ofSigma hBody)
    hFormula

/-! 解码同样由共同递归子一次生成两个极性分支。 -/

/-- 有界 `Sigma` 码解码回一个同层外部公式。 -/
theorem TextbookBoundedIsSigmaCode_l.decode
    {level arity code : Nat}
    (hCode : TextbookBoundedIsSigmaCode_l level arity code) :
    ∃ formula : FOFormula arity,
      textbookFormulaCode_l formula = code ∧
        ExternalBoundedIsSigmaFinite_l level formula := by
  exact TextbookBoundedIsSigmaCode_l.rec
    (motive_1 := fun level arity code _ =>
      ∃ formula : FOFormula arity,
        textbookFormulaCode_l formula = code ∧
          ExternalBoundedIsSigmaFinite_l level formula)
    (motive_2 := fun level arity code _ =>
      ∃ formula : FOFormula arity,
        textbookFormulaCode_l formula = code ∧
          ExternalBoundedIsPiFinite_l level formula)
    (fun hDelta => by
      rcases hDelta.decode with ⟨formula, rfl⟩
      exact ⟨formula.toFO, rfl, .delta0 formula⟩)
    (fun _ ⟨body, hBody, hPi⟩ =>
      ⟨.neg body, by simp [textbookFormulaCode_l, hBody], .neg hPi⟩)
    (fun _ _ ⟨left, hLeft, hLeftSigma⟩
        ⟨right, hRight, hRightSigma⟩ =>
      ⟨.conj left right,
        by simp [textbookFormulaCode_l, hLeft, hRight],
        .conj hLeftSigma hRightSigma⟩)
    (fun _ ⟨body, hBody, hSigma⟩ =>
      ⟨.ex body, by simp [textbookFormulaCode_l, hBody], .ex hSigma⟩)
    (fun _ ⟨body, hBody, hSigma⟩ =>
      ⟨body, hBody, .lift hSigma⟩)
    (fun _ ⟨body, hBody, hPi⟩ =>
      ⟨body, hBody, .ofPi hPi⟩)
    (fun hDelta => by
      rcases hDelta.decode with ⟨formula, rfl⟩
      exact ⟨formula.toFO, rfl, .delta0 formula⟩)
    (fun _ ⟨body, hBody, hSigma⟩ =>
      ⟨.neg body, by simp [textbookFormulaCode_l, hBody], .neg hSigma⟩)
    (fun _ _ ⟨left, hLeft, hLeftPi⟩
        ⟨right, hRight, hRightPi⟩ =>
      ⟨.conj left right,
        by simp [textbookFormulaCode_l, hLeft, hRight],
        .conj hLeftPi hRightPi⟩)
    (fun _ ⟨body, hBody, hPi⟩ =>
      ⟨body, hBody, .lift hPi⟩)
    (fun _ ⟨body, hBody, hSigma⟩ =>
      ⟨body, hBody, .ofSigma hSigma⟩)
    hCode

/-- 有界 `Pi` 码解码回一个同层外部公式。 -/
theorem TextbookBoundedIsPiCode_l.decode
    {level arity code : Nat}
    (hCode : TextbookBoundedIsPiCode_l level arity code) :
    ∃ formula : FOFormula arity,
      textbookFormulaCode_l formula = code ∧
        ExternalBoundedIsPiFinite_l level formula := by
  exact TextbookBoundedIsPiCode_l.rec
    (motive_1 := fun level arity code _ =>
      ∃ formula : FOFormula arity,
        textbookFormulaCode_l formula = code ∧
          ExternalBoundedIsSigmaFinite_l level formula)
    (motive_2 := fun level arity code _ =>
      ∃ formula : FOFormula arity,
        textbookFormulaCode_l formula = code ∧
          ExternalBoundedIsPiFinite_l level formula)
    (fun hDelta => by
      rcases hDelta.decode with ⟨formula, rfl⟩
      exact ⟨formula.toFO, rfl, .delta0 formula⟩)
    (fun _ ⟨body, hBody, hPi⟩ =>
      ⟨.neg body, by simp [textbookFormulaCode_l, hBody], .neg hPi⟩)
    (fun _ _ ⟨left, hLeft, hLeftSigma⟩
        ⟨right, hRight, hRightSigma⟩ =>
      ⟨.conj left right,
        by simp [textbookFormulaCode_l, hLeft, hRight],
        .conj hLeftSigma hRightSigma⟩)
    (fun _ ⟨body, hBody, hSigma⟩ =>
      ⟨.ex body, by simp [textbookFormulaCode_l, hBody], .ex hSigma⟩)
    (fun _ ⟨body, hBody, hSigma⟩ =>
      ⟨body, hBody, .lift hSigma⟩)
    (fun _ ⟨body, hBody, hPi⟩ =>
      ⟨body, hBody, .ofPi hPi⟩)
    (fun hDelta => by
      rcases hDelta.decode with ⟨formula, rfl⟩
      exact ⟨formula.toFO, rfl, .delta0 formula⟩)
    (fun _ ⟨body, hBody, hSigma⟩ =>
      ⟨.neg body, by simp [textbookFormulaCode_l, hBody], .neg hSigma⟩)
    (fun _ _ ⟨left, hLeft, hLeftPi⟩
        ⟨right, hRight, hRightPi⟩ =>
      ⟨.conj left right,
        by simp [textbookFormulaCode_l, hLeft, hRight],
        .conj hLeftPi hRightPi⟩)
    (fun _ ⟨body, hBody, hPi⟩ =>
      ⟨body, hBody, .lift hPi⟩)
    (fun _ ⟨body, hBody, hSigma⟩ =>
      ⟨body, hBody, .ofSigma hSigma⟩)
    hCode

/-- 有界 `Sigma` 码与相应外部公式的存在性精确等价。 -/
theorem textbookBoundedIsSigmaCode_iff_l
    {level arity code : Nat} :
    TextbookBoundedIsSigmaCode_l level arity code ↔
      ∃ formula : FOFormula arity,
        textbookFormulaCode_l formula = code ∧
          ExternalBoundedIsSigmaFinite_l level formula := by
  constructor
  · exact TextbookBoundedIsSigmaCode_l.decode
  · rintro ⟨formula, rfl, hFormula⟩
    exact textbookFormulaCode_bounded_isSigma_l hFormula

/-- 有界 `Pi` 码与相应外部公式的存在性精确等价。 -/
theorem textbookBoundedIsPiCode_iff_l
    {level arity code : Nat} :
    TextbookBoundedIsPiCode_l level arity code ↔
      ∃ formula : FOFormula arity,
        textbookFormulaCode_l formula = code ∧
          ExternalBoundedIsPiFinite_l level formula := by
  constructor
  · exact TextbookBoundedIsPiCode_l.decode
  · rintro ⟨formula, rfl, hFormula⟩
    exact textbookFormulaCode_bounded_isPi_l hFormula

end YesMetaZFC.BMS.ConstructibleBridge
