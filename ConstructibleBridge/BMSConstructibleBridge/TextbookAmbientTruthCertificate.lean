import BMSConstructibleBridge.TextbookAmbientDelta0TruthFormula
import BMSConstructibleBridge.TextbookBoundedLevyCode

/-!
# 固定有限 Levy 层的 ambient 真值证书

本文件先在 Lean 元语义中隔离部分真谓词的归纳核心。`Sigma` 侧证书表示公式为真，
`Pi` 侧证书表示公式为假；同层的否定、合取和存在量词形成有限归纳树，只有层级
提升叶才调用严格低一层的证书。后续对象化只需把这棵有限树编码成成员语言记录。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible
open Constructible.FiniteSequenceZF

/-- 可构造层载体上的原始成员关系。 -/
abbrev stageMembership_l (top : Ordinal.{u}) :
    StageCarrier top → StageCarrier top → Prop :=
  fun left right => left.1 ∈ right.1

/--
同一归纳族中的 `mode = true` 表示 `Sigma` 真，`mode = false` 表示 `Pi` 假。
合并两个极性后，跨极性的否定仍是结构递减，可靠性证明可直接作普通归纳。
-/
inductive TextbookAmbientCertificateStep_l
    (top : Ordinal.{u}) (currentLevel lowerLevel : Nat)
    (hasLower : Prop)
    (lowerSigma : {arity : Nat} → Nat → Tuple (StageCarrier top) arity → Prop)
    (lowerPiFalse : {arity : Nat} → Nat → Tuple (StageCarrier top) arity → Prop) :
    Bool → {arity : Nat} → Nat → Tuple (StageCarrier top) arity → Prop where
  | deltaSigma {arity : Nat} (formula : Delta0Formula arity)
      (assignment : Tuple (StageCarrier top) arity)
      (hFormula : FOFormula.Satisfies (stageMembership_l top)
        formula.toFO assignment) :
      TextbookAmbientCertificateStep_l top currentLevel lowerLevel hasLower
        lowerSigma lowerPiFalse true (textbookFormulaCode_l formula.toFO) assignment
  | deltaPiFalse {arity : Nat} (formula : Delta0Formula arity)
      (assignment : Tuple (StageCarrier top) arity)
      (hFormula : ¬ FOFormula.Satisfies (stageMembership_l top)
        formula.toFO assignment) :
      TextbookAmbientCertificateStep_l top currentLevel lowerLevel hasLower
        lowerSigma lowerPiFalse false (textbookFormulaCode_l formula.toFO) assignment
  | negSigma {arity code : Nat} {assignment : Tuple (StageCarrier top) arity} :
      TextbookAmbientCertificateStep_l top currentLevel lowerLevel hasLower
          lowerSigma lowerPiFalse false code assignment →
        TextbookAmbientCertificateStep_l top currentLevel lowerLevel hasLower
          lowerSigma lowerPiFalse true (textbookECode code 0 2) assignment
  | negPiFalse {arity code : Nat} {assignment : Tuple (StageCarrier top) arity} :
      TextbookAmbientCertificateStep_l top currentLevel lowerLevel hasLower
          lowerSigma lowerPiFalse true code assignment →
        TextbookAmbientCertificateStep_l top currentLevel lowerLevel hasLower
          lowerSigma lowerPiFalse false (textbookECode code 0 2) assignment
  | conjSigma {arity leftCode rightCode : Nat}
      {assignment : Tuple (StageCarrier top) arity} :
      TextbookAmbientCertificateStep_l top currentLevel lowerLevel hasLower
          lowerSigma lowerPiFalse true leftCode assignment →
      TextbookAmbientCertificateStep_l top currentLevel lowerLevel hasLower
          lowerSigma lowerPiFalse true rightCode assignment →
        TextbookAmbientCertificateStep_l top currentLevel lowerLevel hasLower
          lowerSigma lowerPiFalse true
          (textbookECode leftCode rightCode 3) assignment
  | conjPiFalseLeft {arity leftCode rightCode : Nat}
      {assignment : Tuple (StageCarrier top) arity} :
      TextbookAmbientCertificateStep_l top currentLevel lowerLevel hasLower
          lowerSigma lowerPiFalse false leftCode assignment →
      TextbookBoundedIsPiCode_l currentLevel arity rightCode →
        TextbookAmbientCertificateStep_l top currentLevel lowerLevel hasLower
          lowerSigma lowerPiFalse false
          (textbookECode leftCode rightCode 3) assignment
  | conjPiFalseRight {arity leftCode rightCode : Nat}
      {assignment : Tuple (StageCarrier top) arity} :
      TextbookBoundedIsPiCode_l currentLevel arity leftCode →
      TextbookAmbientCertificateStep_l top currentLevel lowerLevel hasLower
          lowerSigma lowerPiFalse false rightCode assignment →
        TextbookAmbientCertificateStep_l top currentLevel lowerLevel hasLower
          lowerSigma lowerPiFalse false
          (textbookECode leftCode rightCode 3) assignment
  | exSigma {arity code : Nat} {assignment : Tuple (StageCarrier top) arity}
      (witness : StageCarrier top) :
      TextbookAmbientCertificateStep_l top currentLevel lowerLevel hasLower
          lowerSigma lowerPiFalse true code (snoc assignment witness) →
        TextbookAmbientCertificateStep_l top currentLevel lowerLevel hasLower
          lowerSigma lowerPiFalse true (textbookECode code 0 4) assignment
  | lowerSigmaTruth {arity code : Nat}
      {assignment : Tuple (StageCarrier top) arity} :
      hasLower → TextbookBoundedIsSigmaCode_l lowerLevel arity code →
      lowerSigma code assignment →
        TextbookAmbientCertificateStep_l top currentLevel lowerLevel hasLower
          lowerSigma lowerPiFalse true code assignment
  | lowerPiTruth {arity code : Nat}
      {assignment : Tuple (StageCarrier top) arity} :
      hasLower → TextbookBoundedIsPiCode_l lowerLevel arity code →
      (¬ lowerPiFalse code assignment) →
        TextbookAmbientCertificateStep_l top currentLevel lowerLevel hasLower
          lowerSigma lowerPiFalse true code assignment
  | lowerPiFalse {arity code : Nat}
      {assignment : Tuple (StageCarrier top) arity} :
      hasLower → TextbookBoundedIsPiCode_l lowerLevel arity code →
      lowerPiFalse code assignment →
        TextbookAmbientCertificateStep_l top currentLevel lowerLevel hasLower
          lowerSigma lowerPiFalse false code assignment
  | lowerSigmaFalse {arity code : Nat}
      {assignment : Tuple (StageCarrier top) arity} :
      hasLower → TextbookBoundedIsSigmaCode_l lowerLevel arity code →
      (¬ lowerSigma code assignment) →
        TextbookAmbientCertificateStep_l top currentLevel lowerLevel hasLower
          lowerSigma lowerPiFalse false code assignment

abbrev TextbookAmbientSigmaCertificateStep_l
    (top : Ordinal.{u}) (currentLevel lowerLevel : Nat) (hasLower : Prop)
    (lowerSigma : {arity : Nat} → Nat → Tuple (StageCarrier top) arity → Prop)
    (lowerPiFalse : {arity : Nat} → Nat → Tuple (StageCarrier top) arity → Prop) :
    {arity : Nat} → Nat → Tuple (StageCarrier top) arity → Prop :=
  TextbookAmbientCertificateStep_l top currentLevel lowerLevel hasLower
    lowerSigma lowerPiFalse true

abbrev TextbookAmbientPiFalseCertificateStep_l
    (top : Ordinal.{u}) (currentLevel lowerLevel : Nat) (hasLower : Prop)
    (lowerSigma : {arity : Nat} → Nat → Tuple (StageCarrier top) arity → Prop)
    (lowerPiFalse : {arity : Nat} → Nat → Tuple (StageCarrier top) arity → Prop) :
    {arity : Nat} → Nat → Tuple (StageCarrier top) arity → Prop :=
  TextbookAmbientCertificateStep_l top currentLevel lowerLevel hasLower
    lowerSigma lowerPiFalse false

mutual
  /-- `Sigma_level` 码在当前层赋值下为真的规范有限证书命题。 -/
  noncomputable def TextbookAmbientSigmaCertificate_l
      (top : Ordinal.{u}) :
      (level : Nat) → {arity : Nat} → Nat → Tuple (StageCarrier top) arity → Prop
    | 0, _, code, assignment =>
        TextbookAmbientSigmaCertificateStep_l top 0 0 False
          (fun _ _ => False) (fun _ _ => False) code assignment
    | level + 1, _, code, assignment =>
        TextbookAmbientSigmaCertificateStep_l top (level + 1) level True
          (TextbookAmbientSigmaCertificate_l top level)
          (TextbookAmbientPiFalseCertificate_l top level) code assignment

  /-- `Pi_level` 码在当前层赋值下为假的规范有限证书命题。 -/
  noncomputable def TextbookAmbientPiFalseCertificate_l
      (top : Ordinal.{u}) :
      (level : Nat) → {arity : Nat} → Nat → Tuple (StageCarrier top) arity → Prop
    | 0, _, code, assignment =>
        TextbookAmbientPiFalseCertificateStep_l top 0 0 False
          (fun _ _ => False) (fun _ _ => False) code assignment
    | level + 1, _, code, assignment =>
        TextbookAmbientPiFalseCertificateStep_l top (level + 1) level True
          (TextbookAmbientSigmaCertificate_l top level)
          (TextbookAmbientPiFalseCertificate_l top level) code assignment
end

/-!
The following wrappers deliberately expose the outer recursion on `level`.
They keep later mutual-recursion proofs independent of reducibility heuristics.
-/

theorem textbookAmbientSigmaCertificate_delta_l
    {top : Ordinal.{u}} (level : Nat) {arity : Nat}
    (formula : Delta0Formula arity)
    (assignment : Tuple (StageCarrier top) arity)
    (hFormula : FOFormula.Satisfies (stageMembership_l top)
      formula.toFO assignment) :
    TextbookAmbientSigmaCertificate_l top level
      (textbookFormulaCode_l formula.toFO) assignment := by
  cases level <;>
    exact TextbookAmbientCertificateStep_l.deltaSigma formula assignment hFormula

theorem textbookAmbientPiFalseCertificate_delta_l
    {top : Ordinal.{u}} (level : Nat) {arity : Nat}
    (formula : Delta0Formula arity)
    (assignment : Tuple (StageCarrier top) arity)
    (hFormula : ¬ FOFormula.Satisfies (stageMembership_l top)
      formula.toFO assignment) :
    TextbookAmbientPiFalseCertificate_l top level
      (textbookFormulaCode_l formula.toFO) assignment := by
  cases level <;>
    exact TextbookAmbientCertificateStep_l.deltaPiFalse formula assignment hFormula

theorem textbookAmbientSigmaCertificate_neg_l
    {top : Ordinal.{u}} (level : Nat) {arity code : Nat}
    {assignment : Tuple (StageCarrier top) arity}
    (hBody : TextbookAmbientPiFalseCertificate_l top level code assignment) :
    TextbookAmbientSigmaCertificate_l top level
      (textbookECode code 0 2) assignment := by
  cases level <;>
    exact TextbookAmbientCertificateStep_l.negSigma hBody

theorem textbookAmbientPiFalseCertificate_neg_l
    {top : Ordinal.{u}} (level : Nat) {arity code : Nat}
    {assignment : Tuple (StageCarrier top) arity}
    (hBody : TextbookAmbientSigmaCertificate_l top level code assignment) :
    TextbookAmbientPiFalseCertificate_l top level
      (textbookECode code 0 2) assignment := by
  cases level <;>
    exact TextbookAmbientCertificateStep_l.negPiFalse hBody

theorem textbookAmbientSigmaCertificate_conj_l
    {top : Ordinal.{u}} (level : Nat) {arity leftCode rightCode : Nat}
    {assignment : Tuple (StageCarrier top) arity}
    (hLeft : TextbookAmbientSigmaCertificate_l top level leftCode assignment)
    (hRight : TextbookAmbientSigmaCertificate_l top level rightCode assignment) :
    TextbookAmbientSigmaCertificate_l top level
      (textbookECode leftCode rightCode 3) assignment := by
  cases level <;>
    exact TextbookAmbientCertificateStep_l.conjSigma hLeft hRight

theorem textbookAmbientPiFalseCertificate_conjLeft_l
    {top : Ordinal.{u}} (level : Nat) {arity leftCode rightCode : Nat}
    {assignment : Tuple (StageCarrier top) arity}
    (hLeft : TextbookAmbientPiFalseCertificate_l top level leftCode assignment)
    (hRight : TextbookBoundedIsPiCode_l level arity rightCode) :
    TextbookAmbientPiFalseCertificate_l top level
      (textbookECode leftCode rightCode 3) assignment := by
  cases level <;>
    exact TextbookAmbientCertificateStep_l.conjPiFalseLeft hLeft hRight

theorem textbookAmbientPiFalseCertificate_conjRight_l
    {top : Ordinal.{u}} (level : Nat) {arity leftCode rightCode : Nat}
    {assignment : Tuple (StageCarrier top) arity}
    (hLeft : TextbookBoundedIsPiCode_l level arity leftCode)
    (hRight : TextbookAmbientPiFalseCertificate_l top level rightCode assignment) :
    TextbookAmbientPiFalseCertificate_l top level
      (textbookECode leftCode rightCode 3) assignment := by
  cases level <;>
    exact TextbookAmbientCertificateStep_l.conjPiFalseRight hLeft hRight

theorem textbookAmbientSigmaCertificate_ex_l
    {top : Ordinal.{u}} (level : Nat) {arity code : Nat}
    {assignment : Tuple (StageCarrier top) arity}
    (witness : StageCarrier top)
    (hBody : TextbookAmbientSigmaCertificate_l top level code
      (snoc assignment witness)) :
    TextbookAmbientSigmaCertificate_l top level
      (textbookECode code 0 4) assignment := by
  cases level <;>
    exact TextbookAmbientCertificateStep_l.exSigma witness hBody

theorem textbookAmbientSigmaCertificate_lowerSigmaTruth_l
    {top : Ordinal.{u}} (lowerLevel : Nat) {arity code : Nat}
    {assignment : Tuple (StageCarrier top) arity}
    (hCode : TextbookBoundedIsSigmaCode_l lowerLevel arity code)
    (hCertificate : TextbookAmbientSigmaCertificate_l top lowerLevel code assignment) :
    TextbookAmbientSigmaCertificate_l top (lowerLevel + 1) code assignment := by
  exact TextbookAmbientCertificateStep_l.lowerSigmaTruth trivial hCode hCertificate

theorem textbookAmbientSigmaCertificate_lowerPiTruth_l
    {top : Ordinal.{u}} (lowerLevel : Nat) {arity code : Nat}
    {assignment : Tuple (StageCarrier top) arity}
    (hCode : TextbookBoundedIsPiCode_l lowerLevel arity code)
    (hCertificate : ¬ TextbookAmbientPiFalseCertificate_l top lowerLevel code assignment) :
    TextbookAmbientSigmaCertificate_l top (lowerLevel + 1) code assignment := by
  exact TextbookAmbientCertificateStep_l.lowerPiTruth trivial hCode hCertificate

theorem textbookAmbientPiFalseCertificate_lowerPiFalse_l
    {top : Ordinal.{u}} (lowerLevel : Nat) {arity code : Nat}
    {assignment : Tuple (StageCarrier top) arity}
    (hCode : TextbookBoundedIsPiCode_l lowerLevel arity code)
    (hCertificate : TextbookAmbientPiFalseCertificate_l top lowerLevel code assignment) :
    TextbookAmbientPiFalseCertificate_l top (lowerLevel + 1) code assignment := by
  exact TextbookAmbientCertificateStep_l.lowerPiFalse trivial hCode hCertificate

theorem textbookAmbientPiFalseCertificate_lowerSigmaFalse_l
    {top : Ordinal.{u}} (lowerLevel : Nat) {arity code : Nat}
    {assignment : Tuple (StageCarrier top) arity}
    (hCode : TextbookBoundedIsSigmaCode_l lowerLevel arity code)
    (hCertificate : ¬ TextbookAmbientSigmaCertificate_l top lowerLevel code assignment) :
    TextbookAmbientPiFalseCertificate_l top (lowerLevel + 1) code assignment := by
  exact TextbookAmbientCertificateStep_l.lowerSigmaFalse trivial hCode hCertificate

/-! ## 证书可靠性 -/

/-- 按证书极性选择其外部语义。 -/
def TextbookAmbientCertificateMeaning_l
    (top : Ordinal.{u}) (level : Nat) (mode : Bool)
    {arity : Nat} (code : Nat) (assignment : Tuple (StageCarrier top) arity) : Prop :=
  if mode then
    ∃ formula : FOFormula arity,
      textbookFormulaCode_l formula = code ∧
      ExternalBoundedIsSigmaFinite_l level formula ∧
      FOFormula.Satisfies (stageMembership_l top) formula assignment
  else
    ∃ formula : FOFormula arity,
      textbookFormulaCode_l formula = code ∧
      ExternalBoundedIsPiFinite_l level formula ∧
      ¬ FOFormula.Satisfies (stageMembership_l top) formula assignment

/-- 单层有限证书的可靠性。 -/
theorem textbookAmbientCertificateStep_sound_l
    {top : Ordinal.{u}} {currentLevel lowerLevel : Nat} {hasLower : Prop}
    {lowerSigma : {arity : Nat} → Nat → Tuple (StageCarrier top) arity → Prop}
    {lowerPiFalse : {arity : Nat} → Nat → Tuple (StageCarrier top) arity → Prop}
    (hCurrent : hasLower → currentLevel = lowerLevel + 1)
    (hLowerSigmaSound : ∀ {arity code} {assignment : Tuple (StageCarrier top) arity},
      lowerSigma code assignment →
        TextbookAmbientCertificateMeaning_l top lowerLevel true code assignment)
    (hLowerPiSound : ∀ {arity code} {assignment : Tuple (StageCarrier top) arity},
      lowerPiFalse code assignment →
        TextbookAmbientCertificateMeaning_l top lowerLevel false code assignment)
    (hLowerSigmaComplete : hasLower → ∀ {arity code}
      (hCode : TextbookBoundedIsSigmaCode_l lowerLevel arity code)
      (formula : FOFormula arity), textbookFormulaCode_l formula = code →
      ∀ assignment : Tuple (StageCarrier top) arity,
        FOFormula.Satisfies (stageMembership_l top) formula assignment →
          lowerSigma code assignment)
    (hLowerPiComplete : hasLower → ∀ {arity code}
      (hCode : TextbookBoundedIsPiCode_l lowerLevel arity code)
      (formula : FOFormula arity), textbookFormulaCode_l formula = code →
      ∀ assignment : Tuple (StageCarrier top) arity,
        ¬ FOFormula.Satisfies (stageMembership_l top) formula assignment →
          lowerPiFalse code assignment)
    {mode arity code} {assignment : Tuple (StageCarrier top) arity}
    (hCertificate : TextbookAmbientCertificateStep_l top currentLevel lowerLevel
      hasLower lowerSigma lowerPiFalse mode code assignment) :
    TextbookAmbientCertificateMeaning_l top currentLevel mode code assignment := by
  induction hCertificate with
  | deltaSigma formula assignment hFormula =>
      exact ⟨formula.toFO, rfl, .delta0 formula, hFormula⟩
  | deltaPiFalse formula assignment hFormula =>
      exact ⟨formula.toFO, rfl, .delta0 formula, hFormula⟩
  | negSigma hChild ih =>
      rcases ih with ⟨body, rfl, hBody, hFalse⟩
      exact ⟨.neg body, rfl, .neg hBody, hFalse⟩
  | negPiFalse hChild ih =>
      rcases ih with ⟨body, rfl, hBody, hTrue⟩
      exact ⟨.neg body, rfl, .neg hBody, fun hNeg => hNeg hTrue⟩
  | conjSigma hLeft hRight ihLeft ihRight =>
      rcases ihLeft with ⟨left, rfl, hLeftClass, hLeftSat⟩
      rcases ihRight with ⟨right, rfl, hRightClass, hRightSat⟩
      exact ⟨.conj left right, rfl, .conj hLeftClass hRightClass,
        ⟨hLeftSat, hRightSat⟩⟩
  | conjPiFalseLeft hLeft hRightCode ihLeft =>
      rcases ihLeft with ⟨left, rfl, hLeftClass, hLeftFalse⟩
      rcases hRightCode.decode with ⟨right, hRightCodeEq, hRightClass⟩
      exact ⟨.conj left right,
        by simp [textbookFormulaCode_l, hRightCodeEq],
        .conj hLeftClass hRightClass,
        fun hBoth => hLeftFalse hBoth.1⟩
  | conjPiFalseRight hLeftCode hRight ihRight =>
      rcases hLeftCode.decode with ⟨left, hLeftCodeEq, hLeftClass⟩
      rcases ihRight with ⟨right, rfl, hRightClass, hRightFalse⟩
      exact ⟨.conj left right,
        by simp [textbookFormulaCode_l, hLeftCodeEq],
        .conj hLeftClass hRightClass,
        fun hBoth => hRightFalse hBoth.2⟩
  | exSigma witness hBody ihBody =>
      rcases ihBody with ⟨body, rfl, hBodyClass, hBodySat⟩
      exact ⟨.ex body, rfl, .ex hBodyClass, ⟨witness, hBodySat⟩⟩
  | lowerSigmaTruth hAvailable hCode hLower =>
      have hMeaning := hLowerSigmaSound hLower
      rcases hMeaning with ⟨formula, hFormulaCode, hClass, hSat⟩
      rw [hCurrent hAvailable]
      exact ⟨formula, hFormulaCode, .lift hClass, hSat⟩
  | @lowerPiTruth arity code assignment hAvailable hCode hNotFalse =>
      rcases hCode.decode with ⟨formula, hFormulaCode, hClass⟩
      rw [hCurrent hAvailable]
      refine ⟨formula, hFormulaCode, .ofPi hClass, ?_⟩
      by_contra hFalse
      exact hNotFalse
        (hLowerPiComplete hAvailable hCode formula hFormulaCode assignment hFalse)
  | lowerPiFalse hAvailable hCode hLower =>
      have hMeaning := hLowerPiSound hLower
      rcases hMeaning with ⟨formula, hFormulaCode, hClass, hFalse⟩
      rw [hCurrent hAvailable]
      exact ⟨formula, hFormulaCode, .lift hClass, hFalse⟩
  | @lowerSigmaFalse arity code assignment hAvailable hCode hNotTrue =>
      rcases hCode.decode with ⟨formula, hFormulaCode, hClass⟩
      rw [hCurrent hAvailable]
      refine ⟨formula, hFormulaCode, .ofSigma hClass, ?_⟩
      intro hSat
      exact hNotTrue
        (hLowerSigmaComplete hAvailable hCode formula hFormulaCode assignment hSat)

/-! ## 全层可靠性与完备性 -/

/-- 固定层的四个证书正确性方向。 -/
def TextbookAmbientCertificateCorrectAt_l
    (top : Ordinal.{u}) (level : Nat) : Prop :=
  (∀ {arity code : Nat} {assignment : Tuple (StageCarrier top) arity},
    TextbookAmbientSigmaCertificate_l top level code assignment →
      TextbookAmbientCertificateMeaning_l top level true code assignment) ∧
  (∀ {arity code : Nat} {assignment : Tuple (StageCarrier top) arity},
    TextbookAmbientPiFalseCertificate_l top level code assignment →
      TextbookAmbientCertificateMeaning_l top level false code assignment) ∧
  (∀ {arity code : Nat} (hCode : TextbookBoundedIsSigmaCode_l level arity code)
      (formula : FOFormula arity), textbookFormulaCode_l formula = code →
      ∀ assignment : Tuple (StageCarrier top) arity,
        FOFormula.Satisfies (stageMembership_l top) formula assignment →
          TextbookAmbientSigmaCertificate_l top level code assignment) ∧
  (∀ {arity code : Nat} (hCode : TextbookBoundedIsPiCode_l level arity code)
      (formula : FOFormula arity), textbookFormulaCode_l formula = code →
      ∀ assignment : Tuple (StageCarrier top) arity,
        ¬ FOFormula.Satisfies (stageMembership_l top) formula assignment →
          TextbookAmbientPiFalseCertificate_l top level code assignment)

/--
固定有限 Levy 层的证书与真实 Tarski 语义完全一致。证明对层级作强归纳；
同层语法递归由码证书的共同递归子处理，跨层叶只使用严格低层的归纳假设。
-/
theorem textbookAmbientCertificate_correctAt_l
    (top : Ordinal.{u}) (level : Nat) :
    TextbookAmbientCertificateCorrectAt_l top level := by
  induction level using Nat.strong_induction_on with
  | h level hLower =>
      have hPrevious : ∀ previous, previous < level →
          TextbookAmbientCertificateCorrectAt_l top previous :=
        fun previous hPrevious => hLower previous hPrevious
      have hSigmaSound : ∀ {arity code : Nat}
          {assignment : Tuple (StageCarrier top) arity},
          TextbookAmbientSigmaCertificate_l top level code assignment →
            TextbookAmbientCertificateMeaning_l top level true code assignment := by
        cases level with
        | zero =>
            intro arity code assignment hCertificate
            change TextbookAmbientSigmaCertificateStep_l top 0 0 False
              (fun _ _ => False) (fun _ _ => False) code assignment at hCertificate
            apply textbookAmbientCertificateStep_sound_l
              (fun hFalse => False.elim hFalse)
              (fun hFalse => False.elim hFalse)
              (fun hFalse => False.elim hFalse)
              (fun hFalse => False.elim hFalse)
              (fun hFalse => False.elim hFalse)
              hCertificate
        | succ previous =>
            intro arity code assignment hCertificate
            rcases hPrevious previous (Nat.lt_succ_self previous) with
              ⟨hPreviousSigmaSound, hPreviousPiSound,
                hPreviousSigmaComplete, hPreviousPiComplete⟩
            change TextbookAmbientSigmaCertificateStep_l top (previous + 1) previous True
              (TextbookAmbientSigmaCertificate_l top previous)
              (TextbookAmbientPiFalseCertificate_l top previous)
              code assignment at hCertificate
            exact textbookAmbientCertificateStep_sound_l (fun _ => rfl)
              hPreviousSigmaSound hPreviousPiSound
              (fun _ => hPreviousSigmaComplete)
              (fun _ => hPreviousPiComplete) hCertificate
      have hPiSound : ∀ {arity code : Nat}
          {assignment : Tuple (StageCarrier top) arity},
          TextbookAmbientPiFalseCertificate_l top level code assignment →
            TextbookAmbientCertificateMeaning_l top level false code assignment := by
        cases level with
        | zero =>
            intro arity code assignment hCertificate
            change TextbookAmbientPiFalseCertificateStep_l top 0 0 False
              (fun _ _ => False) (fun _ _ => False) code assignment at hCertificate
            apply textbookAmbientCertificateStep_sound_l
              (fun hFalse => False.elim hFalse)
              (fun hFalse => False.elim hFalse)
              (fun hFalse => False.elim hFalse)
              (fun hFalse => False.elim hFalse)
              (fun hFalse => False.elim hFalse)
              hCertificate
        | succ previous =>
            intro arity code assignment hCertificate
            rcases hPrevious previous (Nat.lt_succ_self previous) with
              ⟨hPreviousSigmaSound, hPreviousPiSound,
                hPreviousSigmaComplete, hPreviousPiComplete⟩
            change TextbookAmbientPiFalseCertificateStep_l top (previous + 1) previous True
              (TextbookAmbientSigmaCertificate_l top previous)
              (TextbookAmbientPiFalseCertificate_l top previous)
              code assignment at hCertificate
            exact textbookAmbientCertificateStep_sound_l (fun _ => rfl)
              hPreviousSigmaSound hPreviousPiSound
              (fun _ => hPreviousSigmaComplete)
              (fun _ => hPreviousPiComplete) hCertificate
      have hSigmaComplete : ∀ {arity code : Nat}
          (hCode : TextbookBoundedIsSigmaCode_l level arity code)
          (formula : FOFormula arity), textbookFormulaCode_l formula = code →
          ∀ assignment : Tuple (StageCarrier top) arity,
            FOFormula.Satisfies (stageMembership_l top) formula assignment →
              TextbookAmbientSigmaCertificate_l top level code assignment := by
        intro arity code hCode
        exact TextbookBoundedIsSigmaCode_l.rec
          (motive_1 := fun currentLevel arity code _ =>
            currentLevel ≤ level →
            ∀ formula : FOFormula arity, textbookFormulaCode_l formula = code →
            ∀ assignment : Tuple (StageCarrier top) arity,
              FOFormula.Satisfies (stageMembership_l top) formula assignment →
                TextbookAmbientSigmaCertificate_l top currentLevel code assignment)
          (motive_2 := fun currentLevel arity code _ =>
            currentLevel ≤ level →
            ∀ formula : FOFormula arity, textbookFormulaCode_l formula = code →
            ∀ assignment : Tuple (StageCarrier top) arity,
              ¬ FOFormula.Satisfies (stageMembership_l top) formula assignment →
                TextbookAmbientPiFalseCertificate_l top currentLevel code assignment)
          (fun hDelta _ formula hFormulaCode assignment hSat => by
            rcases hDelta.decode with ⟨bounded, hBoundedCode⟩
            have hFormula : formula = bounded.toFO :=
              textbookFormulaCode_injective_l
                (hFormulaCode.trans hBoundedCode.symm)
            subst formula
            rw [← hFormulaCode]
            exact textbookAmbientSigmaCertificate_delta_l _ bounded assignment hSat)
          (fun hBody ih hBound formula hFormulaCode assignment hSat => by
            rcases hBody.decode with ⟨body, hBodyCode, _⟩
            have hFormula : formula = .neg body :=
              textbookFormulaCode_injective_l
                (hFormulaCode.trans (by simp [textbookFormulaCode_l, hBodyCode]))
            subst formula
            exact textbookAmbientSigmaCertificate_neg_l _
              (ih hBound body hBodyCode assignment hSat))
          (fun hLeft hRight ihLeft ihRight hBound formula hFormulaCode assignment hSat => by
            rcases hLeft.decode with ⟨left, hLeftCode, _⟩
            rcases hRight.decode with ⟨right, hRightCode, _⟩
            have hFormula : formula = .conj left right :=
              textbookFormulaCode_injective_l
                (hFormulaCode.trans (by simp [textbookFormulaCode_l,
                  hLeftCode, hRightCode]))
            subst formula
            exact textbookAmbientSigmaCertificate_conj_l _
              (ihLeft hBound left hLeftCode assignment hSat.1)
              (ihRight hBound right hRightCode assignment hSat.2))
          (fun hBody ih hBound formula hFormulaCode assignment hSat => by
            rcases hBody.decode with ⟨body, hBodyCode, _⟩
            have hFormula : formula = .ex body :=
              textbookFormulaCode_injective_l
                (hFormulaCode.trans (by simp [textbookFormulaCode_l, hBodyCode]))
            subst formula
            rcases hSat with ⟨witness, hWitness⟩
            exact textbookAmbientSigmaCertificate_ex_l _ witness
              (ih hBound body hBodyCode (snoc assignment witness) hWitness))
          (fun hChild ih hBound formula hFormulaCode assignment hSat => by
            change TextbookAmbientSigmaCertificateStep_l top (_ + 1) _ True
              (TextbookAmbientSigmaCertificate_l top _)
              (TextbookAmbientPiFalseCertificate_l top _)
              _ _
            exact .lowerSigmaTruth trivial hChild
              (ih (Nat.le_of_lt (lt_of_lt_of_le (Nat.lt_succ_self _) hBound))
                formula hFormulaCode assignment hSat))
          (fun hChild _ hBound formula hFormulaCode assignment hSat => by
            have hChildLt : _ < level :=
              lt_of_lt_of_le (Nat.lt_succ_self _) hBound
            rcases hPrevious _ hChildLt with
              ⟨_, hChildPiSound, _, _⟩
            change TextbookAmbientSigmaCertificateStep_l top (_ + 1) _ True
              (TextbookAmbientSigmaCertificate_l top _)
              (TextbookAmbientPiFalseCertificate_l top _)
              _ _
            apply TextbookAmbientCertificateStep_l.lowerPiTruth trivial hChild
            intro hFalseCertificate
            rcases hChildPiSound hFalseCertificate with
              ⟨other, hOtherCode, _, hOtherFalse⟩
            have hOther : other = formula :=
              textbookFormulaCode_injective_l
                (hOtherCode.trans hFormulaCode.symm)
            subst other
            exact hOtherFalse hSat)
          (fun hDelta _ formula hFormulaCode assignment hFalse => by
            rcases hDelta.decode with ⟨bounded, hBoundedCode⟩
            have hFormula : formula = bounded.toFO :=
              textbookFormulaCode_injective_l
                (hFormulaCode.trans hBoundedCode.symm)
            subst formula
            rw [← hFormulaCode]
            exact textbookAmbientPiFalseCertificate_delta_l _ bounded assignment hFalse)
          (fun hBody ih hBound formula hFormulaCode assignment hFalse => by
            rcases hBody.decode with ⟨body, hBodyCode, _⟩
            have hFormula : formula = .neg body :=
              textbookFormulaCode_injective_l
                (hFormulaCode.trans (by simp [textbookFormulaCode_l, hBodyCode]))
            subst formula
            exact textbookAmbientPiFalseCertificate_neg_l _
              (ih hBound body hBodyCode assignment (Classical.not_not.mp hFalse)))
          (fun hLeft hRight ihLeft ihRight hBound formula hFormulaCode assignment hFalse => by
            rcases hLeft.decode with ⟨left, hLeftCode, _⟩
            rcases hRight.decode with ⟨right, hRightCode, _⟩
            have hFormula : formula = .conj left right :=
              textbookFormulaCode_injective_l
                (hFormulaCode.trans (by simp [textbookFormulaCode_l,
                  hLeftCode, hRightCode]))
            subst formula
            by_cases hLeftSat : FOFormula.Satisfies
                (stageMembership_l top) left assignment
            · exact textbookAmbientPiFalseCertificate_conjRight_l _ hLeft
                (ihRight hBound right hRightCode assignment
                  (fun hRightSat => hFalse ⟨hLeftSat, hRightSat⟩))
            · exact textbookAmbientPiFalseCertificate_conjLeft_l _
                (ihLeft hBound left hLeftCode assignment hLeftSat) hRight)
          (fun hChild ih hBound formula hFormulaCode assignment hFalse => by
            change TextbookAmbientPiFalseCertificateStep_l top (_ + 1) _ True
              (TextbookAmbientSigmaCertificate_l top _)
              (TextbookAmbientPiFalseCertificate_l top _)
              _ _
            exact .lowerPiFalse trivial hChild
              (ih (Nat.le_of_lt (lt_of_lt_of_le (Nat.lt_succ_self _) hBound))
                formula hFormulaCode assignment hFalse))
          (fun hChild _ hBound formula hFormulaCode assignment hFalse => by
            have hChildLt : _ < level :=
              lt_of_lt_of_le (Nat.lt_succ_self _) hBound
            rcases hPrevious _ hChildLt with
              ⟨hChildSigmaSound, _, _, _⟩
            change TextbookAmbientPiFalseCertificateStep_l top (_ + 1) _ True
              (TextbookAmbientSigmaCertificate_l top _)
              (TextbookAmbientPiFalseCertificate_l top _)
              _ _
            apply TextbookAmbientCertificateStep_l.lowerSigmaFalse trivial hChild
            intro hTrueCertificate
            rcases hChildSigmaSound hTrueCertificate with
              ⟨other, hOtherCode, _, hOtherSat⟩
            have hOther : other = formula :=
              textbookFormulaCode_injective_l
                (hOtherCode.trans hFormulaCode.symm)
            subst other
            exact hFalse hOtherSat)
          hCode (Nat.le_refl level)
      have hPiComplete : ∀ {arity code : Nat}
          (hCode : TextbookBoundedIsPiCode_l level arity code)
          (formula : FOFormula arity), textbookFormulaCode_l formula = code →
          ∀ assignment : Tuple (StageCarrier top) arity,
            ¬ FOFormula.Satisfies (stageMembership_l top) formula assignment →
              TextbookAmbientPiFalseCertificate_l top level code assignment := by
        intro arity code hCode
        exact TextbookBoundedIsPiCode_l.rec
          (motive_1 := fun currentLevel arity code _ =>
            currentLevel ≤ level →
            ∀ formula : FOFormula arity, textbookFormulaCode_l formula = code →
            ∀ assignment : Tuple (StageCarrier top) arity,
              FOFormula.Satisfies (stageMembership_l top) formula assignment →
                TextbookAmbientSigmaCertificate_l top currentLevel code assignment)
          (motive_2 := fun currentLevel arity code _ =>
            currentLevel ≤ level →
            ∀ formula : FOFormula arity, textbookFormulaCode_l formula = code →
            ∀ assignment : Tuple (StageCarrier top) arity,
              ¬ FOFormula.Satisfies (stageMembership_l top) formula assignment →
                TextbookAmbientPiFalseCertificate_l top currentLevel code assignment)
          (fun hDelta _ formula hFormulaCode assignment hSat => by
            rcases hDelta.decode with ⟨bounded, hBoundedCode⟩
            have hFormula : formula = bounded.toFO :=
              textbookFormulaCode_injective_l
                (hFormulaCode.trans hBoundedCode.symm)
            subst formula
            rw [← hFormulaCode]
            exact textbookAmbientSigmaCertificate_delta_l _ bounded assignment hSat)
          (fun hBody ih hBound formula hFormulaCode assignment hSat => by
            rcases hBody.decode with ⟨body, hBodyCode, _⟩
            have hFormula : formula = .neg body :=
              textbookFormulaCode_injective_l
                (hFormulaCode.trans (by simp [textbookFormulaCode_l, hBodyCode]))
            subst formula
            exact textbookAmbientSigmaCertificate_neg_l _
              (ih hBound body hBodyCode assignment hSat))
          (fun hLeft hRight ihLeft ihRight hBound formula hFormulaCode assignment hSat => by
            rcases hLeft.decode with ⟨left, hLeftCode, _⟩
            rcases hRight.decode with ⟨right, hRightCode, _⟩
            have hFormula : formula = .conj left right :=
              textbookFormulaCode_injective_l
                (hFormulaCode.trans (by simp [textbookFormulaCode_l,
                  hLeftCode, hRightCode]))
            subst formula
            exact textbookAmbientSigmaCertificate_conj_l _
              (ihLeft hBound left hLeftCode assignment hSat.1)
              (ihRight hBound right hRightCode assignment hSat.2))
          (fun hBody ih hBound formula hFormulaCode assignment hSat => by
            rcases hBody.decode with ⟨body, hBodyCode, _⟩
            have hFormula : formula = .ex body :=
              textbookFormulaCode_injective_l
                (hFormulaCode.trans (by simp [textbookFormulaCode_l, hBodyCode]))
            subst formula
            rcases hSat with ⟨witness, hWitness⟩
            exact textbookAmbientSigmaCertificate_ex_l _ witness
              (ih hBound body hBodyCode (snoc assignment witness) hWitness))
          (fun hChild ih hBound formula hFormulaCode assignment hSat => by
            change TextbookAmbientSigmaCertificateStep_l top (_ + 1) _ True
              (TextbookAmbientSigmaCertificate_l top _)
              (TextbookAmbientPiFalseCertificate_l top _)
              _ _
            exact .lowerSigmaTruth trivial hChild
              (ih (Nat.le_of_lt (lt_of_lt_of_le (Nat.lt_succ_self _) hBound))
                formula hFormulaCode assignment hSat))
          (fun hChild _ hBound formula hFormulaCode assignment hSat => by
            have hChildLt : _ < level :=
              lt_of_lt_of_le (Nat.lt_succ_self _) hBound
            rcases hPrevious _ hChildLt with ⟨_, hChildPiSound, _, _⟩
            change TextbookAmbientSigmaCertificateStep_l top (_ + 1) _ True
              (TextbookAmbientSigmaCertificate_l top _)
              (TextbookAmbientPiFalseCertificate_l top _)
              _ _
            apply TextbookAmbientCertificateStep_l.lowerPiTruth trivial hChild
            intro hFalseCertificate
            rcases hChildPiSound hFalseCertificate with
              ⟨other, hOtherCode, _, hOtherFalse⟩
            have hOther : other = formula :=
              textbookFormulaCode_injective_l
                (hOtherCode.trans hFormulaCode.symm)
            subst other
            exact hOtherFalse hSat)
          (fun hDelta _ formula hFormulaCode assignment hFalse => by
            rcases hDelta.decode with ⟨bounded, hBoundedCode⟩
            have hFormula : formula = bounded.toFO :=
              textbookFormulaCode_injective_l
                (hFormulaCode.trans hBoundedCode.symm)
            subst formula
            rw [← hFormulaCode]
            exact textbookAmbientPiFalseCertificate_delta_l _ bounded assignment hFalse)
          (fun hBody ih hBound formula hFormulaCode assignment hFalse => by
            rcases hBody.decode with ⟨body, hBodyCode, _⟩
            have hFormula : formula = .neg body :=
              textbookFormulaCode_injective_l
                (hFormulaCode.trans (by simp [textbookFormulaCode_l, hBodyCode]))
            subst formula
            exact textbookAmbientPiFalseCertificate_neg_l _
              (ih hBound body hBodyCode assignment (Classical.not_not.mp hFalse)))
          (fun hLeft hRight ihLeft ihRight hBound formula hFormulaCode assignment hFalse => by
            rcases hLeft.decode with ⟨left, hLeftCode, _⟩
            rcases hRight.decode with ⟨right, hRightCode, _⟩
            have hFormula : formula = .conj left right :=
              textbookFormulaCode_injective_l
                (hFormulaCode.trans (by simp [textbookFormulaCode_l,
                  hLeftCode, hRightCode]))
            subst formula
            by_cases hLeftSat : FOFormula.Satisfies
                (stageMembership_l top) left assignment
            · exact textbookAmbientPiFalseCertificate_conjRight_l _ hLeft
                (ihRight hBound right hRightCode assignment
                  (fun hRightSat => hFalse ⟨hLeftSat, hRightSat⟩))
            · exact textbookAmbientPiFalseCertificate_conjLeft_l _
                (ihLeft hBound left hLeftCode assignment hLeftSat) hRight)
          (fun hChild ih hBound formula hFormulaCode assignment hFalse => by
            change TextbookAmbientPiFalseCertificateStep_l top (_ + 1) _ True
              (TextbookAmbientSigmaCertificate_l top _)
              (TextbookAmbientPiFalseCertificate_l top _)
              _ _
            exact .lowerPiFalse trivial hChild
              (ih (Nat.le_of_lt (lt_of_lt_of_le (Nat.lt_succ_self _) hBound))
                formula hFormulaCode assignment hFalse))
          (fun hChild _ hBound formula hFormulaCode assignment hFalse => by
            have hChildLt : _ < level :=
              lt_of_lt_of_le (Nat.lt_succ_self _) hBound
            rcases hPrevious _ hChildLt with ⟨hChildSigmaSound, _, _, _⟩
            change TextbookAmbientPiFalseCertificateStep_l top (_ + 1) _ True
              (TextbookAmbientSigmaCertificate_l top _)
              (TextbookAmbientPiFalseCertificate_l top _)
              _ _
            apply TextbookAmbientCertificateStep_l.lowerSigmaFalse trivial hChild
            intro hTrueCertificate
            rcases hChildSigmaSound hTrueCertificate with
              ⟨other, hOtherCode, _, hOtherSat⟩
            have hOther : other = formula :=
              textbookFormulaCode_injective_l
                (hOtherCode.trans hFormulaCode.symm)
            subst other
            exact hFalse hOtherSat)
          hCode (Nat.le_refl level)
      exact ⟨hSigmaSound, hPiSound, hSigmaComplete, hPiComplete⟩

/-- 已分类 `Sigma` 公式的证书存在性精确等价于它在当前层为真。 -/
theorem textbookAmbientSigmaCertificate_iff_l
    {top : Ordinal.{u}} {level arity : Nat}
    (formula : FOFormula arity)
    (hFormula : ExternalBoundedIsSigmaFinite_l level formula)
    (assignment : Tuple (StageCarrier top) arity) :
    TextbookAmbientSigmaCertificate_l top level
        (textbookFormulaCode_l formula) assignment ↔
      FOFormula.Satisfies (stageMembership_l top) formula assignment := by
  let hCode := textbookFormulaCode_bounded_isSigma_l hFormula
  rcases textbookAmbientCertificate_correctAt_l top level with
    ⟨hSound, _, hComplete, _⟩
  constructor
  · intro hCertificate
    rcases hSound hCertificate with
      ⟨other, hOtherCode, _, hOtherSat⟩
    have hOther : other = formula :=
      textbookFormulaCode_injective_l hOtherCode
    simpa only [hOther] using hOtherSat
  · intro hSat
    exact hComplete hCode formula rfl assignment hSat

/-- 已分类 `Pi` 公式的假证书存在性精确等价于它在当前层为假。 -/
theorem textbookAmbientPiFalseCertificate_iff_l
    {top : Ordinal.{u}} {level arity : Nat}
    (formula : FOFormula arity)
    (hFormula : ExternalBoundedIsPiFinite_l level formula)
    (assignment : Tuple (StageCarrier top) arity) :
    TextbookAmbientPiFalseCertificate_l top level
        (textbookFormulaCode_l formula) assignment ↔
      ¬ FOFormula.Satisfies (stageMembership_l top) formula assignment := by
  let hCode := textbookFormulaCode_bounded_isPi_l hFormula
  rcases textbookAmbientCertificate_correctAt_l top level with
    ⟨_, hSound, _, hComplete⟩
  constructor
  · intro hCertificate
    rcases hSound hCertificate with
      ⟨other, hOtherCode, _, hOtherFalse⟩
    have hOther : other = formula :=
      textbookFormulaCode_injective_l hOtherCode
    simpa only [hOther] using hOtherFalse
  · intro hFalse
    exact hComplete hCode formula rfl assignment hFalse

end YesMetaZFC.BMS.ConstructibleBridge
