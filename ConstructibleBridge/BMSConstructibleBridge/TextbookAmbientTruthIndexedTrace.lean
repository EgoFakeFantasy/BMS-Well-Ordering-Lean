import BMSConstructibleBridge.TextbookAmbientTruthEarlierRecord

/-!
# Indexed local rules for ambient truth traces

Same-level recursive premises must occur in the already checked prefix.  A
level-raising row may instead consult the fully constructed certificate at the
strict predecessor level; this is the semantic shape that the recursively
defined object-language checker will mirror.
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- Canonical truth row attached to a typed stage assignment. -/
noncomputable def textbookAmbientTruthJudgmentOf_l
    {top : Ordinal.{u}} (isSigma : Bool) (level code : Nat)
    {arity : Nat} (assignment : Tuple (StageCarrier top) arity) :
    TextbookAmbientTruthJudgment_l.{u} :=
  ⟨⟨isSigma, level, arity, code⟩, textbookTupleGraph assignment⟩

/-- A row denotes the corresponding positive or negative certificate. -/
def TextbookAmbientTruthJudgment_l.Certified
    (top : Ordinal.{u}) (entry : TextbookAmbientTruthJudgment_l.{u}) : Prop :=
  ∃ assignment : Tuple (StageCarrier top) entry.arity,
    entry.assignmentCode = textbookTupleGraph assignment ∧
      if entry.isSigma then
        TextbookAmbientSigmaCertificate_l top entry.level entry.code assignment
      else
        TextbookAmbientPiFalseCertificate_l top entry.level entry.code assignment

/-- The textbook graph remembers every coordinate of its typed tuple. -/
theorem textbookTupleGraph_injective_l
    {top : Ordinal.{u}} {arity : Nat}
    {left right : Tuple (StageCarrier top) arity}
    (hGraph : textbookTupleGraph left = textbookTupleGraph right) :
    left = right := by
  funext index
  apply Subtype.ext
  have hValue := textbookTupleGraph_value left index
  rw [hGraph, textbookTupleGraph_value_iff right index] at hValue
  exact hValue

/-- Certification of a canonical row reduces to its selected certificate. -/
theorem textbookAmbientTruthJudgmentOf_certified_iff_l
    {top : Ordinal.{u}} (isSigma : Bool) (level code : Nat)
    {arity : Nat} (assignment : Tuple (StageCarrier top) arity) :
    (textbookAmbientTruthJudgmentOf_l isSigma level code assignment).Certified top ↔
      if isSigma then
        TextbookAmbientSigmaCertificate_l top level code assignment
      else
        TextbookAmbientPiFalseCertificate_l top level code assignment := by
  constructor
  · rintro ⟨other, hGraph, hCertificate⟩
    have hAssignment : assignment = other :=
      textbookTupleGraph_injective_l hGraph
    subst other
    exact hCertificate
  · intro hCertificate
    exact ⟨assignment, rfl, hCertificate⟩

/-- One nonrecursive row rule over a supplied set of strictly earlier rows. -/
inductive TextbookAmbientTruthRuleOver_l
    (top : Ordinal.{u})
    (available : TextbookAmbientTruthJudgment_l.{u} → Prop) :
    TextbookAmbientTruthJudgment_l.{u} → Prop where
  | deltaSigma (level : Nat) {arity : Nat} (formula : Delta0Formula arity)
      (assignment : Tuple (StageCarrier top) arity)
      (hFormula : FOFormula.Satisfies (stageMembership_l top)
        formula.toFO assignment) :
      TextbookAmbientTruthRuleOver_l top available
        (textbookAmbientTruthJudgmentOf_l true level
          (textbookFormulaCode_l formula.toFO) assignment)
  | deltaPiFalse (level : Nat) {arity : Nat} (formula : Delta0Formula arity)
      (assignment : Tuple (StageCarrier top) arity)
      (hFormula : ¬ FOFormula.Satisfies (stageMembership_l top)
        formula.toFO assignment) :
      TextbookAmbientTruthRuleOver_l top available
        (textbookAmbientTruthJudgmentOf_l false level
          (textbookFormulaCode_l formula.toFO) assignment)
  | negSigma (level code : Nat) {arity : Nat}
      (assignment : Tuple (StageCarrier top) arity) :
      available (textbookAmbientTruthJudgmentOf_l false level code assignment) →
      TextbookAmbientTruthRuleOver_l top available
        (textbookAmbientTruthJudgmentOf_l true level
          (textbookECode code 0 2) assignment)
  | negPiFalse (level code : Nat) {arity : Nat}
      (assignment : Tuple (StageCarrier top) arity) :
      available (textbookAmbientTruthJudgmentOf_l true level code assignment) →
      TextbookAmbientTruthRuleOver_l top available
        (textbookAmbientTruthJudgmentOf_l false level
          (textbookECode code 0 2) assignment)
  | conjSigma (level leftCode rightCode : Nat) {arity : Nat}
      (assignment : Tuple (StageCarrier top) arity) :
      available
        (textbookAmbientTruthJudgmentOf_l true level leftCode assignment) →
      available
        (textbookAmbientTruthJudgmentOf_l true level rightCode assignment) →
      TextbookAmbientTruthRuleOver_l top available
        (textbookAmbientTruthJudgmentOf_l true level
          (textbookECode leftCode rightCode 3) assignment)
  | conjPiFalseLeft (level leftCode rightCode : Nat) {arity : Nat}
      (assignment : Tuple (StageCarrier top) arity) :
      available
        (textbookAmbientTruthJudgmentOf_l false level leftCode assignment) →
      TextbookBoundedIsPiCode_l level arity rightCode →
      TextbookAmbientTruthRuleOver_l top available
        (textbookAmbientTruthJudgmentOf_l false level
          (textbookECode leftCode rightCode 3) assignment)
  | conjPiFalseRight (level leftCode rightCode : Nat) {arity : Nat}
      (assignment : Tuple (StageCarrier top) arity) :
      TextbookBoundedIsPiCode_l level arity leftCode →
      available
        (textbookAmbientTruthJudgmentOf_l false level rightCode assignment) →
      TextbookAmbientTruthRuleOver_l top available
        (textbookAmbientTruthJudgmentOf_l false level
          (textbookECode leftCode rightCode 3) assignment)
  | exSigma (level code : Nat) {arity : Nat}
      (assignment : Tuple (StageCarrier top) arity)
      (witness : StageCarrier top) :
      available (textbookAmbientTruthJudgmentOf_l true level code
        (snoc assignment witness)) →
      TextbookAmbientTruthRuleOver_l top available
        (textbookAmbientTruthJudgmentOf_l true level
          (textbookECode code 0 4) assignment)
  | lowerSigmaTruth (lowerLevel code : Nat) {arity : Nat}
      (assignment : Tuple (StageCarrier top) arity) :
      TextbookBoundedIsSigmaCode_l lowerLevel arity code →
      TextbookAmbientSigmaCertificate_l top lowerLevel code assignment →
      TextbookAmbientTruthRuleOver_l top available
        (textbookAmbientTruthJudgmentOf_l true (lowerLevel + 1)
          code assignment)
  | lowerPiTruth (lowerLevel code : Nat) {arity : Nat}
      (assignment : Tuple (StageCarrier top) arity) :
      TextbookBoundedIsPiCode_l lowerLevel arity code →
      (¬ TextbookAmbientPiFalseCertificate_l top lowerLevel code assignment) →
      TextbookAmbientTruthRuleOver_l top available
        (textbookAmbientTruthJudgmentOf_l true (lowerLevel + 1)
          code assignment)
  | lowerPiFalse (lowerLevel code : Nat) {arity : Nat}
      (assignment : Tuple (StageCarrier top) arity) :
      TextbookBoundedIsPiCode_l lowerLevel arity code →
      TextbookAmbientPiFalseCertificate_l top lowerLevel code assignment →
      TextbookAmbientTruthRuleOver_l top available
        (textbookAmbientTruthJudgmentOf_l false (lowerLevel + 1)
          code assignment)
  | lowerSigmaFalse (lowerLevel code : Nat) {arity : Nat}
      (assignment : Tuple (StageCarrier top) arity) :
      TextbookBoundedIsSigmaCode_l lowerLevel arity code →
      (¬ TextbookAmbientSigmaCertificate_l top lowerLevel code assignment) →
      TextbookAmbientTruthRuleOver_l top available
        (textbookAmbientTruthJudgmentOf_l false (lowerLevel + 1)
          code assignment)

/-- Every local rule is semantically sound when all referenced rows are certified. -/
theorem textbookAmbientTruthRuleOver_sound_l
    {top : Ordinal.{u}}
    {available : TextbookAmbientTruthJudgment_l.{u} → Prop}
    {entry : TextbookAmbientTruthJudgment_l.{u}}
    (hAvailable : ∀ child, available child → child.Certified top)
    (hRule : TextbookAmbientTruthRuleOver_l top available entry) :
    entry.Certified top := by
  cases hRule with
  | deltaSigma level formula assignment hFormula =>
      apply (textbookAmbientTruthJudgmentOf_certified_iff_l
        true level (textbookFormulaCode_l formula.toFO) assignment).mpr
      exact textbookAmbientSigmaCertificate_delta_l level formula assignment hFormula
  | deltaPiFalse level formula assignment hFormula =>
      apply (textbookAmbientTruthJudgmentOf_certified_iff_l
        false level (textbookFormulaCode_l formula.toFO) assignment).mpr
      exact textbookAmbientPiFalseCertificate_delta_l level formula assignment hFormula
  | negSigma level code assignment hBody =>
      apply (textbookAmbientTruthJudgmentOf_certified_iff_l
        true level (textbookECode code 0 2) assignment).mpr
      exact textbookAmbientSigmaCertificate_neg_l level
        ((textbookAmbientTruthJudgmentOf_certified_iff_l
          false level code assignment).mp (hAvailable _ hBody))
  | negPiFalse level code assignment hBody =>
      apply (textbookAmbientTruthJudgmentOf_certified_iff_l
        false level (textbookECode code 0 2) assignment).mpr
      exact textbookAmbientPiFalseCertificate_neg_l level
        ((textbookAmbientTruthJudgmentOf_certified_iff_l
          true level code assignment).mp (hAvailable _ hBody))
  | conjSigma level leftCode rightCode assignment hLeft hRight =>
      apply (textbookAmbientTruthJudgmentOf_certified_iff_l
        true level (textbookECode leftCode rightCode 3) assignment).mpr
      exact textbookAmbientSigmaCertificate_conj_l level
        ((textbookAmbientTruthJudgmentOf_certified_iff_l
          true level leftCode assignment).mp (hAvailable _ hLeft))
        ((textbookAmbientTruthJudgmentOf_certified_iff_l
          true level rightCode assignment).mp (hAvailable _ hRight))
  | conjPiFalseLeft level leftCode rightCode assignment hLeft hRight =>
      apply (textbookAmbientTruthJudgmentOf_certified_iff_l
        false level (textbookECode leftCode rightCode 3) assignment).mpr
      exact textbookAmbientPiFalseCertificate_conjLeft_l level
        ((textbookAmbientTruthJudgmentOf_certified_iff_l
          false level leftCode assignment).mp (hAvailable _ hLeft)) hRight
  | conjPiFalseRight level leftCode rightCode assignment hLeft hRight =>
      apply (textbookAmbientTruthJudgmentOf_certified_iff_l
        false level (textbookECode leftCode rightCode 3) assignment).mpr
      exact textbookAmbientPiFalseCertificate_conjRight_l level hLeft
        ((textbookAmbientTruthJudgmentOf_certified_iff_l
          false level rightCode assignment).mp (hAvailable _ hRight))
  | exSigma level code assignment witness hBody =>
      apply (textbookAmbientTruthJudgmentOf_certified_iff_l
        true level (textbookECode code 0 4) assignment).mpr
      exact textbookAmbientSigmaCertificate_ex_l level witness
        ((textbookAmbientTruthJudgmentOf_certified_iff_l
          true level code (snoc assignment witness)).mp (hAvailable _ hBody))
  | lowerSigmaTruth lowerLevel code assignment hCode hCertificate =>
      apply (textbookAmbientTruthJudgmentOf_certified_iff_l
        true (lowerLevel + 1) code assignment).mpr
      exact textbookAmbientSigmaCertificate_lowerSigmaTruth_l
        lowerLevel hCode hCertificate
  | lowerPiTruth lowerLevel code assignment hCode hCertificate =>
      apply (textbookAmbientTruthJudgmentOf_certified_iff_l
        true (lowerLevel + 1) code assignment).mpr
      exact textbookAmbientSigmaCertificate_lowerPiTruth_l
        lowerLevel hCode hCertificate
  | lowerPiFalse lowerLevel code assignment hCode hCertificate =>
      apply (textbookAmbientTruthJudgmentOf_certified_iff_l
        false (lowerLevel + 1) code assignment).mpr
      exact textbookAmbientPiFalseCertificate_lowerPiFalse_l
        lowerLevel hCode hCertificate
  | lowerSigmaFalse lowerLevel code assignment hCode hCertificate =>
      apply (textbookAmbientTruthJudgmentOf_certified_iff_l
        false (lowerLevel + 1) code assignment).mpr
      exact textbookAmbientPiFalseCertificate_lowerSigmaFalse_l
        lowerLevel hCode hCertificate

/-- Local rules remain valid when the set of available rows is enlarged. -/
theorem textbookAmbientTruthRuleOver_mono_l
    {top : Ordinal.{u}}
    {available available' : TextbookAmbientTruthJudgment_l.{u} → Prop}
    {entry : TextbookAmbientTruthJudgment_l.{u}}
    (hSubset : ∀ child, available child → available' child)
    (hRule : TextbookAmbientTruthRuleOver_l top available entry) :
    TextbookAmbientTruthRuleOver_l top available' entry := by
  cases hRule with
  | deltaSigma level formula assignment hFormula =>
      exact .deltaSigma level formula assignment hFormula
  | deltaPiFalse level formula assignment hFormula =>
      exact .deltaPiFalse level formula assignment hFormula
  | negSigma level code assignment hBody =>
      exact .negSigma level code assignment (hSubset _ hBody)
  | negPiFalse level code assignment hBody =>
      exact .negPiFalse level code assignment (hSubset _ hBody)
  | conjSigma level leftCode rightCode assignment hLeft hRight =>
      exact .conjSigma level leftCode rightCode assignment
        (hSubset _ hLeft) (hSubset _ hRight)
  | conjPiFalseLeft level leftCode rightCode assignment hLeft hRight =>
      exact .conjPiFalseLeft level leftCode rightCode assignment
        (hSubset _ hLeft) hRight
  | conjPiFalseRight level leftCode rightCode assignment hLeft hRight =>
      exact .conjPiFalseRight level leftCode rightCode assignment
        hLeft (hSubset _ hRight)
  | exSigma level code assignment witness hBody =>
      exact .exSigma level code assignment witness (hSubset _ hBody)
  | lowerSigmaTruth lowerLevel code assignment hCode hCertificate =>
      exact .lowerSigmaTruth lowerLevel code assignment hCode hCertificate
  | lowerPiTruth lowerLevel code assignment hCode hCertificate =>
      exact .lowerPiTruth lowerLevel code assignment hCode hCertificate
  | lowerPiFalse lowerLevel code assignment hCode hCertificate =>
      exact .lowerPiFalse lowerLevel code assignment hCode hCertificate
  | lowerSigmaFalse lowerLevel code assignment hCode hCertificate =>
      exact .lowerSigmaFalse lowerLevel code assignment hCode hCertificate

/-- At an index, availability is literal membership in the strict prefix. -/
def textbookAmbientTruthIndexedRule_l
    (top : Ordinal.{u}) (trace : List TextbookAmbientTruthJudgment_l.{u})
    (index : Fin trace.length) : Prop :=
  TextbookAmbientTruthRuleOver_l top
    (· ∈ trace.take index.1) (trace.get index)

/-- A finite trace is valid precisely when every row obeys its indexed rule. -/
def TextbookAmbientTruthTraceValid_l
    (top : Ordinal.{u})
    (trace : List TextbookAmbientTruthJudgment_l.{u}) : Prop :=
  ∀ index : Fin trace.length,
    textbookAmbientTruthIndexedRule_l top trace index

/-- A valid indexed trace may be extended by one row justified by the old trace. -/
theorem TextbookAmbientTruthTraceValid_l.snoc_l
    {top : Ordinal.{u}}
    {trace : List TextbookAmbientTruthJudgment_l.{u}}
    {entry : TextbookAmbientTruthJudgment_l.{u}}
    (hTrace : TextbookAmbientTruthTraceValid_l top trace)
    (hEntry : TextbookAmbientTruthRuleOver_l top (· ∈ trace) entry) :
    TextbookAmbientTruthTraceValid_l top (trace ++ [entry]) := by
  intro index
  by_cases hOld : index.1 < trace.length
  · let oldIndex : Fin trace.length := ⟨index.1, hOld⟩
    have hTake : (trace ++ [entry]).take index.1 = trace.take index.1 :=
      List.take_append_of_le_length (Nat.le_of_lt hOld)
    have hGet : (trace ++ [entry]).get index = trace.get oldIndex := by
      simp only [List.get_eq_getElem]
      rw [List.getElem_append_left hOld]
    simpa only [textbookAmbientTruthIndexedRule_l, hTake, hGet] using
      hTrace oldIndex
  · have hLast : index.1 = trace.length := by
      have hBound := index.2
      simp only [List.length_append, List.length_singleton] at hBound
      omega
    have hIndex : index = ⟨trace.length, by simp⟩ := Fin.ext hLast
    rw [hIndex]
    have hTake : (trace ++ [entry]).take trace.length = trace := by
      simpa using List.take_append_of_le_length (Nat.le_refl trace.length)
    have hGet : (trace ++ [entry]).get ⟨trace.length, by simp⟩ = entry := by
      simp
    simpa only [textbookAmbientTruthIndexedRule_l, hTake, hGet] using hEntry

/-- A constructor-oriented presentation of finite ambient truth traces. -/
inductive TextbookAmbientTruthTraceBuilt_l (top : Ordinal.{u}) :
    List TextbookAmbientTruthJudgment_l.{u} → Prop where
  | nil : TextbookAmbientTruthTraceBuilt_l top []
  | snoc {trace : List TextbookAmbientTruthJudgment_l.{u}}
      {entry : TextbookAmbientTruthJudgment_l.{u}} :
      TextbookAmbientTruthTraceBuilt_l top trace →
      TextbookAmbientTruthRuleOver_l top (· ∈ trace) entry →
      TextbookAmbientTruthTraceBuilt_l top (trace ++ [entry])

/-- Constructor-built traces satisfy the indexed validity definition. -/
theorem TextbookAmbientTruthTraceBuilt_l.valid_l
    {top : Ordinal.{u}} {trace : List TextbookAmbientTruthJudgment_l.{u}}
    (hTrace : TextbookAmbientTruthTraceBuilt_l top trace) :
    TextbookAmbientTruthTraceValid_l top trace := by
  induction hTrace with
  | nil => intro index; exact Fin.elim0 index
  | snoc hPrevious hEntry ih => exact ih.snoc_l hEntry

/-- Constructor-built traces may be concatenated without invalidating references. -/
theorem TextbookAmbientTruthTraceBuilt_l.append_l
    {top : Ordinal.{u}}
    {left right : List TextbookAmbientTruthJudgment_l.{u}}
    (hLeft : TextbookAmbientTruthTraceBuilt_l top left)
    (hRight : TextbookAmbientTruthTraceBuilt_l top right) :
    TextbookAmbientTruthTraceBuilt_l top (left ++ right) := by
  induction hRight with
  | nil => simpa using hLeft
  | @snoc previous entry hPrevious hEntry ih =>
      have hExtended := textbookAmbientTruthRuleOver_mono_l
        (available' := fun child => child ∈ left ++ previous)
        (fun child hChild => List.mem_append_right left hChild) hEntry
      simpa only [List.append_assoc] using
        TextbookAmbientTruthTraceBuilt_l.snoc ih hExtended

namespace TextbookAmbientTruthJudgment_l

/-- A row is supported by a finite constructor-built trace. -/
def HasTrace (top : Ordinal.{u})
    (entry : TextbookAmbientTruthJudgment_l.{u}) : Prop :=
  ∃ trace, TextbookAmbientTruthTraceBuilt_l top trace ∧ entry ∈ trace

/-- Append one locally justified row to an already built trace. -/
theorem hasTrace_of_rule_l
    {top : Ordinal.{u}}
    {trace : List TextbookAmbientTruthJudgment_l.{u}}
    {entry : TextbookAmbientTruthJudgment_l.{u}}
    (hTrace : TextbookAmbientTruthTraceBuilt_l top trace)
    (hRule : TextbookAmbientTruthRuleOver_l top (· ∈ trace) entry) :
    entry.HasTrace top :=
  ⟨trace ++ [entry], .snoc hTrace hRule, by simp⟩

theorem HasTrace.negSigma_l
    {top : Ordinal.{u}} {level arity code : Nat}
    {assignment : Tuple (StageCarrier top) arity}
    (hBody : (textbookAmbientTruthJudgmentOf_l false level code assignment).HasTrace top) :
    (textbookAmbientTruthJudgmentOf_l true level
      (textbookECode code 0 2) assignment).HasTrace top := by
  rcases hBody with ⟨trace, hTrace, hMember⟩
  exact hasTrace_of_rule_l hTrace (.negSigma level code assignment hMember)

theorem HasTrace.negPiFalse_l
    {top : Ordinal.{u}} {level arity code : Nat}
    {assignment : Tuple (StageCarrier top) arity}
    (hBody : (textbookAmbientTruthJudgmentOf_l true level code assignment).HasTrace top) :
    (textbookAmbientTruthJudgmentOf_l false level
      (textbookECode code 0 2) assignment).HasTrace top := by
  rcases hBody with ⟨trace, hTrace, hMember⟩
  exact hasTrace_of_rule_l hTrace (.negPiFalse level code assignment hMember)

theorem HasTrace.conjSigma_l
    {top : Ordinal.{u}} {level arity leftCode rightCode : Nat}
    {assignment : Tuple (StageCarrier top) arity}
    (hLeft : (textbookAmbientTruthJudgmentOf_l true level
      leftCode assignment).HasTrace top)
    (hRight : (textbookAmbientTruthJudgmentOf_l true level
      rightCode assignment).HasTrace top) :
    (textbookAmbientTruthJudgmentOf_l true level
      (textbookECode leftCode rightCode 3) assignment).HasTrace top := by
  rcases hLeft with ⟨leftTrace, hLeftTrace, hLeftMember⟩
  rcases hRight with ⟨rightTrace, hRightTrace, hRightMember⟩
  apply hasTrace_of_rule_l (hLeftTrace.append_l hRightTrace)
  exact .conjSigma level leftCode rightCode assignment
    (List.mem_append_left rightTrace hLeftMember)
    (List.mem_append_right leftTrace hRightMember)

theorem HasTrace.conjPiFalseLeft_l
    {top : Ordinal.{u}} {level arity leftCode rightCode : Nat}
    {assignment : Tuple (StageCarrier top) arity}
    (hLeft : (textbookAmbientTruthJudgmentOf_l false level
      leftCode assignment).HasTrace top)
    (hRight : TextbookBoundedIsPiCode_l level arity rightCode) :
    (textbookAmbientTruthJudgmentOf_l false level
      (textbookECode leftCode rightCode 3) assignment).HasTrace top := by
  rcases hLeft with ⟨trace, hTrace, hMember⟩
  exact hasTrace_of_rule_l hTrace
    (.conjPiFalseLeft level leftCode rightCode assignment hMember hRight)

theorem HasTrace.conjPiFalseRight_l
    {top : Ordinal.{u}} {level arity leftCode rightCode : Nat}
    {assignment : Tuple (StageCarrier top) arity}
    (hLeft : TextbookBoundedIsPiCode_l level arity leftCode)
    (hRight : (textbookAmbientTruthJudgmentOf_l false level
      rightCode assignment).HasTrace top) :
    (textbookAmbientTruthJudgmentOf_l false level
      (textbookECode leftCode rightCode 3) assignment).HasTrace top := by
  rcases hRight with ⟨trace, hTrace, hMember⟩
  exact hasTrace_of_rule_l hTrace
    (.conjPiFalseRight level leftCode rightCode assignment hLeft hMember)

theorem HasTrace.exSigma_l
    {top : Ordinal.{u}} {level arity code : Nat}
    {assignment : Tuple (StageCarrier top) arity}
    (witness : StageCarrier top)
    (hBody : (textbookAmbientTruthJudgmentOf_l true level code
      (snoc assignment witness)).HasTrace top) :
    (textbookAmbientTruthJudgmentOf_l true level
      (textbookECode code 0 4) assignment).HasTrace top := by
  rcases hBody with ⟨trace, hTrace, hMember⟩
  exact hasTrace_of_rule_l hTrace
    (.exSigma level code assignment witness hMember)

end TextbookAmbientTruthJudgment_l

private theorem textbookAmbientCertificateStep_hasTrace_l
    {top : Ordinal.{u}} {currentLevel lowerLevel : Nat} {hasLower : Prop}
    {lowerSigma : {arity : Nat} → Nat → Tuple (StageCarrier top) arity → Prop}
    {lowerPiFalse : {arity : Nat} → Nat → Tuple (StageCarrier top) arity → Prop}
    (hLowerSigmaTruth : ∀ {arity code : Nat}
      {assignment : Tuple (StageCarrier top) arity},
      hasLower → TextbookBoundedIsSigmaCode_l lowerLevel arity code →
      lowerSigma code assignment →
      (textbookAmbientTruthJudgmentOf_l true currentLevel code assignment).HasTrace top)
    (hLowerPiTruth : ∀ {arity code : Nat}
      {assignment : Tuple (StageCarrier top) arity},
      hasLower → TextbookBoundedIsPiCode_l lowerLevel arity code →
      (¬ lowerPiFalse code assignment) →
      (textbookAmbientTruthJudgmentOf_l true currentLevel code assignment).HasTrace top)
    (hLowerPiFalse : ∀ {arity code : Nat}
      {assignment : Tuple (StageCarrier top) arity},
      hasLower → TextbookBoundedIsPiCode_l lowerLevel arity code →
      lowerPiFalse code assignment →
      (textbookAmbientTruthJudgmentOf_l false currentLevel code assignment).HasTrace top)
    (hLowerSigmaFalse : ∀ {arity code : Nat}
      {assignment : Tuple (StageCarrier top) arity},
      hasLower → TextbookBoundedIsSigmaCode_l lowerLevel arity code →
      (¬ lowerSigma code assignment) →
      (textbookAmbientTruthJudgmentOf_l false currentLevel code assignment).HasTrace top)
    {mode : Bool} {arity code : Nat}
    {assignment : Tuple (StageCarrier top) arity}
    (hCertificate : TextbookAmbientCertificateStep_l top currentLevel lowerLevel
      hasLower lowerSigma lowerPiFalse mode code assignment) :
    (textbookAmbientTruthJudgmentOf_l mode currentLevel code assignment).HasTrace top := by
  induction hCertificate with
  | deltaSigma formula assignment hFormula =>
      exact TextbookAmbientTruthJudgment_l.hasTrace_of_rule_l .nil
        (.deltaSigma currentLevel formula assignment hFormula)
  | deltaPiFalse formula assignment hFormula =>
      exact TextbookAmbientTruthJudgment_l.hasTrace_of_rule_l .nil
        (.deltaPiFalse currentLevel formula assignment hFormula)
  | negSigma hBody ih => exact ih.negSigma_l
  | negPiFalse hBody ih => exact ih.negPiFalse_l
  | conjSigma hLeft hRight ihLeft ihRight => exact ihLeft.conjSigma_l ihRight
  | conjPiFalseLeft hLeft hRight ih => exact ih.conjPiFalseLeft_l hRight
  | conjPiFalseRight hLeft hRight ih => exact ih.conjPiFalseRight_l hLeft
  | exSigma witness hBody ih => exact ih.exSigma_l witness
  | lowerSigmaTruth hLower hCode hCertificate =>
      exact hLowerSigmaTruth hLower hCode hCertificate
  | lowerPiTruth hLower hCode hCertificate =>
      exact hLowerPiTruth hLower hCode hCertificate
  | lowerPiFalse hLower hCode hCertificate =>
      exact hLowerPiFalse hLower hCode hCertificate
  | lowerSigmaFalse hLower hCode hCertificate =>
      exact hLowerSigmaFalse hLower hCode hCertificate

/-- Every positive ambient certificate expands to a finite forward trace. -/
theorem textbookAmbientSigmaCertificate_hasTrace_l
    {top : Ordinal.{u}} {level arity code : Nat}
    {assignment : Tuple (StageCarrier top) arity}
    (hCertificate : TextbookAmbientSigmaCertificate_l top level code assignment) :
    (textbookAmbientTruthJudgmentOf_l true level code assignment).HasTrace top := by
  cases level with
  | zero =>
      exact textbookAmbientCertificateStep_hasTrace_l
        (fun hLower => False.elim hLower)
        (fun hLower => False.elim hLower)
        (fun hLower => False.elim hLower)
        (fun hLower => False.elim hLower) hCertificate
  | succ lowerLevel =>
      apply textbookAmbientCertificateStep_hasTrace_l
        (fun hLower hCode hLowerCertificate => ?_)
        (fun hLower hCode hLowerCertificate => ?_)
        (fun hLower hCode hLowerCertificate => ?_)
        (fun hLower hCode hLowerCertificate => ?_) hCertificate
      · exact TextbookAmbientTruthJudgment_l.hasTrace_of_rule_l .nil
          (.lowerSigmaTruth lowerLevel _ _ hCode hLowerCertificate)
      · exact TextbookAmbientTruthJudgment_l.hasTrace_of_rule_l .nil
          (.lowerPiTruth lowerLevel _ _ hCode hLowerCertificate)
      · exact TextbookAmbientTruthJudgment_l.hasTrace_of_rule_l .nil
          (.lowerPiFalse lowerLevel _ _ hCode hLowerCertificate)
      · exact TextbookAmbientTruthJudgment_l.hasTrace_of_rule_l .nil
          (.lowerSigmaFalse lowerLevel _ _ hCode hLowerCertificate)

/-- Every negative ambient certificate expands to a finite forward trace. -/
theorem textbookAmbientPiFalseCertificate_hasTrace_l
    {top : Ordinal.{u}} {level arity code : Nat}
    {assignment : Tuple (StageCarrier top) arity}
    (hCertificate : TextbookAmbientPiFalseCertificate_l top level code assignment) :
    (textbookAmbientTruthJudgmentOf_l false level code assignment).HasTrace top := by
  cases level with
  | zero =>
      exact textbookAmbientCertificateStep_hasTrace_l
        (fun hLower => False.elim hLower)
        (fun hLower => False.elim hLower)
        (fun hLower => False.elim hLower)
        (fun hLower => False.elim hLower) hCertificate
  | succ lowerLevel =>
      apply textbookAmbientCertificateStep_hasTrace_l
        (fun hLower hCode hLowerCertificate => ?_)
        (fun hLower hCode hLowerCertificate => ?_)
        (fun hLower hCode hLowerCertificate => ?_)
        (fun hLower hCode hLowerCertificate => ?_) hCertificate
      · exact TextbookAmbientTruthJudgment_l.hasTrace_of_rule_l .nil
          (.lowerSigmaTruth lowerLevel _ _ hCode hLowerCertificate)
      · exact TextbookAmbientTruthJudgment_l.hasTrace_of_rule_l .nil
          (.lowerPiTruth lowerLevel _ _ hCode hLowerCertificate)
      · exact TextbookAmbientTruthJudgment_l.hasTrace_of_rule_l .nil
          (.lowerPiFalse lowerLevel _ _ hCode hLowerCertificate)
      · exact TextbookAmbientTruthJudgment_l.hasTrace_of_rule_l .nil
          (.lowerSigmaFalse lowerLevel _ _ hCode hLowerCertificate)

/-- Every row of an indexed ambient truth trace carries the intended certificate. -/
theorem textbookAmbientTruthTraceValid_certified_l
    {top : Ordinal.{u}}
    {trace : List TextbookAmbientTruthJudgment_l.{u}}
    (hTrace : TextbookAmbientTruthTraceValid_l top trace)
    (index : Fin trace.length) :
    (trace.get index).Certified top := by
  have hAll : ∀ position (hPosition : position < trace.length),
      (trace.get ⟨position, hPosition⟩).Certified top := by
    intro position
    induction position using Nat.strong_induction_on with
    | h position ih =>
        intro hPosition
        apply textbookAmbientTruthRuleOver_sound_l ?_
          (hTrace ⟨position, hPosition⟩)
        intro child hChild
        obtain ⟨prior, hPrior⟩ := List.mem_iff_get.mp hChild
        have hPriorPosition : prior.1 < position := by
          have hPriorBound := prior.2
          simp only [List.length_take] at hPriorBound
          omega
        have hPriorTrace : trace.get ⟨prior.1,
            hPriorPosition.trans hPosition⟩ = child := by
          simpa only [List.get_eq_getElem, List.getElem_take] using hPrior
        rw [← hPriorTrace]
        exact ih prior.1 hPriorPosition (hPriorPosition.trans hPosition)
  exact hAll index.1 index.2

/-- Canonical row certification is equivalent to existence of a finite trace. -/
theorem textbookAmbientTruthJudgmentOf_certified_iff_hasTrace_l
    {top : Ordinal.{u}} (isSigma : Bool) (level code : Nat)
    {arity : Nat} (assignment : Tuple (StageCarrier top) arity) :
    (textbookAmbientTruthJudgmentOf_l isSigma level code assignment).Certified top ↔
      (textbookAmbientTruthJudgmentOf_l isSigma level code assignment).HasTrace top := by
  rw [textbookAmbientTruthJudgmentOf_certified_iff_l]
  cases isSigma
  · constructor
    · exact textbookAmbientPiFalseCertificate_hasTrace_l
    · rintro ⟨trace, hBuilt, hMember⟩
      obtain ⟨index, hIndex⟩ := List.mem_iff_get.mp hMember
      have hCertified := textbookAmbientTruthTraceValid_certified_l
        hBuilt.valid_l index
      rw [hIndex, textbookAmbientTruthJudgmentOf_certified_iff_l] at hCertified
      exact hCertified
  · constructor
    · exact textbookAmbientSigmaCertificate_hasTrace_l
    · rintro ⟨trace, hBuilt, hMember⟩
      obtain ⟨index, hIndex⟩ := List.mem_iff_get.mp hMember
      have hCertified := textbookAmbientTruthTraceValid_certified_l
        hBuilt.valid_l index
      rw [hIndex, textbookAmbientTruthJudgmentOf_certified_iff_l] at hCertified
      exact hCertified

end YesMetaZFC.BMS.ConstructibleBridge
