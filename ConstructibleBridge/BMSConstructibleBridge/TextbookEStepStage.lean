import BMSConstructibleBridge.TextbookEStepOperationsStage

/-!
# textbook E 单步公式在局部可构造层中的语义

本模块把各个集合操作的局部层绝对性组装为五个构造器分支，最后得到
`textbookEStepFormula` 的精确局部层语义。
-/

open Set

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible
open Constructible.FiniteSequenceZF

noncomputable section

/-! ## 两个原子分支 -/

/-- 成员原子构造器分支在局部层中的精确语义。 -/
theorem satisfiesIn_stepBranchZero_stage_standard_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    {a key history output : ZFSet.{u}}
    (ha : a ∈ LStageZF θ) (hkey : key ∈ LStageZF θ)
    (hhistory : history ∈ LStageZF θ) (houtput : output ∈ LStageZF θ)
    (m n : Nat) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        Constructible.TextbookEFormula.stepBranchZero
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n] ↔
      ∃ i j : Nat, m = Constructible.textbookECode i j 0 ∧ i < n ∧ j < n ∧
        output = Constructible.textbookDInCodeZF a
          (natCode n) (natCode i) (natCode j) := by
  rw [Constructible.TextbookEFormula.stepBranchZero]
  simp only [Constructible.Model.SatisfiesIn]
  let base : Tuple ZFSet.{u} 7 :=
    ![a, key, history, output,
      (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n]
  have hassign (iSet jSet tagSet : ZFSet.{u}) :
      snoc (snoc (snoc base iSet) jSet) tagSet =
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet] := by
    funext position
    fin_cases position <;> rfl
  constructor
  · rintro ⟨iSet, hiSet, jSet, hjSet, tagSet, htagSet, hguard, hvalue⟩
    rw [hassign] at hguard hvalue
    rcases exists_natCode_fields_of_satisfiesIn_codeGuardBody_stage_l
      hθ hω ha hkey hhistory houtput hiSet hjSet htagSet
      0 true m n hguard with
      ⟨i, j, hiEq, hjEq, htagEq, hcode, hi, hj⟩
    subst iSet
    subst jSet
    subst tagSet
    have hvalueEq : output = Constructible.textbookDInCodeZF a
        (natCode n) (natCode i) (natCode j) := by
      rw [satisfiesIn_formula5At_stage_iff_l] at hvalue
      have h := (satisfiesIn_dInOutputFormula_stage_natCode_iff_l
        hθ hω n i j ha houtput).mp (by simpa using hvalue)
      simpa only [Constructible.textbookDInCodeZF_natCode] using h
    exact ⟨i, j, hcode, hi, hj, hvalueEq⟩
  · rintro ⟨i, j, hcode, hi, hj, hvalue⟩
    refine ⟨(natCode i : ZFSet.{u}), natCode_mem_stage_l hω i,
      (natCode j : ZFSet.{u}), natCode_mem_stage_l hω j,
      (natCode 0 : ZFSet.{u}), natCode_mem_stage_l hω 0, ?_, ?_⟩
    · rw [hassign]
      exact (satisfiesIn_codeGuardBody_stage_natCode_iff_l
        hθ hω 0 true ha hkey hhistory houtput m n i j).mpr
          ⟨hcode, hi, hj⟩
    · rw [hassign, satisfiesIn_formula5At_stage_iff_l]
      apply (satisfiesIn_dInOutputFormula_stage_natCode_iff_l
        hθ hω n i j ha houtput).mpr
      simpa only [Constructible.textbookDInCodeZF_natCode] using hvalue

/-- 相等原子构造器分支在局部层中的精确语义。 -/
theorem satisfiesIn_stepBranchOne_stage_standard_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    {a key history output : ZFSet.{u}}
    (ha : a ∈ LStageZF θ) (hkey : key ∈ LStageZF θ)
    (hhistory : history ∈ LStageZF θ) (houtput : output ∈ LStageZF θ)
    (m n : Nat) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        Constructible.TextbookEFormula.stepBranchOne
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n] ↔
      ∃ i j : Nat, m = Constructible.textbookECode i j 1 ∧ i < n ∧ j < n ∧
        output = Constructible.textbookDEqCodeZF a
          (natCode n) (natCode i) (natCode j) := by
  rw [Constructible.TextbookEFormula.stepBranchOne]
  simp only [Constructible.Model.SatisfiesIn]
  let base : Tuple ZFSet.{u} 7 :=
    ![a, key, history, output,
      (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n]
  have hassign (iSet jSet tagSet : ZFSet.{u}) :
      snoc (snoc (snoc base iSet) jSet) tagSet =
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet] := by
    funext position
    fin_cases position <;> rfl
  constructor
  · rintro ⟨iSet, hiSet, jSet, hjSet, tagSet, htagSet, hguard, hvalue⟩
    rw [hassign] at hguard hvalue
    rcases exists_natCode_fields_of_satisfiesIn_codeGuardBody_stage_l
      hθ hω ha hkey hhistory houtput hiSet hjSet htagSet
      1 true m n hguard with
      ⟨i, j, hiEq, hjEq, htagEq, hcode, hi, hj⟩
    subst iSet
    subst jSet
    subst tagSet
    have hvalueEq : output = Constructible.textbookDEqCodeZF a
        (natCode n) (natCode i) (natCode j) := by
      rw [satisfiesIn_formula5At_stage_iff_l] at hvalue
      have h := (satisfiesIn_dEqOutputFormula_stage_natCode_iff_l
        hθ hω n i j ha houtput).mp (by simpa using hvalue)
      simpa only [Constructible.textbookDEqCodeZF_natCode] using h
    exact ⟨i, j, hcode, hi, hj, hvalueEq⟩
  · rintro ⟨i, j, hcode, hi, hj, hvalue⟩
    refine ⟨(natCode i : ZFSet.{u}), natCode_mem_stage_l hω i,
      (natCode j : ZFSet.{u}), natCode_mem_stage_l hω j,
      (natCode 1 : ZFSet.{u}), natCode_mem_stage_l hω 1, ?_, ?_⟩
    · rw [hassign]
      exact (satisfiesIn_codeGuardBody_stage_natCode_iff_l
        hθ hω 1 true ha hkey hhistory houtput m n i j).mpr
          ⟨hcode, hi, hj⟩
    · rw [hassign, satisfiesIn_formula5At_stage_iff_l]
      apply (satisfiesIn_dEqOutputFormula_stage_natCode_iff_l
        hθ hω n i j ha houtput).mpr
      simpa only [Constructible.textbookDEqCodeZF_natCode] using hvalue

/-! ## 相对补分支 -/

/-- 相对补构造器分支在局部层中的精确语义。 -/
theorem satisfiesIn_stepBranchTwo_stage_standard_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    {a key history output : ZFSet.{u}}
    (ha : a ∈ LStageZF θ) (hkey : key ∈ LStageZF θ)
    (hhistory : history ∈ LStageZF θ) (houtput : output ∈ LStageZF θ)
    (m n : Nat) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        Constructible.TextbookEFormula.stepBranchTwo
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n] ↔
      ∃ i j : Nat, m = Constructible.textbookECode i j 2 ∧
        output = Constructible.relativeDifferenceZF
          (ZFSet.funs (natCode n) a)
          (Constructible.uniqueGraphLookupZF history
            (ZFSet.pair (natCode i) (natCode n))) := by
  rw [Constructible.TextbookEFormula.stepBranchTwo]
  simp only [Constructible.Model.SatisfiesIn]
  let base : Tuple ZFSet.{u} 7 :=
    ![a, key, history, output,
      (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n]
  have hfields (iSet jSet tagSet : ZFSet.{u}) :
      snoc (snoc (snoc base iSet) jSet) tagSet =
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet] := by
    funext position
    fin_cases position <;> rfl
  have hkeyAssignment (iSet jSet tagSet lookupKey : ZFSet.{u}) :
      snoc ![a, key, history, output,
        (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
        iSet, jSet, tagSet] lookupKey =
      ![a, key, history, output,
        (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
        iSet, jSet, tagSet, lookupKey] := by
    funext position
    fin_cases position <;> rfl
  have hremovedAssignment
      (iSet jSet tagSet lookupKey removed : ZFSet.{u}) :
      snoc ![a, key, history, output,
        (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
        iSet, jSet, tagSet, lookupKey] removed =
      ![a, key, history, output,
        (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
        iSet, jSet, tagSet, lookupKey, removed] := by
    funext position
    fin_cases position <;> rfl
  have hspaceAssignment
      (iSet jSet tagSet lookupKey removed space : ZFSet.{u}) :
      snoc ![a, key, history, output,
        (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
        iSet, jSet, tagSet, lookupKey, removed] space =
      ![a, key, history, output,
        (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
        iSet, jSet, tagSet, lookupKey, removed, space] := by
    funext position
    fin_cases position <;> rfl
  constructor
  · rintro ⟨iSet, hiSet, jSet, hjSet, tagSet, htagSet, hguard,
      lookupKey, hlookupKeyStage, hpair, removed, hremovedStage, hlookup,
      space, hspaceStage, hspaceFormula, hdifference⟩
    rw [hfields] at hguard hpair hlookup hspaceFormula hdifference
    rw [hkeyAssignment] at hpair hlookup hspaceFormula hdifference
    rw [hremovedAssignment] at hlookup hspaceFormula hdifference
    rw [hspaceAssignment] at hspaceFormula hdifference
    rcases exists_natCode_fields_of_satisfiesIn_codeGuardBody_stage_l
      hθ hω ha hkey hhistory houtput hiSet hjSet htagSet
      2 false m n hguard with
      ⟨i, j, hiEq, hjEq, htagEq, hcode, _htrivial⟩
    subst iSet
    subst jSet
    subst tagSet
    have hpairAssignment : ∀ position : Fin 11,
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          natCode i, natCode j, natCode 2, lookupKey] position ∈
            LStageZF θ := by
      intro position
      fin_cases position <;>
        first
          | exact omega_toZFSet_mem_stage_l hω
          | exact natCode_mem_stage_l hω _
          | assumption
    have hlookupKey : lookupKey = ZFSet.pair (natCode i) (natCode n) :=
      (satisfiesIn_kuratowskiPairEqAt_stage_iff_l
        (Fin.last 10) (7 : Fin 11) (6 : Fin 11) _ hpairAssignment).mp hpair
    subst lookupKey
    have hremoved : removed = Constructible.uniqueGraphLookupZF history
        (ZFSet.pair (natCode i) (natCode n)) := by
      rw [satisfiesIn_formula3At_stage_iff_l] at hlookup
      exact (satisfiesIn_uniqueGraphLookupFormula_stage_iff_l hθ
        hhistory hlookupKeyStage hremovedStage).mp (by simpa using hlookup)
    subst removed
    have hspaceValue : space = ZFSet.funs (natCode n) a := by
      rw [satisfiesIn_formula3At_stage_iff_l] at hspaceFormula
      exact (satisfiesIn_finiteFunctionSpaceGraph_stage_natCode_iff_l
        hθ hω n ha hspaceStage).mp (by simpa using hspaceFormula)
    subst space
    have hvalue : output = Constructible.relativeDifferenceZF
        (ZFSet.funs (natCode n) a)
        (Constructible.uniqueGraphLookupZF history
          (ZFSet.pair (natCode i) (natCode n))) := by
      rw [satisfiesIn_formula3At_stage_iff_l] at hdifference
      exact (satisfiesIn_relativeDifferenceOutputFormula_stage_iff_l
        hspaceStage hremovedStage houtput).mp (by simpa using hdifference)
    exact ⟨i, j, hcode, hvalue⟩
  · rintro ⟨i, j, hcode, hvalue⟩
    let lookupKey : ZFSet.{u} := ZFSet.pair (natCode i) (natCode n)
    have hlookupKeyStage : lookupKey ∈ LStageZF θ :=
      orderedPair_mem_LStageZF_of_isSuccLimit hθ
        (natCode_mem_stage_l hω i) (natCode_mem_stage_l hω n)
    let removed : ZFSet.{u} :=
      Constructible.uniqueGraphLookupZF history lookupKey
    have hremovedStage : removed ∈ LStageZF θ :=
      uniqueGraphLookupZF_mem_LStageZF_l hθ hhistory hlookupKeyStage
    let space : ZFSet.{u} := ZFSet.funs (natCode n) a
    have hspaceStage : space ∈ LStageZF θ := by
      simpa [space, Constructible.textbookTupleSpace] using
        textbookTupleSpace_mem_LStageZF_l hθ ha n
    refine ⟨(natCode i : ZFSet.{u}), natCode_mem_stage_l hω i,
      (natCode j : ZFSet.{u}), natCode_mem_stage_l hω j,
      (natCode 2 : ZFSet.{u}), natCode_mem_stage_l hω 2, ?_,
      lookupKey, hlookupKeyStage, ?_, removed, hremovedStage, ?_,
      space, hspaceStage, ?_, ?_⟩
    · rw [hfields]
      exact (satisfiesIn_codeGuardBody_stage_natCode_iff_l
        hθ hω 2 false ha hkey hhistory houtput m n i j).mpr
          ⟨hcode, trivial⟩
    · rw [hfields, hkeyAssignment]
      apply (satisfiesIn_kuratowskiPairEqAt_stage_iff_l
        (Fin.last 10) (7 : Fin 11) (6 : Fin 11) _ (by
          intro position
          fin_cases position <;>
            first
              | exact omega_toZFSet_mem_stage_l hω
              | exact natCode_mem_stage_l hω _
              | assumption)).mpr
      rfl
    · rw [hfields, hkeyAssignment, hremovedAssignment,
        satisfiesIn_formula3At_stage_iff_l]
      exact (satisfiesIn_uniqueGraphLookupFormula_stage_iff_l hθ
        hhistory hlookupKeyStage hremovedStage).mpr rfl
    · rw [hfields, hkeyAssignment, hremovedAssignment,
        hspaceAssignment, satisfiesIn_formula3At_stage_iff_l]
      exact (satisfiesIn_finiteFunctionSpaceGraph_stage_natCode_iff_l
        hθ hω n ha hspaceStage).mpr rfl
    · rw [hfields, hkeyAssignment, hremovedAssignment,
        hspaceAssignment, satisfiesIn_formula3At_stage_iff_l]
      apply (satisfiesIn_relativeDifferenceOutputFormula_stage_iff_l
        hspaceStage hremovedStage houtput).mpr
      simpa [space, removed, lookupKey] using hvalue

/-! ## 交集分支 -/

/-- 交集构造器分支在局部层中的精确语义。 -/
theorem satisfiesIn_stepBranchThree_stage_standard_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    {a key history output : ZFSet.{u}}
    (ha : a ∈ LStageZF θ) (hkey : key ∈ LStageZF θ)
    (hhistory : history ∈ LStageZF θ) (houtput : output ∈ LStageZF θ)
    (m n : Nat) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        Constructible.TextbookEFormula.stepBranchThree
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n] ↔
      ∃ i j : Nat, m = Constructible.textbookECode i j 3 ∧
        output = Constructible.intersectionZF
          (Constructible.uniqueGraphLookupZF history
            (ZFSet.pair (natCode i) (natCode n)))
          (Constructible.uniqueGraphLookupZF history
            (ZFSet.pair (natCode j) (natCode n))) := by
  rw [Constructible.TextbookEFormula.stepBranchThree]
  simp only [Constructible.Model.SatisfiesIn]
  let base : Tuple ZFSet.{u} 7 :=
    ![a, key, history, output,
      (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n]
  have hfields (iSet jSet tagSet : ZFSet.{u}) :
      snoc (snoc (snoc base iSet) jSet) tagSet =
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet] := by
    funext position
    fin_cases position <;> rfl
  have hleftKeyAssignment (iSet jSet tagSet leftKey : ZFSet.{u}) :
      snoc ![a, key, history, output,
        (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
        iSet, jSet, tagSet] leftKey =
      ![a, key, history, output,
        (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
        iSet, jSet, tagSet, leftKey] := by
    funext position
    fin_cases position <;> rfl
  have hleftValueAssignment
      (iSet jSet tagSet leftKey leftValue : ZFSet.{u}) :
      snoc ![a, key, history, output,
        (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
        iSet, jSet, tagSet, leftKey] leftValue =
      ![a, key, history, output,
        (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
        iSet, jSet, tagSet, leftKey, leftValue] := by
    funext position
    fin_cases position <;> rfl
  have hrightKeyAssignment
      (iSet jSet tagSet leftKey leftValue rightKey : ZFSet.{u}) :
      snoc ![a, key, history, output,
        (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
        iSet, jSet, tagSet, leftKey, leftValue] rightKey =
      ![a, key, history, output,
        (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
        iSet, jSet, tagSet, leftKey, leftValue, rightKey] := by
    funext position
    fin_cases position <;> rfl
  have hrightValueAssignment
      (iSet jSet tagSet leftKey leftValue rightKey rightValue : ZFSet.{u}) :
      snoc ![a, key, history, output,
        (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
        iSet, jSet, tagSet, leftKey, leftValue, rightKey] rightValue =
      ![a, key, history, output,
        (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
        iSet, jSet, tagSet, leftKey, leftValue, rightKey, rightValue] := by
    funext position
    fin_cases position <;> rfl
  constructor
  · rintro ⟨iSet, hiSet, jSet, hjSet, tagSet, htagSet, hguard,
      leftKey, hleftKeyStage, hleftPair,
      leftValue, hleftValueStage, hleftLookup,
      rightKey, hrightKeyStage, hrightPair,
      rightValue, hrightValueStage, hrightLookup, hintersection⟩
    rw [hfields] at hguard hleftPair hleftLookup hrightPair hrightLookup hintersection
    rw [hleftKeyAssignment] at hleftPair hleftLookup hrightPair hrightLookup hintersection
    rw [hleftValueAssignment] at hleftLookup hrightPair hrightLookup hintersection
    rw [hrightKeyAssignment] at hrightPair hrightLookup hintersection
    rw [hrightValueAssignment] at hrightLookup hintersection
    rcases exists_natCode_fields_of_satisfiesIn_codeGuardBody_stage_l
      hθ hω ha hkey hhistory houtput hiSet hjSet htagSet
      3 false m n hguard with
      ⟨i, j, hiEq, hjEq, htagEq, hcode, _htrivial⟩
    subst iSet
    subst jSet
    subst tagSet
    have hleftAssignment : ∀ position : Fin 11,
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          natCode i, natCode j, natCode 3, leftKey] position ∈
            LStageZF θ := by
      intro position
      fin_cases position <;>
        first
          | exact omega_toZFSet_mem_stage_l hω
          | exact natCode_mem_stage_l hω _
          | assumption
    have hleftKey : leftKey = ZFSet.pair (natCode i) (natCode n) :=
      (satisfiesIn_kuratowskiPairEqAt_stage_iff_l
        (Fin.last 10) (7 : Fin 11) (6 : Fin 11) _ hleftAssignment).mp
        hleftPair
    subst leftKey
    have hleftValue : leftValue = Constructible.uniqueGraphLookupZF history
        (ZFSet.pair (natCode i) (natCode n)) := by
      rw [satisfiesIn_formula3At_stage_iff_l] at hleftLookup
      exact (satisfiesIn_uniqueGraphLookupFormula_stage_iff_l hθ
        hhistory hleftKeyStage hleftValueStage).mp (by simpa using hleftLookup)
    subst leftValue
    have hrightAssignment : ∀ position : Fin 13,
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          natCode i, natCode j, natCode 3,
          ZFSet.pair (natCode i) (natCode n),
          Constructible.uniqueGraphLookupZF history
            (ZFSet.pair (natCode i) (natCode n)), rightKey] position ∈
              LStageZF θ := by
      intro position
      fin_cases position <;>
        first
          | exact omega_toZFSet_mem_stage_l hω
          | exact natCode_mem_stage_l hω _
          | assumption
    have hrightKey : rightKey = ZFSet.pair (natCode j) (natCode n) :=
      (satisfiesIn_kuratowskiPairEqAt_stage_iff_l
        (Fin.last 12) (8 : Fin 13) (6 : Fin 13) _ hrightAssignment).mp
        hrightPair
    subst rightKey
    have hrightValue : rightValue = Constructible.uniqueGraphLookupZF history
        (ZFSet.pair (natCode j) (natCode n)) := by
      rw [satisfiesIn_formula3At_stage_iff_l] at hrightLookup
      exact (satisfiesIn_uniqueGraphLookupFormula_stage_iff_l hθ
        hhistory hrightKeyStage hrightValueStage).mp (by simpa using hrightLookup)
    subst rightValue
    have hvalue : output = Constructible.intersectionZF
        (Constructible.uniqueGraphLookupZF history
          (ZFSet.pair (natCode i) (natCode n)))
        (Constructible.uniqueGraphLookupZF history
          (ZFSet.pair (natCode j) (natCode n))) := by
      rw [satisfiesIn_formula3At_stage_iff_l] at hintersection
      exact (satisfiesIn_intersectionOutputFormula_stage_iff_l
        hleftValueStage hrightValueStage houtput).mp
          (by simpa using hintersection)
    exact ⟨i, j, hcode, hvalue⟩
  · rintro ⟨i, j, hcode, hvalue⟩
    let leftKey : ZFSet.{u} := ZFSet.pair (natCode i) (natCode n)
    have hleftKeyStage : leftKey ∈ LStageZF θ :=
      orderedPair_mem_LStageZF_of_isSuccLimit hθ
        (natCode_mem_stage_l hω i) (natCode_mem_stage_l hω n)
    let leftValue : ZFSet.{u} :=
      Constructible.uniqueGraphLookupZF history leftKey
    have hleftValueStage : leftValue ∈ LStageZF θ :=
      uniqueGraphLookupZF_mem_LStageZF_l hθ hhistory hleftKeyStage
    let rightKey : ZFSet.{u} := ZFSet.pair (natCode j) (natCode n)
    have hrightKeyStage : rightKey ∈ LStageZF θ :=
      orderedPair_mem_LStageZF_of_isSuccLimit hθ
        (natCode_mem_stage_l hω j) (natCode_mem_stage_l hω n)
    let rightValue : ZFSet.{u} :=
      Constructible.uniqueGraphLookupZF history rightKey
    have hrightValueStage : rightValue ∈ LStageZF θ :=
      uniqueGraphLookupZF_mem_LStageZF_l hθ hhistory hrightKeyStage
    refine ⟨(natCode i : ZFSet.{u}), natCode_mem_stage_l hω i,
      (natCode j : ZFSet.{u}), natCode_mem_stage_l hω j,
      (natCode 3 : ZFSet.{u}), natCode_mem_stage_l hω 3, ?_,
      leftKey, hleftKeyStage, ?_, leftValue, hleftValueStage, ?_,
      rightKey, hrightKeyStage, ?_, rightValue, hrightValueStage, ?_, ?_⟩
    · rw [hfields]
      exact (satisfiesIn_codeGuardBody_stage_natCode_iff_l
        hθ hω 3 false ha hkey hhistory houtput m n i j).mpr
          ⟨hcode, trivial⟩
    · rw [hfields, hleftKeyAssignment]
      apply (satisfiesIn_kuratowskiPairEqAt_stage_iff_l
        (Fin.last 10) (7 : Fin 11) (6 : Fin 11) _ (by
          intro position
          fin_cases position <;>
            first
              | exact omega_toZFSet_mem_stage_l hω
              | exact natCode_mem_stage_l hω _
              | assumption)).mpr
      rfl
    · rw [hfields, hleftKeyAssignment, hleftValueAssignment,
        satisfiesIn_formula3At_stage_iff_l]
      exact (satisfiesIn_uniqueGraphLookupFormula_stage_iff_l hθ
        hhistory hleftKeyStage hleftValueStage).mpr rfl
    · rw [hfields, hleftKeyAssignment, hleftValueAssignment,
        hrightKeyAssignment]
      apply (satisfiesIn_kuratowskiPairEqAt_stage_iff_l
        (Fin.last 12) (8 : Fin 13) (6 : Fin 13) _ (by
          intro position
          fin_cases position <;>
            first
              | exact omega_toZFSet_mem_stage_l hω
              | exact natCode_mem_stage_l hω _
              | assumption)).mpr
      rfl
    · rw [hfields, hleftKeyAssignment, hleftValueAssignment,
        hrightKeyAssignment, hrightValueAssignment,
        satisfiesIn_formula3At_stage_iff_l]
      exact (satisfiesIn_uniqueGraphLookupFormula_stage_iff_l hθ
        hhistory hrightKeyStage hrightValueStage).mpr rfl
    · rw [hfields, hleftKeyAssignment, hleftValueAssignment,
        hrightKeyAssignment, hrightValueAssignment,
        satisfiesIn_formula3At_stage_iff_l]
      apply (satisfiesIn_intersectionOutputFormula_stage_iff_l
        hleftValueStage hrightValueStage houtput).mpr
      simpa [leftValue, leftKey, rightValue, rightKey] using hvalue

/-! ## 存在投影分支 -/

/-- 存在投影构造器分支在局部层中的精确语义。 -/
theorem satisfiesIn_stepBranchFour_stage_standard_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    {a key history output : ZFSet.{u}}
    (ha : a ∈ LStageZF θ) (hkey : key ∈ LStageZF θ)
    (hhistory : history ∈ LStageZF θ) (houtput : output ∈ LStageZF θ)
    (m n : Nat) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        Constructible.TextbookEFormula.stepBranchFour
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n] ↔
      ∃ i j : Nat, m = Constructible.textbookECode i j 4 ∧
        output = Constructible.textbookExistsProjCodeZF a (natCode n)
          (Constructible.uniqueGraphLookupZF history
            (ZFSet.pair (natCode i) (natCode (n + 1)))) := by
  rw [Constructible.TextbookEFormula.stepBranchFour]
  simp only [Constructible.Model.SatisfiesIn]
  let base : Tuple ZFSet.{u} 7 :=
    ![a, key, history, output,
      (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n]
  have hfields (iSet jSet tagSet : ZFSet.{u}) :
      snoc (snoc (snoc base iSet) jSet) tagSet =
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet] := by
    funext position
    fin_cases position <;> rfl
  have hsuccAssignment (iSet jSet tagSet succN : ZFSet.{u}) :
      snoc ![a, key, history, output,
        (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
        iSet, jSet, tagSet] succN =
      ![a, key, history, output,
        (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
        iSet, jSet, tagSet, succN] := by
    funext position
    fin_cases position <;> rfl
  have hkeyAssignment
      (iSet jSet tagSet succN lookupKey : ZFSet.{u}) :
      snoc ![a, key, history, output,
        (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
        iSet, jSet, tagSet, succN] lookupKey =
      ![a, key, history, output,
        (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
        iSet, jSet, tagSet, succN, lookupKey] := by
    funext position
    fin_cases position <;> rfl
  have hrelationAssignment
      (iSet jSet tagSet succN lookupKey relation : ZFSet.{u}) :
      snoc ![a, key, history, output,
        (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
        iSet, jSet, tagSet, succN, lookupKey] relation =
      ![a, key, history, output,
        (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
        iSet, jSet, tagSet, succN, lookupKey, relation] := by
    funext position
    fin_cases position <;> rfl
  constructor
  · rintro ⟨iSet, hiSet, jSet, hjSet, tagSet, htagSet, hguard,
      succN, hsuccStage, hsucc, lookupKey, hlookupKeyStage, hpair,
      relation, hrelationStage, hlookup, hprojection⟩
    rw [hfields] at hguard hsucc hpair hlookup hprojection
    rw [hsuccAssignment] at hsucc hpair hlookup hprojection
    rw [hkeyAssignment] at hpair hlookup hprojection
    rw [hrelationAssignment] at hlookup hprojection
    rcases exists_natCode_fields_of_satisfiesIn_codeGuardBody_stage_l
      hθ hω ha hkey hhistory houtput hiSet hjSet htagSet
      4 false m n hguard with
      ⟨i, j, hiEq, hjEq, htagEq, hcode, _htrivial⟩
    subst iSet
    subst jSet
    subst tagSet
    have hsuccArgs : ∀ position : Fin 11,
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          natCode i, natCode j, natCode 4, succN] position ∈
            LStageZF θ := by
      intro position
      fin_cases position <;>
        first
          | exact omega_toZFSet_mem_stage_l hω
          | exact natCode_mem_stage_l hω _
          | assumption
    have hsuccN : succN = (natCode (n + 1) : ZFSet.{u}) := by
      have h := (satisfiesIn_successorAt_stage_iff_l
        (Fin.last 10) (6 : Fin 11) _ hsuccArgs).mp hsucc
      simpa [natCode_succ_eq_insert] using h
    subst succN
    have hpairArgs : ∀ position : Fin 12,
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          natCode i, natCode j, natCode 4, natCode (n + 1), lookupKey]
            position ∈ LStageZF θ := by
      intro position
      fin_cases position <;>
        first
          | exact omega_toZFSet_mem_stage_l hω
          | exact natCode_mem_stage_l hω _
          | assumption
    have hlookupKey : lookupKey =
        ZFSet.pair (natCode i) (natCode (n + 1)) :=
      (satisfiesIn_kuratowskiPairEqAt_stage_iff_l
        (Fin.last 11) (7 : Fin 12) (10 : Fin 12) _ hpairArgs).mp hpair
    subst lookupKey
    have hrelation : relation = Constructible.uniqueGraphLookupZF history
        (ZFSet.pair (natCode i) (natCode (n + 1))) := by
      rw [satisfiesIn_formula3At_stage_iff_l] at hlookup
      exact (satisfiesIn_uniqueGraphLookupFormula_stage_iff_l hθ
        hhistory hlookupKeyStage hrelationStage).mp (by simpa using hlookup)
    subst relation
    have hvalue : output = Constructible.textbookExistsProjCodeZF a
        (natCode n) (Constructible.uniqueGraphLookupZF history
          (ZFSet.pair (natCode i) (natCode (n + 1)))) := by
      rw [satisfiesIn_formula4At_stage_iff_l] at hprojection
      exact (satisfiesIn_existsProjOutputFormula_stage_natCode_iff_l
        hθ hω n ha hrelationStage houtput).mp (by simpa using hprojection)
    exact ⟨i, j, hcode, hvalue⟩
  · rintro ⟨i, j, hcode, hvalue⟩
    let succN : ZFSet.{u} := natCode (n + 1)
    have hsuccStage : succN ∈ LStageZF θ := natCode_mem_stage_l hω (n + 1)
    let lookupKey : ZFSet.{u} := ZFSet.pair (natCode i) succN
    have hlookupKeyStage : lookupKey ∈ LStageZF θ :=
      orderedPair_mem_LStageZF_of_isSuccLimit hθ
        (natCode_mem_stage_l hω i) hsuccStage
    let relation : ZFSet.{u} :=
      Constructible.uniqueGraphLookupZF history lookupKey
    have hrelationStage : relation ∈ LStageZF θ :=
      uniqueGraphLookupZF_mem_LStageZF_l hθ hhistory hlookupKeyStage
    refine ⟨(natCode i : ZFSet.{u}), natCode_mem_stage_l hω i,
      (natCode j : ZFSet.{u}), natCode_mem_stage_l hω j,
      (natCode 4 : ZFSet.{u}), natCode_mem_stage_l hω 4, ?_,
      succN, hsuccStage, ?_, lookupKey, hlookupKeyStage, ?_,
      relation, hrelationStage, ?_, ?_⟩
    · rw [hfields]
      exact (satisfiesIn_codeGuardBody_stage_natCode_iff_l
        hθ hω 4 false ha hkey hhistory houtput m n i j).mpr
          ⟨hcode, trivial⟩
    · rw [hfields, hsuccAssignment]
      apply (satisfiesIn_successorAt_stage_iff_l
        (Fin.last 10) (6 : Fin 11) _ (by
          intro position
          fin_cases position <;>
            first
              | exact omega_toZFSet_mem_stage_l hω
              | exact natCode_mem_stage_l hω _
              | assumption)).mpr
      simp [succN, natCode_succ_eq_insert]
    · rw [hfields, hsuccAssignment, hkeyAssignment]
      apply (satisfiesIn_kuratowskiPairEqAt_stage_iff_l
        (Fin.last 11) (7 : Fin 12) (10 : Fin 12) _ (by
          intro position
          fin_cases position <;>
            first
              | exact omega_toZFSet_mem_stage_l hω
              | exact natCode_mem_stage_l hω _
              | assumption)).mpr
      rfl
    · rw [hfields, hsuccAssignment, hkeyAssignment,
        hrelationAssignment, satisfiesIn_formula3At_stage_iff_l]
      exact (satisfiesIn_uniqueGraphLookupFormula_stage_iff_l hθ
        hhistory hlookupKeyStage hrelationStage).mpr rfl
    · rw [hfields, hsuccAssignment, hkeyAssignment,
        hrelationAssignment, satisfiesIn_formula4At_stage_iff_l]
      apply (satisfiesIn_existsProjOutputFormula_stage_natCode_iff_l
        hθ hω n ha hrelationStage houtput).mpr
      simpa [relation, lookupKey, succN] using hvalue

/-! ## 分支汇总与完整单步公式 -/

private theorem satisfiesIn_eStepDisj_stage_iff_l
    (M : Set ZFSet.{u}) {n : Nat} (left right : FOFormula n)
    (assignment : Tuple ZFSet.{u} n) :
    Constructible.Model.SatisfiesIn M (.disj left right) assignment ↔
      Constructible.Model.SatisfiesIn M left assignment ∨
        Constructible.Model.SatisfiesIn M right assignment := by
  classical
  simp only [FOFormula.disj, Constructible.Model.SatisfiesIn]
  tauto

/-- 五种构造器守卫的析取恰好是外部的 `TextbookEGuard`。 -/
theorem satisfiesIn_anyCodeGuard_stage_standard_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    {a key history output : ZFSet.{u}}
    (ha : a ∈ LStageZF θ) (hkey : key ∈ LStageZF θ)
    (hhistory : history ∈ LStageZF θ) (houtput : output ∈ LStageZF θ)
    (m n : Nat) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        Constructible.TextbookEFormula.anyCodeGuard
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n] ↔
      Constructible.TextbookEFormula.TextbookEGuard m n := by
  rw [Constructible.TextbookEFormula.anyCodeGuard]
  repeat' rw [satisfiesIn_eStepDisj_stage_iff_l]
  rw [satisfiesIn_codeGuard_stage_standard_iff_l
      hθ hω 0 true ha hkey hhistory houtput,
    satisfiesIn_codeGuard_stage_standard_iff_l
      hθ hω 1 true ha hkey hhistory houtput,
    satisfiesIn_codeGuard_stage_standard_iff_l
      hθ hω 2 false ha hkey hhistory houtput,
    satisfiesIn_codeGuard_stage_standard_iff_l
      hθ hω 3 false ha hkey hhistory houtput,
    satisfiesIn_codeGuard_stage_standard_iff_l
      hθ hω 4 false ha hkey hhistory houtput]
  simp [Constructible.TextbookEFormula.TextbookEGuard]

/-- 未被五种构造器识别的键在局部层中精确返回空集。 -/
theorem satisfiesIn_stepFallback_stage_standard_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    {a key history output : ZFSet.{u}}
    (ha : a ∈ LStageZF θ) (hkey : key ∈ LStageZF θ)
    (hhistory : history ∈ LStageZF θ) (houtput : output ∈ LStageZF θ)
    (m n : Nat) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        Constructible.TextbookEFormula.stepFallback
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n] ↔
      ¬ Constructible.TextbookEFormula.TextbookEGuard m n ∧
        output = (∅ : ZFSet.{u}) := by
  let assignment : Tuple ZFSet.{u} 7 :=
    ![a, key, history, output,
      (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n]
  have hAssignment : ∀ position, assignment position ∈ LStageZF θ := by
    intro position
    fin_cases position <;>
      first
        | exact omega_toZFSet_mem_stage_l hω
        | exact natCode_mem_stage_l hω _
        | assumption
  change Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      Constructible.TextbookEFormula.stepFallback assignment ↔ _
  rw [Constructible.TextbookEFormula.stepFallback]
  simp only [Constructible.Model.SatisfiesIn]
  rw [satisfiesIn_anyCodeGuard_stage_standard_iff_l
    hθ hω ha hkey hhistory houtput]
  exact and_congr Iff.rfl
    (satisfiesIn_emptyDeltaAt_stage_iff_l
      (3 : Fin 7) assignment hAssignment)

/-- 六个互斥分支的析取恰好表达外部单步分支结果。 -/
theorem satisfiesIn_stepBranches_stage_standard_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    {a key history output : ZFSet.{u}}
    (ha : a ∈ LStageZF θ) (hkey : key ∈ LStageZF θ)
    (hhistory : history ∈ LStageZF θ) (houtput : output ∈ LStageZF θ)
    (m n : Nat) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        (.disj Constructible.TextbookEFormula.stepBranchZero <|
          .disj Constructible.TextbookEFormula.stepBranchOne <|
          .disj Constructible.TextbookEFormula.stepBranchTwo <|
          .disj Constructible.TextbookEFormula.stepBranchThree <|
          .disj Constructible.TextbookEFormula.stepBranchFour
            Constructible.TextbookEFormula.stepFallback)
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n] ↔
      Constructible.TextbookEFormula.TextbookEBranchResult
        a history output m n := by
  repeat' rw [satisfiesIn_eStepDisj_stage_iff_l]
  rw [satisfiesIn_stepBranchZero_stage_standard_iff_l
      hθ hω ha hkey hhistory houtput,
    satisfiesIn_stepBranchOne_stage_standard_iff_l
      hθ hω ha hkey hhistory houtput,
    satisfiesIn_stepBranchTwo_stage_standard_iff_l
      hθ hω ha hkey hhistory houtput,
    satisfiesIn_stepBranchThree_stage_standard_iff_l
      hθ hω ha hkey hhistory houtput,
    satisfiesIn_stepBranchFour_stage_standard_iff_l
      hθ hω ha hkey hhistory houtput,
    satisfiesIn_stepFallback_stage_standard_iff_l
      hθ hω ha hkey hhistory houtput]
  rfl

/-- 已解码为标准自然数对时，单步主体恰好计算外部 `textbookEStep`。 -/
theorem satisfiesIn_textbookEStepBody_stage_standard_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    {a key history output : ZFSet.{u}}
    (ha : a ∈ LStageZF θ) (hkey : key ∈ LStageZF θ)
    (hhistory : history ∈ LStageZF θ) (houtput : output ∈ LStageZF θ)
    (m n : Nat) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        Constructible.TextbookEFormula.textbookEStepBody
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n] ↔
      key = ZFSet.pair (natCode m) (natCode n) ∧
        output = Constructible.textbookEStep a
          (ZFSet.pair (natCode m) (natCode n)) history := by
  rw [Constructible.TextbookEFormula.textbookEStepBody]
  let assignment : Tuple ZFSet.{u} 7 :=
    ![a, key, history, output,
      (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n]
  have hAssignment : ∀ position, assignment position ∈ LStageZF θ := by
    intro position
    fin_cases position <;>
      first
        | exact omega_toZFSet_mem_stage_l hω
        | exact natCode_mem_stage_l hω _
        | assumption
  change
    (Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        (Constructible.Model.standardOmegaAt (4 : Fin 7)) assignment ∧
      (natCode m : ZFSet.{u}) ∈ Ordinal.omega0.toZFSet ∧
      (natCode n : ZFSet.{u}) ∈ Ordinal.omega0.toZFSet ∧
      Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        (Delta0Formula.kuratowskiPairEqAt
          (1 : Fin 7) (5 : Fin 7) (6 : Fin 7)).toFO assignment ∧
      Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        (.disj Constructible.TextbookEFormula.stepBranchZero <|
          .disj Constructible.TextbookEFormula.stepBranchOne <|
          .disj Constructible.TextbookEFormula.stepBranchTwo <|
          .disj Constructible.TextbookEFormula.stepBranchThree <|
          .disj Constructible.TextbookEFormula.stepBranchFour
            Constructible.TextbookEFormula.stepFallback) assignment) ↔ _
  rw [satisfiesIn_standardOmegaAt_stage_iff_l
      hθ hω (4 : Fin 7) assignment hAssignment,
    satisfiesIn_kuratowskiPairEqAt_stage_iff_l
      (1 : Fin 7) (5 : Fin 7) (6 : Fin 7) assignment hAssignment,
    satisfiesIn_stepBranches_stage_standard_iff_l
      hθ hω ha hkey hhistory houtput,
    Constructible.TextbookEFormula.textbookEBranchResult_iff_step]
  simp [assignment, IndexedSequenceZF.mem_omega_iff_exists_natCode]

/-- 完整 E 单步公式在任意足够高的后继极限层中具有外部精确语义。 -/
theorem satisfiesIn_textbookEStepFormula_stage_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    {a key history output : ZFSet.{u}}
    (ha : a ∈ LStageZF θ) (hkey : key ∈ LStageZF θ)
    (hhistory : history ∈ LStageZF θ) (houtput : output ∈ LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        Constructible.TextbookEFormula.textbookEStepFormula
        ![a, key, history, output] ↔
      key ∈ Constructible.TextbookEDomain ∧
        output = Constructible.textbookEStep a key history := by
  rw [Constructible.TextbookEFormula.textbookEStepFormula]
  simp only [Constructible.Model.SatisfiesIn]
  have hassign (omega mSet nSet : ZFSet.{u}) :
      snoc (snoc (snoc ![a, key, history, output] omega) mSet) nSet =
        ![a, key, history, output, omega, mSet, nSet] := by
    funext position
    fin_cases position <;> rfl
  constructor
  · rintro ⟨omega, homegaStage, mSet, hmSetStage,
      nSet, hnSetStage, hbody⟩
    rw [hassign] at hbody
    have hAssignment : ∀ position : Fin 7,
        ![a, key, history, output, omega, mSet, nSet] position ∈
          LStageZF θ := by
      intro position
      fin_cases position <;> assumption
    have homega : omega = (Ordinal.omega0.toZFSet : ZFSet.{u}) :=
      (satisfiesIn_standardOmegaAt_stage_iff_l hθ hω (4 : Fin 7)
        ![a, key, history, output, omega, mSet, nSet] hAssignment).mp
          hbody.1
    subst omega
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode mSet).mp
      hbody.2.1 with ⟨m, rfl⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode nSet).mp
      hbody.2.2.1 with ⟨n, rfl⟩
    have hstandard := (satisfiesIn_textbookEStepBody_stage_standard_iff_l
      hθ hω ha hkey hhistory houtput m n).mp hbody
    constructor
    · apply Constructible.mem_textbookEDomain_iff.mpr
      exact ⟨natCode m,
        (IndexedSequenceZF.mem_omega_iff_exists_natCode
          (natCode m)).mpr ⟨m, rfl⟩,
        natCode n,
        (IndexedSequenceZF.mem_omega_iff_exists_natCode
          (natCode n)).mpr ⟨n, rfl⟩, hstandard.1⟩
    · simpa only [hstandard.1] using hstandard.2
  · rintro ⟨hkeyDomain, hvalue⟩
    rcases Constructible.exists_textbookEKeyDecode_of_mem_textbookEDomain
      hkeyDomain with ⟨m, n, _hdecode, hkeyEq⟩
    refine ⟨(Ordinal.omega0.toZFSet : ZFSet.{u}),
      omega_toZFSet_mem_stage_l hω,
      (natCode m : ZFSet.{u}), natCode_mem_stage_l hω m,
      (natCode n : ZFSet.{u}), natCode_mem_stage_l hω n, ?_⟩
    rw [hassign]
    apply (satisfiesIn_textbookEStepBody_stage_standard_iff_l
      hθ hω ha hkey hhistory houtput m n).mpr
    exact ⟨hkeyEq, by simpa only [hkeyEq] using hvalue⟩

end

end YesMetaZFC.BMS.ConstructibleBridge
