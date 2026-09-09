import BMSConstructibleBridge.TextbookEBoundedFormula
import BMSConstructibleBridge.TextbookFormulaCode
import BMSConstructibleBridge.TextbookEStageBounds
import ConstructibleUniverse.SetTheory.ZFC.Constructible.Ordinals

/-!
# 后继极限层中的 ambient Delta0 真值公式

对有限参数元组，选择一个属于当前层的传递集合 `domain`，要求该元组是从标准
自然数元数到 `domain` 的函数，然后在 `domain` 上计算规范 textbook `E` 值。
Delta0 绝对性保证选择哪个足够大的传递集合并不影响结果。这样得到的公式只用
纯成员语言，同时避免引入任意公式的 Tarski 真谓词。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible
open Constructible.FiniteSequenceZF

noncomputable section

/-- 布局 `[positiveArity, code, tuple, domain, output]` 的 ambient Delta0 真值核心。 -/
def textbookAmbientDelta0TruthBody_l : FOFormula 5 :=
  .conj
    (FOFormula.rename ![(3 : Fin 5)] OrdinalFormula.transitive)
    (.conj
      (TextbookDefFormula.isFunctionDeltaAt
        (2 : Fin 5) (0 : Fin 5) (3 : Fin 5)).toFO
      (.conj
        (FOFormula.rename
          ![(3 : Fin 5), (0 : Fin 5), (1 : Fin 5), (4 : Fin 5)]
          TextbookEBoundedFormula_l.valueFormula)
        (.mem (2 : Fin 5) (4 : Fin 5))))

/-- 布局 `[positiveArity, code, tuple]` 的 ambient Delta0 真值公式。 -/
def textbookAmbientDelta0TruthFormula_l : FOFormula 3 :=
  .ex (.ex textbookAmbientDelta0TruthBody_l)

/-- 核心中传递性子公式的层内语义。 -/
private theorem satisfiesIn_ambientTransitiveAt_iff_l
    {θ : Ordinal.{u}} (assignment : Tuple ZFSet.{u} 5)
    (hAssignment : ∀ position, assignment position ∈ LStageZF θ) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        (FOFormula.rename ![(3 : Fin 5)] OrdinalFormula.transitive)
        assignment ↔
      (assignment 3).IsTransitive := by
  rw [Model.satisfiesIn_rename]
  let selected : Tuple (StageCarrier θ) 1 :=
    ![⟨assignment 3, hAssignment 3⟩]
  have hSubtype := Model.satisfies_stageCarrier_iff_satisfiesIn
    OrdinalFormula.transitive selected
  have hValues : (fun position => (selected position).1) =
      ![assignment 3] := by
    funext position
    fin_cases position
    rfl
  rw [hValues] at hSubtype
  have hSemantic := OrdinalFormula.satisfies_transitive
    (LStageZF_isTransitive θ) (selected 0)
  have hSelectedValue : (selected 0).1 = assignment 3 := by rfl
  rw [hSelectedValue] at hSemantic
  exact hSubtype.symm.trans hSemantic

/--
在标准自然数码处，ambient Delta0 真值公式精确表示存在一个传递定义域，在该
定义域上元组的规范 E 关系成立。
-/
theorem satisfiesIn_textbookAmbientDelta0TruthFormula_natCode_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) (positiveArity code : Nat)
    {tuple : ZFSet.{u}} (htuple : tuple ∈ LStageZF θ) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookAmbientDelta0TruthFormula_l
        ![natCode positiveArity, natCode code, tuple] ↔
      ∃ domain ∈ LStageZF θ,
        domain.IsTransitive ∧
          ZFSet.IsFunc (natCode positiveArity) domain tuple ∧
            tuple ∈ textbookEZF domain (natCode positiveArity) (natCode code) := by
  simp only [textbookAmbientDelta0TruthFormula_l, Model.SatisfiesIn]
  constructor
  · rintro ⟨domain, hdomain, output, houtput, hbody⟩
    have hBodyAssignment :
        snoc (snoc ![natCode positiveArity, natCode code, tuple] domain) output =
          ![natCode positiveArity, natCode code, tuple, domain, output] := by
      funext position
      fin_cases position <;> rfl
    rw [hBodyAssignment] at hbody
    simp only [textbookAmbientDelta0TruthBody_l, Model.SatisfiesIn] at hbody
    rcases hbody with ⟨htransitive, hfunction, hvalue, hmember⟩
    have hAll : ∀ position,
        ![natCode positiveArity, natCode code, tuple, domain, output] position ∈
          LStageZF θ := by
      intro position
      fin_cases position
      · exact natCode_mem_LStageZF_of_isSuccLimit hθ positiveArity
      · exact natCode_mem_LStageZF_of_isSuccLimit hθ code
      · exact htuple
      · exact hdomain
      · exact houtput
    have hTransitive : domain.IsTransitive :=
      (satisfiesIn_ambientTransitiveAt_iff_l _ hAll).mp htransitive
    have hFunction : ZFSet.IsFunc (natCode positiveArity) domain tuple := by
      rw [Model.satisfiesIn_delta0_iff (LStageZF_isTransitive θ)
        (TextbookDefFormula.isFunctionDeltaAt
          (2 : Fin 5) (0 : Fin 5) (3 : Fin 5)) _ hAll] at hfunction
      rw [Delta0Formula.satisfies_toFO,
        TextbookDefFormula.satisfies_isFunctionDeltaAt] at hfunction
      change ZFSet.IsFunc (natCode positiveArity) domain tuple at hfunction
      exact hfunction
    simp only [Model.satisfiesIn_rename] at hvalue
    have hValueAssignment :
        (fun position =>
          ![natCode positiveArity, natCode code, tuple, domain, output]
            (![(3 : Fin 5), (0 : Fin 5), (1 : Fin 5), (4 : Fin 5)] position)) =
          ![domain, natCode positiveArity, natCode code, output] := by
      funext position
      fin_cases position <;> rfl
    rw [hValueAssignment,
      satisfiesIn_textbookEBoundedValueFormula_natCode_iff_l
        hθ hω positiveArity code hdomain houtput] at hvalue
    exact ⟨domain, hdomain, hTransitive, hFunction, hvalue ▸ hmember⟩
  · rintro ⟨domain, hdomain, hTransitive, hFunction, hmember⟩
    let output := textbookEZF domain (natCode positiveArity) (natCode code)
    have houtput : output ∈ LStageZF θ :=
      textbookEZF_natCode_mem_LStageZF_l hθ hdomain positiveArity code
    refine ⟨domain, hdomain, output, houtput, ?_⟩
    have hBodyAssignment :
        snoc (snoc ![natCode positiveArity, natCode code, tuple] domain) output =
          ![natCode positiveArity, natCode code, tuple, domain, output] := by
      funext position
      fin_cases position <;> rfl
    rw [hBodyAssignment]
    simp only [textbookAmbientDelta0TruthBody_l, Model.SatisfiesIn]
    have hAll : ∀ position,
        ![natCode positiveArity, natCode code, tuple, domain, output] position ∈
          LStageZF θ := by
      intro position
      fin_cases position
      · exact natCode_mem_LStageZF_of_isSuccLimit hθ positiveArity
      · exact natCode_mem_LStageZF_of_isSuccLimit hθ code
      · exact htuple
      · exact hdomain
      · exact houtput
    refine ⟨(satisfiesIn_ambientTransitiveAt_iff_l _ hAll).mpr hTransitive, ?_, ?_, hmember⟩
    · apply (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive θ)
        (TextbookDefFormula.isFunctionDeltaAt
          (2 : Fin 5) (0 : Fin 5) (3 : Fin 5)) _ hAll).mpr
      rw [Delta0Formula.satisfies_toFO,
        TextbookDefFormula.satisfies_isFunctionDeltaAt]
      change ZFSet.IsFunc (natCode positiveArity) domain tuple
      exact hFunction
    · simp only [Model.satisfiesIn_rename]
      have hValueAssignment :
          (fun position =>
            ![natCode positiveArity, natCode code, tuple, domain, output]
              (![(3 : Fin 5), (0 : Fin 5), (1 : Fin 5), (4 : Fin 5)] position)) =
            ![domain, natCode positiveArity, natCode code, output] := by
        funext position
        fin_cases position <;> rfl
      rw [hValueAssignment,
        satisfiesIn_textbookEBoundedValueFormula_natCode_iff_l
          hθ hω positiveArity code hdomain houtput]

/-- 当前层有限元组的规范图仍属于当前后继极限层。 -/
theorem textbookTupleGraph_mem_stage_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ) {n : Nat}
    (assignment : Tuple (StageCarrier θ) n) :
    textbookTupleGraph assignment ∈ LStageZF θ := by
  let raw : Tuple ZFSet.{u} n := fun position => (assignment position).1
  obtain ⟨γ, hγ, hsmall⟩ :=
    exists_stageBound_for_tuple_l hθ raw (fun position => (assignment position).2)
  let domain : ZFSet.{u} := LStageZF γ
  let localAssignment : Tuple (ZFCarrier domain) n :=
    fun position => ⟨raw position, hsmall position⟩
  have hdomain : domain ∈ LStageZF θ := LStageZF_mem_of_lt hγ
  obtain ⟨δ, hδ, hgraph⟩ :=
    exists_textbookTupleGraph_stageBound_l hθ hdomain n
  have hGraphEq : textbookTupleGraph localAssignment =
      textbookTupleGraph assignment := by rfl
  rw [← hGraphEq]
  exact LStageZF_mono (le_of_lt hδ) (hgraph localAssignment)

/--
规范编译的正元 Delta0 公式由 ambient 真值公式正确判定。右侧使用原始
`ZFSet` 赋值，因此结论可直接接入外部 Lévy 层语义。
-/
theorem satisfiesIn_textbookAmbientDelta0TruthFormula_compiled_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) {positiveArity : Nat}
    (formula : Delta0Formula (positiveArity + 1))
    (assignment : Tuple (StageCarrier θ) (positiveArity + 1)) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookAmbientDelta0TruthFormula_l
        ![natCode (positiveArity + 1),
          natCode (textbookFormulaCode_l formula.toFO),
          textbookTupleGraph assignment] ↔
      FOFormula.Satisfies Delta0Formula.ZFMem formula.toFO
        (fun position => (assignment position).1) := by
  have htuple : textbookTupleGraph assignment ∈ LStageZF θ :=
    textbookTupleGraph_mem_stage_l hθ assignment
  rw [satisfiesIn_textbookAmbientDelta0TruthFormula_natCode_iff_l
    hθ hω (positiveArity + 1) (textbookFormulaCode_l formula.toFO) htuple]
  constructor
  · rintro ⟨domain, _hdomain, hTransitive, hFunction, hmember⟩
    have hvalues : ∀ position, (assignment position).1 ∈ domain := by
      intro position
      have hpair := textbookTupleGraph_value assignment position
      exact (ZFSet.pair_mem_prod.mp (hFunction.1 hpair)).2
    let domainAssignment : Tuple (ZFCarrier domain) (positiveArity + 1) :=
      fun position => ⟨(assignment position).1, hvalues position⟩
    have hgraph : textbookTupleGraph domainAssignment =
        textbookTupleGraph assignment := by rfl
    have hDomainSat :
        FOFormula.Satisfies (zfCarrierMem domain) formula.toFO domainAssignment :=
      (textbookTupleGraph_mem_compiledRelation_iff_l
        domain formula.toFO domainAssignment).mp (by simpa only [hgraph] using hmember)
    have hAbsolute :=
      (Delta0Formula.satisfies_toFO_absolute
        hTransitive formula domainAssignment).mp hDomainSat
    have hVal : Delta0Formula.val domainAssignment =
        (fun position => (assignment position).1) := by rfl
    simpa only [hVal] using hAbsolute
  · intro hAmbient
    let raw : Tuple ZFSet.{u} (positiveArity + 1) :=
      fun position => (assignment position).1
    obtain ⟨γ, hγ, hsmall⟩ :=
      exists_stageBound_for_tuple_l hθ raw (fun position => (assignment position).2)
    let domain : ZFSet.{u} := LStageZF γ
    let domainAssignment : Tuple (ZFCarrier domain) (positiveArity + 1) :=
      fun position => ⟨raw position, hsmall position⟩
    have hdomain : domain ∈ LStageZF θ := LStageZF_mem_of_lt hγ
    have hDomainSat :
        FOFormula.Satisfies (zfCarrierMem domain) formula.toFO domainAssignment := by
      apply (Delta0Formula.satisfies_toFO_absolute
        (LStageZF_isTransitive γ) formula domainAssignment).mpr
      have hVal : Delta0Formula.val domainAssignment = raw := by rfl
      simpa only [hVal, raw] using hAmbient
    have hmember : textbookTupleGraph assignment ∈
        textbookEZF domain (natCode (positiveArity + 1))
          (natCode (textbookFormulaCode_l formula.toFO)) := by
      have hlocal := (textbookTupleGraph_mem_compiledRelation_iff_l
        domain formula.toFO domainAssignment).mpr hDomainSat
      have hgraph : textbookTupleGraph domainAssignment =
          textbookTupleGraph assignment := by rfl
      simpa only [hgraph] using hlocal
    refine ⟨domain, hdomain, LStageZF_isTransitive γ, ?_, hmember⟩
    have hlocalFunction := textbookTupleGraph_isFunc domainAssignment
    have hgraph : textbookTupleGraph domainAssignment =
        textbookTupleGraph assignment := by rfl
    simpa only [hgraph] using hlocalFunction

/-- 有界公式的原子与量词界均引用已有变量，故这种语法的元数必为正。 -/
theorem delta0Formula_arity_pos_l {arity : Nat} (φ : Delta0Formula arity) :
    0 < arity := by
  induction φ with
  | mem i _ => exact Nat.zero_lt_of_lt i.isLt
  | eq i _ => exact Nat.zero_lt_of_lt i.isLt
  | neg _ ih => exact ih
  | conj _ _ ih _ => exact ih
  | boundedEx i _ _ => exact Nat.zero_lt_of_lt i.isLt

/--
任意有界公式的 ambient 求值正确性。零元数由语法不可能性排除，并不将教材
的零元投影约定误认成闭句语义。
-/
theorem satisfiesIn_textbookAmbientDelta0TruthFormula_finite_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) {arity : Nat}
    (φ : Delta0Formula arity) (assignment : Tuple (StageCarrier θ) arity) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookAmbientDelta0TruthFormula_l
        ![natCode arity, natCode (textbookFormulaCode_l φ.toFO),
          textbookTupleGraph assignment] ↔
      FOFormula.Satisfies Delta0Formula.ZFMem φ.toFO
        (fun position => (assignment position).1) := by
  cases arity with
  | zero => exact (Nat.lt_irrefl 0 (delta0Formula_arity_pos_l φ)).elim
  | succ arity =>
      exact satisfiesIn_textbookAmbientDelta0TruthFormula_compiled_iff_l
        hθ hω φ assignment

end

end YesMetaZFC.BMS.ConstructibleBridge
