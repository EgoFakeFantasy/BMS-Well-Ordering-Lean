import BMSConstructibleBridge.TextbookEStepStage

/-!
# textbook E 局部解在可构造层中的解码

本模块把通用教材式良基递归的局部解公式专门化到 E 枚举。第一部分识别
标准键的最小前驱闭包；第二部分从任意层内公式见证恢复真实局部解。
-/

open Set

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible
open Constructible.FiniteSequenceZF

noncomputable section

/-- 标准 E 键上的最小闭包公式精确识别外部局部递归域。 -/
theorem satisfiesIn_textbookELocalDomainFormula_stage_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) (m n : Nat)
    {a domain : ZFSet.{u}}
    (ha : a ∈ LStageZF θ) (hdomain : domain ∈ LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        (Constructible.Model.localDomainFormula
          Constructible.TextbookEFormula.textbookEDomainWithParamFormula
          Constructible.TextbookEFormula.textbookERelationWithParamFormula)
        ![a, ZFSet.pair (natCode m) (natCode n), domain] ↔
      domain = Constructible.localRecursionDomain
        Constructible.TextbookEDomain Constructible.TextbookERelation
        Constructible.textbookERelation_hasSetPredecessorsOn
        (ZFSet.pair (natCode m) (natCode n)) := by
  let key : ZFSet.{u} := ZFSet.pair (natCode m) (natCode n)
  have hkeyStage : key ∈ LStageZF θ :=
    orderedPair_mem_LStageZF_of_isSuccLimit hθ
      (natCode_mem_stage_l hω m) (natCode_mem_stage_l hω n)
  have hclass : ∀ z : ZFSet.{u}, z ∈ LStageZF θ →
      (Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
          Constructible.TextbookEFormula.textbookEDomainWithParamFormula
          (snoc ![a] z) ↔ z ∈ Constructible.TextbookEDomain) := by
    intro z hz
    have hassign : snoc ![a] z = ![a, z] := by
      funext position
      fin_cases position <;> rfl
    rw [hassign]
    exact satisfiesIn_textbookEDomainWithParamFormula_stage_iff_l
      hθ hω ha hz
  have hrelation : ∀ y : ZFSet.{u}, y ∈ LStageZF θ →
      ∀ z : ZFSet.{u}, z ∈ LStageZF θ →
      (Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
          Constructible.TextbookEFormula.textbookERelationWithParamFormula
          (snoc (snoc ![a] y) z) ↔
        Constructible.ClassRel Constructible.TextbookERelation y z) := by
    intro y hy z hz
    have hassign : snoc (snoc ![a] y) z = ![a, y, z] := by
      funext position
      fin_cases position <;> rfl
    rw [hassign]
    exact satisfiesIn_textbookERelationWithParamFormula_stage_iff_l
      hθ hω ha hy hz
  have hsemantic :=
    Constructible.Model.satisfiesIn_localDomainFormula_iff_eq_localRecursionDomain
      (LStageZF_isTransitive θ)
      Constructible.TextbookEFormula.textbookEDomainWithParamFormula
      Constructible.TextbookEFormula.textbookERelationWithParamFormula
      ![a] hclass hrelation
      Constructible.textbookERelation_isRelationOn
      Constructible.textbookERelation_hasSetPredecessorsOn
      (textbookERelation_predecessorsClosedIn_stage_l hθ)
      hkeyStage (textbookEKey_mem_domain_l m n) hdomain
      (textbookE_localRecursionDomain_natCode_mem_LStageZF_l hθ hω m n)
  have hassign : snoc (snoc ![a] key) domain = ![a, key, domain] := by
    funext position
    fin_cases position <;> rfl
  simpa only [hassign, key] using hsemantic

/--
在后继极限层中，从通用局部解公式见证恢复外部教材式局部解。
通用库版本要求整个载体满足 ZF；这里逐项检查其证明实际只需要传递性、
有序对闭包以及已经显式给出的关系和单步绝对性。
-/
theorem exists_textbookLocalSolution_of_satisfiesIn_stage_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    {parameterCount : Nat}
    (classFormula : FOFormula (parameterCount + 1))
    (relationFormula : FOFormula (parameterCount + 2))
    (stepFormula : FOFormula (parameterCount + 3))
    (parameters : Tuple ZFSet.{u} parameterCount)
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : Constructible.IsWellFoundedSetLikeOn A R)
    (hParameters : ∀ position, parameters position ∈ LStageZF θ)
    (hClass : ∀ z, z ∈ LStageZF θ →
      (Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
          classFormula (snoc parameters z) ↔ z ∈ A))
    (hRelation : ∀ y, y ∈ LStageZF θ → ∀ z, z ∈ LStageZF θ →
      (Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
          relationFormula (snoc (snoc parameters y) z) ↔
        Constructible.ClassRel R y z))
    (hClosed : Constructible.PredecessorsClosedIn
      (LStageZF θ : Set ZFSet.{u}) A R)
    {step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}}
    (hStep : Constructible.Model.TextbookStepAbsoluteAt
      (LStageZF θ : Set ZFSet.{u}) parameters A step stepFormula)
    {x graph : ZFSet.{u}} (hxStage : x ∈ LStageZF θ) (hxA : x ∈ A)
    (hgraphStage : graph ∈ LStageZF θ)
    (hlocalDomainStage : Constructible.localRecursionDomain A R hR.2.2 x ∈
      LStageZF θ)
    (hformula : Constructible.Model.SatisfiesIn
      (LStageZF θ : Set ZFSet.{u})
      (Constructible.Model.localSolutionFormula
        classFormula relationFormula stepFormula)
      (snoc (snoc parameters x) graph)) :
    ∃ solution : Constructible.TextbookLocalSolution A R hR.2.2 step x,
      solution.graph = graph := by
  classical
  rcases (Constructible.Model.satisfiesIn_localSolutionFormula_iff
      (LStageZF_isTransitive θ) classFormula relationFormula stepFormula
      parameters x graph hParameters hxStage hgraphStage).mp hformula with
    ⟨domain, hdomainStage, hdomainFormula, hfunction, hsteps⟩
  have hdomainEq : domain =
      Constructible.localRecursionDomain A R hR.2.2 x :=
    (Constructible.Model.satisfiesIn_localDomainFormula_iff_eq_localRecursionDomain
      (LStageZF_isTransitive θ) classFormula relationFormula parameters
      hClass hRelation hR.1 hR.2.2 hClosed hxStage hxA hdomainStage
      hlocalDomainStage).mp hdomainFormula
  subst domain
  let localDomain := Constructible.localRecursionDomain A R hR.2.2 x
  have hinputStage : ∀ t : ZFSet.{u}, t ∈ localDomain → t ∈ LStageZF θ := by
    intro t ht
    exact (LStageZF_isTransitive θ).mem_trans ht hlocalDomainStage
  let value : ZFSet.{u} → ZFSet.{u} := fun t =>
    if ht : t ∈ localDomain then
      Classical.choose (hfunction.1 t (hinputStage t ht) ht)
    else ∅
  have hvalueSpec : ∀ t : ZFSet.{u}, ∀ ht : t ∈ localDomain,
      value t ∈ LStageZF θ ∧ ZFSet.pair t (value t) ∈ graph ∧
        ∀ other : ZFSet.{u}, other ∈ LStageZF θ →
          ZFSet.pair t other ∈ graph → other = value t := by
    intro t ht
    have hchosen := Classical.choose_spec
      (hfunction.1 t (hinputStage t ht) ht)
    simpa only [value, dif_pos ht] using hchosen
  have hgraphEq : graph =
      Constructible.predecessorRestrictionGraph localDomain value := by
    apply ZFSet.ext
    intro pair
    constructor
    · intro hpairGraph
      have hpairStage : pair ∈ LStageZF θ :=
        (LStageZF_isTransitive θ).mem_trans hpairGraph hgraphStage
      rcases hfunction.2 pair hpairStage hpairGraph with
        ⟨input, _hinputStage, hinputDomain, output,
          houtputStage, hpairEq⟩
      have houtputEq :=
        (hvalueSpec input hinputDomain).2.2 output houtputStage (by
          rw [← hpairEq]
          exact hpairGraph)
      apply Constructible.mem_predecessorRestrictionGraph_iff.mpr
      exact ⟨input, hinputDomain, by rw [← houtputEq]; exact hpairEq.symm⟩
    · intro hpairRestriction
      rcases Constructible.mem_predecessorRestrictionGraph_iff.mp
          hpairRestriction with ⟨input, hinputDomain, hpairEq⟩
      rw [← hpairEq]
      exact (hvalueSpec input hinputDomain).2.1
  have hsatisfies : Constructible.SatisfiesTextbookLocalRecursion
      A R hR.2.2 step x value := by
    intro top htopDomain
    have htopStage : top ∈ LStageZF θ := hinputStage top htopDomain
    rcases hsteps top htopStage htopDomain with
      ⟨restriction, hrestrictionStage, output, houtputStage,
        hrestriction, houtputGraph, hstepFormula⟩
    have htopA : top ∈ A :=
      Constructible.localRecursionDomain_subset hR.2.2 hxA htopDomain
    have hrestrictionEq : restriction =
        Constructible.predecessorRestrictionGraph
          (Constructible.displayedPredecessors A R hR.2.2 top) value := by
      apply ZFSet.ext
      intro pair
      constructor
      · intro hpairRestriction
        have hpairStage : pair ∈ LStageZF θ :=
          (LStageZF_isTransitive θ).mem_trans
            hpairRestriction hrestrictionStage
        rcases (hrestriction pair hpairStage).mp hpairRestriction with
          ⟨hpairGraph, input, hinputStage', output', houtputStage',
            hpairEq, hinputFormula, hrelationFormula⟩
        have hinputA : input ∈ A :=
          (hClass input hinputStage').mp hinputFormula
        have hinputTop : Constructible.ClassRel R input top :=
          (hRelation input hinputStage' top htopStage).mp hrelationFormula
        have hinputPred : input ∈
            Constructible.displayedPredecessors A R hR.2.2 top :=
          (Constructible.displayedPredecessors_spec hR.2.2 htopA input).mpr
            ⟨hinputA, hinputTop⟩
        have hinputDomain : input ∈ localDomain :=
          Constructible.localRecursionDomain_predecessorClosed
            hR.1 hR.2.2 hxA htopDomain hinputTop
        have houtputEq : output' = value input :=
          (hvalueSpec input hinputDomain).2.2 output' houtputStage' (by
            rw [hpairEq] at hpairGraph
            exact hpairGraph)
        apply Constructible.mem_predecessorRestrictionGraph_iff.mpr
        exact ⟨input, hinputPred, by rw [← houtputEq, hpairEq]⟩
      · intro hpairExpected
        rcases Constructible.mem_predecessorRestrictionGraph_iff.mp
            hpairExpected with ⟨input, hinputPred, hpairEq⟩
        have hinputSpec :=
          (Constructible.displayedPredecessors_spec hR.2.2 htopA input).mp
            hinputPred
        have hinputDomain : input ∈ localDomain :=
          Constructible.localRecursionDomain_predecessorClosed
            hR.1 hR.2.2 hxA htopDomain hinputSpec.2
        have hinputStage' : input ∈ LStageZF θ :=
          hinputStage input hinputDomain
        have hvalueStage : value input ∈ LStageZF θ :=
          (hvalueSpec input hinputDomain).1
        have hpairStage : ZFSet.pair input (value input) ∈ LStageZF θ :=
          orderedPair_mem_LStageZF_of_isSuccLimit
            hθ hinputStage' hvalueStage
        rw [← hpairEq]
        apply (hrestriction (ZFSet.pair input (value input)) hpairStage).mpr
        refine ⟨(hvalueSpec input hinputDomain).2.1,
          input, hinputStage', value input, hvalueStage, rfl, ?_, ?_⟩
        · exact (hClass input hinputStage').mpr hinputSpec.1
        · exact (hRelation input hinputStage' top htopStage).mpr hinputSpec.2
    have houtputEq : output = value top :=
      (hvalueSpec top htopDomain).2.2 output houtputStage houtputGraph
    have hstepSemantic :=
      (hStep.2 top restriction output htopStage
        hrestrictionStage houtputStage).mp hstepFormula
    have hstepEq : output = step top restriction := hstepSemantic.2
    rw [← houtputEq, hstepEq, hrestrictionEq]
  let solution : Constructible.TextbookLocalSolution
      A R hR.2.2 step x :=
    { value := value
      graph := graph
      graph_eq := hgraphEq
      satisfies := hsatisfies }
  exact ⟨solution, rfl⟩

/-- E 单步函数及其公式在给定局部层上组成通用递归所需的绝对性包。 -/
theorem textbookEStep_absoluteAt_stage_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) {a : ZFSet.{u}}
    (ha : a ∈ LStageZF θ) :
    Constructible.Model.TextbookStepAbsoluteAt
      (LStageZF θ : Set ZFSet.{u}) ![a]
      Constructible.TextbookEDomain (Constructible.textbookEStep a)
      Constructible.TextbookEFormula.textbookEStepFormula := by
  constructor
  · intro key _hkeyStage hkeyDomain history hhistoryStage
    exact textbookEStep_mem_LStageZF_l hθ ha hhistoryStage hkeyDomain
  · intro key history output hkeyStage hhistoryStage houtputStage
    have hassign : snoc (snoc (snoc ![a] key) history) output =
        ![a, key, history, output] := by
      funext position
      fin_cases position <;> rfl
    rw [hassign]
    exact satisfiesIn_textbookEStepFormula_stage_iff_l
      hθ hω ha hkeyStage hhistoryStage houtputStage

/-- 任意满足 E 局部解公式的层内图都解码为真实的教材式局部解。 -/
theorem exists_textbookELocalSolution_of_satisfiesIn_stage_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) (m n : Nat)
    {a graph : ZFSet.{u}} (ha : a ∈ LStageZF θ)
    (hgraph : graph ∈ LStageZF θ)
    (hformula : Constructible.Model.SatisfiesIn
      (LStageZF θ : Set ZFSet.{u})
      (Constructible.Model.localSolutionFormula
        Constructible.TextbookEFormula.textbookEDomainWithParamFormula
        Constructible.TextbookEFormula.textbookERelationWithParamFormula
        Constructible.TextbookEFormula.textbookEStepFormula)
      ![a, ZFSet.pair (natCode m) (natCode n), graph]) :
    ∃ solution : Constructible.TextbookLocalSolution
        Constructible.TextbookEDomain Constructible.TextbookERelation
        Constructible.textbookERelation_hasSetPredecessorsOn
        (Constructible.textbookEStep a)
        (ZFSet.pair (natCode m) (natCode n)),
      solution.graph = graph := by
  let key : ZFSet.{u} := ZFSet.pair (natCode m) (natCode n)
  have hkeyStage : key ∈ LStageZF θ :=
    orderedPair_mem_LStageZF_of_isSuccLimit hθ
      (natCode_mem_stage_l hω m) (natCode_mem_stage_l hω n)
  have hclass : ∀ z, z ∈ LStageZF θ →
      (Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
          Constructible.TextbookEFormula.textbookEDomainWithParamFormula
          (snoc ![a] z) ↔ z ∈ Constructible.TextbookEDomain) := by
    intro z hz
    have hassign : snoc ![a] z = ![a, z] := by
      funext position
      fin_cases position <;> rfl
    rw [hassign]
    exact satisfiesIn_textbookEDomainWithParamFormula_stage_iff_l
      hθ hω ha hz
  have hrelation : ∀ y, y ∈ LStageZF θ → ∀ z, z ∈ LStageZF θ →
      (Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
          Constructible.TextbookEFormula.textbookERelationWithParamFormula
          (snoc (snoc ![a] y) z) ↔
        Constructible.ClassRel Constructible.TextbookERelation y z) := by
    intro y hy z hz
    have hassign : snoc (snoc ![a] y) z = ![a, y, z] := by
      funext position
      fin_cases position <;> rfl
    rw [hassign]
    exact satisfiesIn_textbookERelationWithParamFormula_stage_iff_l
      hθ hω ha hy hz
  have hformula' : Constructible.Model.SatisfiesIn
      (LStageZF θ : Set ZFSet.{u})
      (Constructible.Model.localSolutionFormula
        Constructible.TextbookEFormula.textbookEDomainWithParamFormula
        Constructible.TextbookEFormula.textbookERelationWithParamFormula
        Constructible.TextbookEFormula.textbookEStepFormula)
      (snoc (snoc ![a] key) graph) := by
    have hassign : snoc (snoc ![a] key) graph = ![a, key, graph] := by
      funext position
      fin_cases position <;> rfl
    rw [hassign]
    simpa only [key] using hformula
  exact exists_textbookLocalSolution_of_satisfiesIn_stage_l
    hθ
    Constructible.TextbookEFormula.textbookEDomainWithParamFormula
    Constructible.TextbookEFormula.textbookERelationWithParamFormula
    Constructible.TextbookEFormula.textbookEStepFormula ![a]
    Constructible.textbookERelation_isWellFoundedSetLikeOn
    (by intro position; fin_cases position; exact ha)
    hclass hrelation (textbookERelation_predecessorsClosedIn_stage_l hθ)
    (textbookEStep_absoluteAt_stage_l hθ hω ha)
    hkeyStage (textbookEKey_mem_domain_l m n) hgraph
    (textbookE_localRecursionDomain_natCode_mem_LStageZF_l hθ hω m n)
    hformula'

/-- 局部解图在顶键处给出的值等于外部全局 E 递归值。 -/
theorem textbookEByKey_eq_of_satisfies_localSolution_stage_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) (m n : Nat)
    {a graph output : ZFSet.{u}} (ha : a ∈ LStageZF θ)
    (hgraph : graph ∈ LStageZF θ)
    (hformula : Constructible.Model.SatisfiesIn
      (LStageZF θ : Set ZFSet.{u})
      (Constructible.Model.localSolutionFormula
        Constructible.TextbookEFormula.textbookEDomainWithParamFormula
        Constructible.TextbookEFormula.textbookERelationWithParamFormula
        Constructible.TextbookEFormula.textbookEStepFormula)
      ![a, ZFSet.pair (natCode m) (natCode n), graph])
    (hvalue : ZFSet.pair (ZFSet.pair (natCode m) (natCode n)) output ∈
      graph) :
    output = Constructible.textbookEByKey a
      (ZFSet.pair (natCode m) (natCode n)) := by
  rcases exists_textbookELocalSolution_of_satisfiesIn_stage_l
      hθ hω m n ha hgraph hformula with ⟨solution, hsolutionGraph⟩
  have hvalueRestriction :
      ZFSet.pair (ZFSet.pair (natCode m) (natCode n)) output ∈
        Constructible.predecessorRestrictionGraph
          (Constructible.localRecursionDomain
            Constructible.TextbookEDomain Constructible.TextbookERelation
            Constructible.textbookERelation_hasSetPredecessorsOn
            (ZFSet.pair (natCode m) (natCode n))) solution.value := by
    rw [← solution.graph_eq, hsolutionGraph]
    exact hvalue
  rcases Constructible.mem_predecessorRestrictionGraph_iff.mp
      hvalueRestriction with ⟨source, _hsource, hpair⟩
  have hcoordinates := ZFSet.pair_inj.mp hpair
  have hlocalValue : output =
      solution.value (ZFSet.pair (natCode m) (natCode n)) := by
    rw [hcoordinates.1] at hcoordinates
    exact hcoordinates.2.symm
  have htopLocal : ZFSet.pair (natCode m) (natCode n) ∈
      Constructible.localRecursionDomain
        Constructible.TextbookEDomain Constructible.TextbookERelation
        Constructible.textbookERelation_hasSetPredecessorsOn
        (ZFSet.pair (natCode m) (natCode n)) :=
    Constructible.mem_localRecursionDomain_iff.mpr (Or.inl rfl)
  have hagree :=
    Constructible.textbookGlobalRecursionFromLocalGraphs_eq_local_on_domain
      Constructible.textbookERelation_isWellFoundedSetLikeOn
      (Constructible.textbookEStep a) (textbookEKey_mem_domain_l m n)
      solution htopLocal
  exact hlocalValue.trans (by
    simpa only [Constructible.textbookEByKey] using hagree.symm)

/-! ## 公开 E 公式的层内解码 -/

/-- 递归值子公式在局部层中展开为一个层内局部解图。 -/
theorem satisfiesIn_textbookERecursionValueFormula_stage_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    {a key output : ZFSet.{u}}
    (ha : a ∈ LStageZF θ) (hkey : key ∈ LStageZF θ)
    (houtput : output ∈ LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        Constructible.TextbookEFormula.textbookERecursionValueFormula
        ![a, key, output] ↔
      key ∈ Constructible.TextbookEDomain ∧
        ∃ graph : ZFSet.{u}, graph ∈ LStageZF θ ∧
          Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
            (Constructible.Model.localSolutionFormula
              Constructible.TextbookEFormula.textbookEDomainWithParamFormula
              Constructible.TextbookEFormula.textbookERelationWithParamFormula
              Constructible.TextbookEFormula.textbookEStepFormula)
            ![a, key, graph] ∧ ZFSet.pair key output ∈ graph := by
  have hsemantic := Constructible.Model.satisfiesIn_recursionValueFormula_iff
    (LStageZF_isTransitive θ)
    Constructible.TextbookEFormula.textbookEDomainWithParamFormula
    Constructible.TextbookEFormula.textbookERelationWithParamFormula
    Constructible.TextbookEFormula.textbookEStepFormula
    ![a] key output
    (by intro position; fin_cases position; exact ha) hkey houtput
  have hkeyAssignment : snoc ![a] key = ![a, key] := by
    funext position
    fin_cases position <;> rfl
  have hgraphAssignment (graph : ZFSet.{u}) :
      snoc ![a, key] graph = ![a, key, graph] := by
    funext position
    fin_cases position <;> rfl
  have houtputAssignment : snoc ![a, key] output =
      ![a, key, output] := by
    funext position
    fin_cases position <;> rfl
  rw [hkeyAssignment, houtputAssignment] at hsemantic
  simpa only [Constructible.TextbookEFormula.textbookERecursionValueFormula,
    houtputAssignment, hgraphAssignment,
    satisfiesIn_textbookEDomainWithParamFormula_stage_iff_l
      hθ hω ha hkey] using hsemantic

/-- 公开 E 公式在局部层中纯句法地化为标准键上的局部解存在性。 -/
theorem satisfiesIn_textbookEZFFormula_stage_iff_localSolution_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    {a nCode mCode output : ZFSet.{u}}
    (ha : a ∈ LStageZF θ) (hnCode : nCode ∈ LStageZF θ)
    (hmCode : mCode ∈ LStageZF θ) (houtput : output ∈ LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        Constructible.TextbookEFormula.textbookEZFFormula
        ![a, nCode, mCode, output] ↔
      (nCode ∈ Constructible.textbookEOmegaZF ∧
        mCode ∈ Constructible.textbookEOmegaZF) ∧
        ∃ graph : ZFSet.{u}, graph ∈ LStageZF θ ∧
          Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
            (Constructible.Model.localSolutionFormula
              Constructible.TextbookEFormula.textbookEDomainWithParamFormula
              Constructible.TextbookEFormula.textbookERelationWithParamFormula
              Constructible.TextbookEFormula.textbookEStepFormula)
            ![a, ZFSet.pair mCode nCode, graph] ∧
          ZFSet.pair (ZFSet.pair mCode nCode) output ∈ graph := by
  rw [Constructible.TextbookEFormula.textbookEZFFormula]
  simp only [Constructible.Model.SatisfiesIn]
  constructor
  · rintro ⟨key, hkeyStage, hpairFormula, hrecursionFormula⟩
    have hAssignment : ∀ position : Fin 5,
        snoc ![a, nCode, mCode, output] key position ∈ LStageZF θ := by
      intro position
      fin_cases position
      · exact ha
      · exact hnCode
      · exact hmCode
      · exact houtput
      · exact hkeyStage
    have hpair : key = ZFSet.pair mCode nCode :=
      (satisfiesIn_kuratowskiPairEqAt_stage_iff_l
        (Fin.last 4) (2 : Fin 5) (1 : Fin 5)
        (snoc ![a, nCode, mCode, output] key) hAssignment).mp hpairFormula
    subst key
    have hrenamed :=
      (Constructible.Model.satisfiesIn_textbookERecursionValueFormula_rename
        (LStageZF θ : Set ZFSet.{u})
        (snoc ![a, nCode, mCode, output] (ZFSet.pair mCode nCode))).mp
          hrecursionFormula
    have hvalueAssignment :
        ![(snoc ![a, nCode, mCode, output]
              (ZFSet.pair mCode nCode)) 0,
          (snoc ![a, nCode, mCode, output]
              (ZFSet.pair mCode nCode)) 4,
          (snoc ![a, nCode, mCode, output]
              (ZFSet.pair mCode nCode)) 3] =
        ![a, ZFSet.pair mCode nCode, output] := by
      funext position
      fin_cases position <;> rfl
    rw [hvalueAssignment] at hrenamed
    have hkeyStage' : ZFSet.pair mCode nCode ∈ LStageZF θ :=
      orderedPair_mem_LStageZF_of_isSuccLimit hθ hmCode hnCode
    have hdecoded :=
      (satisfiesIn_textbookERecursionValueFormula_stage_iff_l
        hθ hω ha hkeyStage' houtput).mp hrenamed
    rw [Constructible.pair_mem_textbookEDomain_iff] at hdecoded
    exact ⟨hdecoded.1.symm, hdecoded.2⟩
  · rintro ⟨homega, graph, hgraphStage, hlocal, hvalue⟩
    let key : ZFSet.{u} := ZFSet.pair mCode nCode
    have hkeyStage : key ∈ LStageZF θ :=
      orderedPair_mem_LStageZF_of_isSuccLimit hθ hmCode hnCode
    refine ⟨key, hkeyStage, ?_, ?_⟩
    · have hAssignment : ∀ position : Fin 5,
          snoc ![a, nCode, mCode, output] key position ∈ LStageZF θ := by
        intro position
        fin_cases position
        · exact ha
        · exact hnCode
        · exact hmCode
        · exact houtput
        · exact hkeyStage
      apply (satisfiesIn_kuratowskiPairEqAt_stage_iff_l
        (Fin.last 4) (2 : Fin 5) (1 : Fin 5)
        (snoc ![a, nCode, mCode, output] key) hAssignment).mpr
      rfl
    · apply
        (Constructible.Model.satisfiesIn_textbookERecursionValueFormula_rename
          (LStageZF θ : Set ZFSet.{u})
          (snoc ![a, nCode, mCode, output] key)).mpr
      have hvalueAssignment :
          ![(snoc ![a, nCode, mCode, output] key) 0,
            (snoc ![a, nCode, mCode, output] key) 4,
            (snoc ![a, nCode, mCode, output] key) 3] =
          ![a, key, output] := by
        funext position
        fin_cases position <;> rfl
      rw [hvalueAssignment]
      apply (satisfiesIn_textbookERecursionValueFormula_stage_iff_l
        hθ hω ha hkeyStage houtput).mpr
      refine ⟨?_, graph, hgraphStage, ?_, ?_⟩
      · exact (Constructible.pair_mem_textbookEDomain_iff
          mCode nCode).mpr homega.symm
      · simpa only [key] using hlocal
      · simpa only [key] using hvalue

/-- 层内公开 E 公式的任何标准码见证都给出真实的外部 E 值。 -/
theorem textbookEZF_eq_of_satisfiesIn_stage_natCode_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) (n m : Nat)
    {a output : ZFSet.{u}} (ha : a ∈ LStageZF θ)
    (houtput : output ∈ LStageZF θ)
    (hformula : Constructible.Model.SatisfiesIn
      (LStageZF θ : Set ZFSet.{u})
      Constructible.TextbookEFormula.textbookEZFFormula
      ![a, natCode n, natCode m, output]) :
    output = Constructible.textbookEZF a (natCode n) (natCode m) := by
  have hdecoded :=
    (satisfiesIn_textbookEZFFormula_stage_iff_localSolution_l
      hθ hω ha (natCode_mem_stage_l hω n)
        (natCode_mem_stage_l hω m) houtput).mp hformula
  rcases hdecoded.2 with ⟨graph, hgraphStage, hlocal, hvalue⟩
  have hresult := textbookEByKey_eq_of_satisfies_localSolution_stage_l
    hθ hω m n ha hgraphStage hlocal hvalue
  simpa only [Constructible.textbookEZF] using hresult

end

end YesMetaZFC.BMS.ConstructibleBridge
