import BMSConstructibleBridge.TextbookEBoundedDomain
import BMSConstructibleBridge.TextbookELocalSolutionStage

/-!
# textbook E 的有限元数递归公式

这里把有限截断域本身写回纯成员语言。公开递归参数为 `(a,bound)`；定义域是
`omega × bound`，关系只比较代码坐标，单步公式忽略新增的界参数。
-/

open Set

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible
open Constructible.FiniteSequenceZF

noncomputable section

namespace TextbookEBoundedFormula_l

/-- 在布局 `(left,right,omega,bound)` 中描述截断代码递减关系。 -/
def relationDeltaAt {n : Nat}
    (left right omega bound : Fin n) : Delta0Formula n :=
  Delta0Formula.boundedEx omega
    (Delta0Formula.boundedEx bound.castSucc
      (Delta0Formula.boundedEx omega.castSucc.castSucc
        (Delta0Formula.boundedEx bound.castSucc.castSucc.castSucc
          (.conj
            (Delta0Formula.kuratowskiPairEqAt
              left.castSucc.castSucc.castSucc.castSucc
              (Fin.last n).castSucc.castSucc.castSucc
              (Fin.last (n + 1)).castSucc.castSucc)
            (.conj
              (Delta0Formula.kuratowskiPairEqAt
                right.castSucc.castSucc.castSucc.castSucc
                (Fin.last (n + 2)).castSucc
                (Fin.last (n + 3)))
              (.mem
                (Fin.last n).castSucc.castSucc.castSucc
                (Fin.last (n + 2)).castSucc))))))

@[simp] theorem satisfies_relationDeltaAt {n : Nat}
    (left right omega bound : Fin n) (s : Tuple ZFSet.{u} n) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        (relationDeltaAt left right omega bound) s ↔
      ∃ i : ZFSet.{u}, i ∈ s omega ∧
        ∃ k : ZFSet.{u}, k ∈ s bound ∧
          ∃ m : ZFSet.{u}, m ∈ s omega ∧
            ∃ next : ZFSet.{u}, next ∈ s bound ∧
              s left = ZFSet.pair i k ∧
              s right = ZFSet.pair m next ∧ i ∈ m := by
  simp [relationDeltaAt]

/-- 布局 `[a,bound,key]` 的截断定义域公式。 -/
def domainFormula : FOFormula 3 :=
  .ex (.conj
    (Constructible.Model.standardOmegaAt (Fin.last 3))
    (Constructible.TextbookDefFormula.productMemberDeltaAt
      (2 : Fin 4) (Fin.last 3) (1 : Fin 4)).toFO)

/-- 布局 `[a,bound,left,right]` 的截断关系公式。 -/
def relationFormula : FOFormula 4 :=
  .ex (.conj
    (Constructible.Model.standardOmegaAt (Fin.last 4))
    (relationDeltaAt
      (2 : Fin 5) (3 : Fin 5) (Fin.last 4) (1 : Fin 5)).toFO)

/-- 给 textbook E 单步公式插入一个不使用的有限界参数。 -/
def stepRename : Fin 4 → Fin 5 :=
  ![(0 : Fin 5), (2 : Fin 5), (3 : Fin 5), (4 : Fin 5)]

/-- 布局 `[a,bound,key,history,output]` 的单步公式。 -/
def stepFormula : FOFormula 5 :=
  .conj
    (FOFormula.rename ![(0 : Fin 5), (1 : Fin 5), (2 : Fin 5)]
      domainFormula)
    (FOFormula.rename stepRename
      Constructible.TextbookEFormula.textbookEStepFormula)

/-- 布局 `[a,bound,key,output]` 的截断递归值公式。 -/
def recursionValueFormula : FOFormula 4 :=
  Constructible.Model.recursionValueFormula
    domainFormula relationFormula stepFormula

/-- 八元体的坐标为 `[a,arity,code,output,omega,sum,bound,key]`。 -/
def valueBody : FOFormula 8 :=
  .conj
    (FOFormula.rename ![(4 : Fin 8), (1 : Fin 8),
      (2 : Fin 8), (5 : Fin 8)]
      Constructible.TextbookNatFormula.natAddFormula)
    (.conj
      (Delta0Formula.successorAt (6 : Fin 8) (5 : Fin 8)).toFO
      (.conj
        (Delta0Formula.kuratowskiPairEqAt
          (7 : Fin 8) (2 : Fin 8) (1 : Fin 8)).toFO
        (FOFormula.rename ![(0 : Fin 8), (6 : Fin 8),
          (7 : Fin 8), (3 : Fin 8)] recursionValueFormula)))

/-- 布局 `[a,arity,code,output]` 的层稳定 textbook E 公式。 -/
def valueFormula : FOFormula 4 :=
  .ex <| .ex <| .ex <| .ex valueBody

end TextbookEBoundedFormula_l

/-- 截断定义域公式在局部层中精确识别 `omega × bound`。 -/
theorem satisfiesIn_textbookEBoundedDomainFormula_stage_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) {a bound key : ZFSet.{u}}
    (ha : a ∈ LStageZF θ) (hbound : bound ∈ LStageZF θ)
    (hkey : key ∈ LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        TextbookEBoundedFormula_l.domainFormula ![a, bound, key] ↔
      key ∈ TextbookEBoundedDomain_l bound := by
  simp only [TextbookEBoundedFormula_l.domainFormula,
    Constructible.Model.SatisfiesIn]
  constructor
  · rintro ⟨omega, homegaStage, homegaFormula, hproductFormula⟩
    have homega : omega = Ordinal.omega0.toZFSet :=
      (satisfiesIn_standardOmegaAt_stage_iff_l hθ hω (Fin.last 3)
        ![a, bound, key, omega] (by
          intro position
          fin_cases position <;> assumption)).mp homegaFormula
    have hAssignment : ∀ position : Fin 4,
        ![a, bound, key, omega] position ∈ LStageZF θ := by
      intro position
      fin_cases position <;> assumption
    have hdelta :=
      (Constructible.Model.satisfiesIn_delta0_iff
        (LStageZF_isTransitive θ)
        (Constructible.TextbookDefFormula.productMemberDeltaAt
          (2 : Fin 4) (Fin.last 3) (1 : Fin 4))
        ![a, bound, key, omega] hAssignment).mp hproductFormula
    rw [Delta0Formula.satisfies_toFO,
      Constructible.TextbookDefFormula.satisfies_productMemberDeltaAt]
      at hdelta
    change key ∈ (ZFSet.prod omega bound : Set ZFSet.{u}) at hdelta
    simpa only [TextbookEBoundedDomain_l, Constructible.textbookEOmegaZF,
      homega] using hdelta
  · intro hdomain
    let omega : ZFSet.{u} := Ordinal.omega0.toZFSet
    have homegaStage : omega ∈ LStageZF θ := omega_toZFSet_mem_stage_l hω
    refine ⟨omega, homegaStage, ?_, ?_⟩
    · exact (satisfiesIn_standardOmegaAt_stage_iff_l hθ hω
        (Fin.last 3) ![a, bound, key, omega] (by
          intro position
          fin_cases position <;> assumption)).mpr rfl
    · have hAssignment : ∀ position : Fin 4,
          ![a, bound, key, omega] position ∈ LStageZF θ := by
        intro position
        fin_cases position <;> assumption
      apply (Constructible.Model.satisfiesIn_delta0_iff
        (LStageZF_isTransitive θ)
        (Constructible.TextbookDefFormula.productMemberDeltaAt
          (2 : Fin 4) (Fin.last 3) (1 : Fin 4))
        ![a, bound, key, omega] hAssignment).mpr
      rw [Delta0Formula.satisfies_toFO,
        Constructible.TextbookDefFormula.satisfies_productMemberDeltaAt]
      change key ∈ (ZFSet.prod omega bound : Set ZFSet.{u})
      simpa only [TextbookEBoundedDomain_l, Constructible.textbookEOmegaZF,
        omega] using hdomain

/-- 截断关系公式在局部层中精确识别代码递减关系。 -/
theorem satisfiesIn_textbookEBoundedRelationFormula_stage_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) {a bound left right : ZFSet.{u}}
    (ha : a ∈ LStageZF θ) (hbound : bound ∈ LStageZF θ)
    (hBoundOmega : bound ⊆ Constructible.textbookEOmegaZF)
    (hleft : left ∈ LStageZF θ) (hright : right ∈ LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        TextbookEBoundedFormula_l.relationFormula ![a, bound, left, right] ↔
      Constructible.ClassRel (TextbookEBoundedRelation_l bound) left right := by
  simp only [TextbookEBoundedFormula_l.relationFormula,
    Constructible.Model.SatisfiesIn]
  constructor
  · rintro ⟨omega, homegaStage, homegaFormula, hrelationFormula⟩
    have homega : omega = Ordinal.omega0.toZFSet :=
      (satisfiesIn_standardOmegaAt_stage_iff_l hθ hω (Fin.last 4)
        ![a, bound, left, right, omega] (by
          intro position
          fin_cases position <;> assumption)).mp homegaFormula
    have hAssignment : ∀ position : Fin 5,
        ![a, bound, left, right, omega] position ∈ LStageZF θ := by
      intro position
      fin_cases position <;> assumption
    have hdelta :=
      (Constructible.Model.satisfiesIn_delta0_iff
        (LStageZF_isTransitive θ)
        (TextbookEBoundedFormula_l.relationDeltaAt
          (2 : Fin 5) (3 : Fin 5) (Fin.last 4) (1 : Fin 5))
        ![a, bound, left, right, omega] hAssignment).mp hrelationFormula
    rw [Delta0Formula.satisfies_toFO,
      TextbookEBoundedFormula_l.satisfies_relationDeltaAt] at hdelta
    change ∃ i, i ∈ omega ∧ ∃ k, k ∈ bound ∧
      ∃ m, m ∈ omega ∧ ∃ n, n ∈ bound ∧
        left = ZFSet.pair i k ∧ right = ZFSet.pair m n ∧ i ∈ m at hdelta
    rcases hdelta with
      ⟨i, hi, k, hk, m, hm, n, hn, hleftPair, hrightPair, him⟩
    apply (classRel_textbookEBoundedRelation_iff_l bound left right).mpr
    refine ⟨?_, ?_, ?_⟩
    · exact ZFSet.mem_prod.mpr ⟨i,
        by simpa only [Constructible.textbookEOmegaZF, homega] using hi,
        k, hk, hleftPair⟩
    · exact ZFSet.mem_prod.mpr ⟨m,
        by simpa only [Constructible.textbookEOmegaZF, homega] using hm,
        n, hn, hrightPair⟩
    · apply (Constructible.classRel_textbookERelation_iff left right).mpr
      exact ⟨i, k, m, n,
        by simpa only [Constructible.textbookEOmegaZF, homega] using hi,
        hBoundOmega hk,
        by simpa only [Constructible.textbookEOmegaZF, homega] using hm,
        hBoundOmega hn,
        hleftPair, hrightPair, him⟩
  · intro hrelation
    let omega : ZFSet.{u} := Ordinal.omega0.toZFSet
    have homegaStage : omega ∈ LStageZF θ := omega_toZFSet_mem_stage_l hω
    refine ⟨omega, homegaStage, ?_, ?_⟩
    · exact (satisfiesIn_standardOmegaAt_stage_iff_l hθ hω
        (Fin.last 4) ![a, bound, left, right, omega] (by
          intro position
          fin_cases position <;> assumption)).mpr rfl
    · have hAssignment : ∀ position : Fin 5,
          ![a, bound, left, right, omega] position ∈ LStageZF θ := by
        intro position
        fin_cases position <;> assumption
      apply (Constructible.Model.satisfiesIn_delta0_iff
        (LStageZF_isTransitive θ)
        (TextbookEBoundedFormula_l.relationDeltaAt
          (2 : Fin 5) (3 : Fin 5) (Fin.last 4) (1 : Fin 5))
        ![a, bound, left, right, omega] hAssignment).mpr
      rw [Delta0Formula.satisfies_toFO,
        TextbookEBoundedFormula_l.satisfies_relationDeltaAt]
      change ∃ i, i ∈ omega ∧ ∃ k, k ∈ bound ∧
        ∃ m, m ∈ omega ∧ ∃ n, n ∈ bound ∧
          left = ZFSet.pair i k ∧ right = ZFSet.pair m n ∧ i ∈ m
      rcases (classRel_textbookEBoundedRelation_iff_l bound left right).mp
          hrelation with ⟨hleftDomain, hrightDomain, htextbook⟩
      rcases ZFSet.mem_prod.mp hleftDomain with
        ⟨i, hi, k, hk, hleftPair⟩
      rcases ZFSet.mem_prod.mp hrightDomain with
        ⟨m, hm, n, hn, hrightPair⟩
      have him : i ∈ m := by
        rcases (Constructible.classRel_textbookERelation_iff left right).mp
            htextbook with
          ⟨i', k', m', n', _hi', _hk', _hm', _hn',
            hleftPair', hrightPair', hi'm'⟩
        have hleftCoordinates := ZFSet.pair_inj.mp
          (hleftPair'.symm.trans hleftPair)
        have hrightCoordinates := ZFSet.pair_inj.mp
          (hrightPair'.symm.trans hrightPair)
        simpa only [hleftCoordinates.1, hrightCoordinates.1] using hi'm'
      exact ⟨i, by simpa only [Constructible.textbookEOmegaZF, omega] using hi,
        k, hk, m,
        by simpa only [Constructible.textbookEOmegaZF, omega] using hm,
        n, hn, hleftPair, hrightPair, him⟩

/-- 新增的有限界参数不改变 E 单步公式的层内语义。 -/
theorem satisfiesIn_textbookEBoundedStepFormula_stage_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) {a bound key history output : ZFSet.{u}}
    (ha : a ∈ LStageZF θ) (hbound : bound ∈ LStageZF θ)
    (hBoundOmega : bound ⊆ Constructible.textbookEOmegaZF)
    (hkey : key ∈ LStageZF θ) (hhistory : history ∈ LStageZF θ)
    (houtput : output ∈ LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        TextbookEBoundedFormula_l.stepFormula
        ![a, bound, key, history, output] ↔
      key ∈ TextbookEBoundedDomain_l bound ∧
        output = Constructible.textbookEStep a key history := by
  simp only [TextbookEBoundedFormula_l.stepFormula,
    Constructible.Model.SatisfiesIn,
    Constructible.Model.satisfiesIn_rename]
  have hDomainAssignment :
      (fun position => ![a, bound, key, history, output]
        (![(0 : Fin 5), (1 : Fin 5), (2 : Fin 5)] position)) =
        ![a, bound, key] := by
    funext position
    fin_cases position <;> rfl
  have hAssignment :
      (fun position => ![a, bound, key, history, output]
        (TextbookEBoundedFormula_l.stepRename position)) =
        ![a, key, history, output] := by
    funext position
    fin_cases position <;> rfl
  rw [hDomainAssignment, hAssignment,
    satisfiesIn_textbookEBoundedDomainFormula_stage_iff_l
      hθ hω ha hbound hkey,
    satisfiesIn_textbookEStepFormula_stage_iff_l
      hθ hω ha hkey hhistory houtput]
  constructor
  · rintro ⟨hDomain, _hTextbookDomain, hValue⟩
    exact ⟨hDomain, hValue⟩
  · rintro ⟨hDomain, hValue⟩
    exact ⟨hDomain,
      textbookEBoundedDomain_subset_textbookEDomain_l hBoundOmega hDomain,
      hValue⟩

/-- 截断关系的前驱在后继极限层中封闭。 -/
theorem textbookEBoundedRelation_predecessorsClosedIn_stage_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) {bound : ZFSet.{u}}
    (hbound : bound ∈ LStageZF θ) :
    Constructible.PredecessorsClosedIn (LStageZF θ : Set ZFSet.{u})
      (TextbookEBoundedDomain_l bound)
      (TextbookEBoundedRelation_l bound) := by
  intro _right _hright left hleft hrelation
  rcases ZFSet.mem_prod.mp hleft with
    ⟨code, hcodeOmega, arity, harityBound, rfl⟩
  have homegaStage : Constructible.textbookEOmegaZF ∈ LStageZF θ :=
    omega_toZFSet_mem_stage_l hω
  exact orderedPair_mem_LStageZF_of_isSuccLimit hθ
    ((LStageZF_isTransitive θ).mem_trans hcodeOmega homegaStage)
    ((LStageZF_isTransitive θ).mem_trans harityBound hbound)

/-- 截断参数下的 E 单步函数与插入界参数后的公式绝对。 -/
theorem textbookEBoundedStep_absoluteAt_stage_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) {a bound : ZFSet.{u}}
    (ha : a ∈ LStageZF θ) (hbound : bound ∈ LStageZF θ)
    (hBoundOmega : bound ⊆ Constructible.textbookEOmegaZF) :
    Constructible.Model.TextbookStepAbsoluteAt
      (LStageZF θ : Set ZFSet.{u}) ![a, bound]
      (TextbookEBoundedDomain_l bound) (Constructible.textbookEStep a)
      TextbookEBoundedFormula_l.stepFormula := by
  constructor
  · intro key _hkeyStage hkeyDomain history hhistoryStage
    exact textbookEStep_mem_LStageZF_l hθ ha hhistoryStage
      (textbookEBoundedDomain_subset_textbookEDomain_l
        hBoundOmega hkeyDomain)
  · intro key history output hkeyStage hhistoryStage houtputStage
    have hAssignment :
        snoc (snoc (snoc ![a, bound] key) history) output =
          ![a, bound, key, history, output] := by
      funext position
      fin_cases position <;> rfl
    rw [hAssignment]
    exact satisfiesIn_textbookEBoundedStepFormula_stage_iff_l
      hθ hω ha hbound hBoundOmega hkeyStage hhistoryStage houtputStage

/-- 通用最小闭包公式在截断参数处识别真实局部递归域。 -/
theorem satisfiesIn_textbookEBoundedLocalDomainFormula_stage_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) {a bound key domain : ZFSet.{u}}
    (ha : a ∈ LStageZF θ) (hbound : bound ∈ LStageZF θ)
    (hBoundOmega : bound ⊆ Constructible.textbookEOmegaZF)
    (hkey : key ∈ LStageZF θ)
    (hkeyDomain : key ∈ TextbookEBoundedDomain_l bound)
    (hdomain : domain ∈ LStageZF θ)
    (hLocalDomain : Constructible.localRecursionDomain
      (TextbookEBoundedDomain_l bound)
      (TextbookEBoundedRelation_l bound)
      (textbookEBoundedRelation_hasSetPredecessorsOn_l hBoundOmega) key ∈
        LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        (Constructible.Model.localDomainFormula
          TextbookEBoundedFormula_l.domainFormula
          TextbookEBoundedFormula_l.relationFormula)
        ![a, bound, key, domain] ↔
      domain = Constructible.localRecursionDomain
        (TextbookEBoundedDomain_l bound)
        (TextbookEBoundedRelation_l bound)
        (textbookEBoundedRelation_hasSetPredecessorsOn_l hBoundOmega) key := by
  have hParameters : ∀ position : Fin 2,
      ![a, bound] position ∈ LStageZF θ := by
    intro position
    fin_cases position
    · exact ha
    · exact hbound
  have hClass : ∀ z, z ∈ LStageZF θ →
      (Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
          TextbookEBoundedFormula_l.domainFormula (snoc ![a, bound] z) ↔
        z ∈ TextbookEBoundedDomain_l bound) := by
    intro z hz
    have hAssignment : snoc ![a, bound] z = ![a, bound, z] := by
      funext position
      fin_cases position <;> rfl
    rw [hAssignment]
    exact satisfiesIn_textbookEBoundedDomainFormula_stage_iff_l
      hθ hω ha hbound hz
  have hRelation : ∀ y, y ∈ LStageZF θ → ∀ z, z ∈ LStageZF θ →
      (Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
          TextbookEBoundedFormula_l.relationFormula
          (snoc (snoc ![a, bound] y) z) ↔
        Constructible.ClassRel (TextbookEBoundedRelation_l bound) y z) := by
    intro y hy z hz
    have hAssignment : snoc (snoc ![a, bound] y) z =
        ![a, bound, y, z] := by
      funext position
      fin_cases position <;> rfl
    rw [hAssignment]
    exact satisfiesIn_textbookEBoundedRelationFormula_stage_iff_l
      hθ hω ha hbound hBoundOmega hy hz
  have hSemantic :=
    Constructible.Model.satisfiesIn_localDomainFormula_iff_eq_localRecursionDomain
      (LStageZF_isTransitive θ)
      TextbookEBoundedFormula_l.domainFormula
      TextbookEBoundedFormula_l.relationFormula ![a, bound]
      hClass hRelation
      (textbookEBoundedRelation_isRelationOn_l bound)
      (textbookEBoundedRelation_hasSetPredecessorsOn_l hBoundOmega)
      (textbookEBoundedRelation_predecessorsClosedIn_stage_l hθ hω hbound)
      hkey hkeyDomain hdomain hLocalDomain
  have hAssignment : snoc (snoc ![a, bound] key) domain =
      ![a, bound, key, domain] := by
    funext position
    fin_cases position <;> rfl
  simpa only [hAssignment] using hSemantic

/-- 规范有限截断解图在同一后继极限层中满足对象语言局部解公式。 -/
theorem satisfiesIn_textbookEBoundedLocalSolutionFormula_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) {a : ZFSet.{u}}
    (ha : a ∈ LStageZF θ) (code arity bound : Nat)
    (hArity : arity < bound) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      (Constructible.Model.localSolutionFormula
        TextbookEBoundedFormula_l.domainFormula
        TextbookEBoundedFormula_l.relationFormula
        TextbookEBoundedFormula_l.stepFormula)
      ![a, natCode bound,
        ZFSet.pair (natCode code) (natCode arity),
        (textbookEBoundedLocalSolution_l a code arity bound hArity).graph] := by
  let boundSet : ZFSet.{u} := natCode bound
  let key : ZFSet.{u} := ZFSet.pair (natCode code) (natCode arity)
  let hBoundOmega : boundSet ⊆ Constructible.textbookEOmegaZF :=
    natCode_subset_textbookEOmega_l bound
  let hRelation := textbookEBoundedRelation_isWellFoundedSetLikeOn_l hBoundOmega
  let solution := textbookEBoundedLocalSolution_l a code arity bound hArity
  let localDomain := Constructible.localRecursionDomain
    (TextbookEBoundedDomain_l boundSet)
    (TextbookEBoundedRelation_l boundSet) hRelation.2.2 key
  have hboundStage : boundSet ∈ LStageZF θ :=
    natCode_mem_LStageZF_of_isSuccLimit hθ bound
  have hkeyStage : key ∈ LStageZF θ :=
    orderedPair_mem_LStageZF_of_isSuccLimit hθ
      (natCode_mem_LStageZF_of_isSuccLimit hθ code)
      (natCode_mem_LStageZF_of_isSuccLimit hθ arity)
  have hkeyDomain : key ∈ TextbookEBoundedDomain_l boundSet :=
    textbookEKey_mem_boundedDomain_l code arity bound hArity
  have hlocalDomainStage : localDomain ∈ LStageZF θ :=
    textbookEBounded_localRecursionDomain_mem_LStageZF_l
      hθ code arity bound hArity
  have hvalueStage : ∀ input, input ∈ localDomain →
      solution.value input ∈ LStageZF θ :=
    textbookEBoundedLocalSolution_value_mem_LStageZF_l
      hθ ha code arity bound hArity solution
  have hgraphStage : solution.graph ∈ LStageZF θ :=
    textbookEBoundedLocalSolution_graph_mem_LStageZF_l
      hθ ha code arity bound hArity solution
  have hParameters : ∀ position : Fin 2,
      ![a, boundSet] position ∈ LStageZF θ := by
    intro position
    fin_cases position
    · exact ha
    · exact hboundStage
  have hClass : ∀ z, z ∈ LStageZF θ →
      (Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
          TextbookEBoundedFormula_l.domainFormula
          (snoc ![a, boundSet] z) ↔
        z ∈ TextbookEBoundedDomain_l boundSet) := by
    intro z hz
    have hAssignment : snoc ![a, boundSet] z = ![a, boundSet, z] := by
      funext position
      fin_cases position <;> rfl
    rw [hAssignment]
    exact satisfiesIn_textbookEBoundedDomainFormula_stage_iff_l
      hθ hω ha hboundStage hz
  have hRelationFormula : ∀ y, y ∈ LStageZF θ →
      ∀ z, z ∈ LStageZF θ →
      (Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
          TextbookEBoundedFormula_l.relationFormula
          (snoc (snoc ![a, boundSet] y) z) ↔
        Constructible.ClassRel (TextbookEBoundedRelation_l boundSet) y z) := by
    intro y hy z hz
    have hAssignment : snoc (snoc ![a, boundSet] y) z =
        ![a, boundSet, y, z] := by
      funext position
      fin_cases position <;> rfl
    rw [hAssignment]
    exact satisfiesIn_textbookEBoundedRelationFormula_stage_iff_l
      hθ hω ha hboundStage hBoundOmega hy hz
  apply (Constructible.Model.satisfiesIn_localSolutionFormula_iff
    (LStageZF_isTransitive θ)
    TextbookEBoundedFormula_l.domainFormula
    TextbookEBoundedFormula_l.relationFormula
    TextbookEBoundedFormula_l.stepFormula
    ![a, boundSet] key solution.graph
    hParameters hkeyStage hgraphStage).mpr
  refine ⟨localDomain, hlocalDomainStage, ?_, ?_, ?_⟩
  · have hAssignment : snoc (snoc ![a, boundSet] key) localDomain =
        ![a, boundSet, key, localDomain] := by
      funext position
      fin_cases position <;> rfl
    rw [hAssignment]
    exact (satisfiesIn_textbookEBoundedLocalDomainFormula_stage_iff_l
      hθ hω ha hboundStage hBoundOmega hkeyStage hkeyDomain
      hlocalDomainStage hlocalDomainStage).mpr rfl
  · constructor
    · intro input _hinputStage hinputDomain
      refine ⟨solution.value input, hvalueStage input hinputDomain, ?_, ?_⟩
      · rw [solution.graph_eq]
        exact Constructible.pair_mem_predecessorRestrictionGraph
          solution.value hinputDomain
      · intro other _hotherStage hotherGraph
        rw [solution.graph_eq] at hotherGraph
        rcases Constructible.mem_predecessorRestrictionGraph_iff.mp
            hotherGraph with ⟨source, _hsourceDomain, hpair⟩
        rcases ZFSet.pair_inj.mp hpair with ⟨hsource, hvalue⟩
        subst source
        exact hvalue.symm
    · intro pair _hpairStage hpairGraph
      rw [solution.graph_eq] at hpairGraph
      rcases Constructible.mem_predecessorRestrictionGraph_iff.mp
          hpairGraph with ⟨input, hinputDomain, hpair⟩
      have hinputStage : input ∈ LStageZF θ :=
        (LStageZF_isTransitive θ).mem_trans hinputDomain hlocalDomainStage
      exact ⟨input, hinputStage, hinputDomain, solution.value input,
        hvalueStage input hinputDomain, hpair.symm⟩
  · intro top htopStage htopDomain
    let restriction := Constructible.predecessorRestrictionGraph
      (Constructible.displayedPredecessors
        (TextbookEBoundedDomain_l boundSet)
        (TextbookEBoundedRelation_l boundSet) hRelation.2.2 top)
      solution.value
    have htopDomainSet : top ∈ TextbookEBoundedDomain_l boundSet :=
      Constructible.localRecursionDomain_subset
        hRelation.2.2 hkeyDomain htopDomain
    have hrestrictionStage : restriction ∈ LStageZF θ := by
      apply predecessorRestrictionGraph_mem_LStageZF_of_finite_l hθ
        (textbookEBounded_displayedPredecessors_mem_LStageZF_l
          hθ hboundStage hBoundOmega htopDomainSet)
        (textbookEBounded_displayedPredecessors_externallyFinite_l
          bound htopDomainSet)
      intro input hinputPredecessor
      have hinputRelation :=
        (Constructible.displayedPredecessors_spec
          hRelation.2.2 htopDomainSet input).mp hinputPredecessor |>.2
      exact hvalueStage input
        (Constructible.localRecursionDomain_predecessorClosed
          hRelation.1 hRelation.2.2 hkeyDomain htopDomain hinputRelation)
    have htopValueStage : solution.value top ∈ LStageZF θ :=
      hvalueStage top htopDomain
    refine ⟨restriction, hrestrictionStage, solution.value top,
      htopValueStage, ?_, ?_, ?_⟩
    · intro pair _hpairStage
      constructor
      · intro hpairRestriction
        rcases Constructible.mem_predecessorRestrictionGraph_iff.mp
            hpairRestriction with ⟨input, hinputPredecessor, hpair⟩
        have hinputSpec :=
          (Constructible.displayedPredecessors_spec
            hRelation.2.2 htopDomainSet input).mp hinputPredecessor
        have hinputDomain :=
          Constructible.localRecursionDomain_predecessorClosed
            hRelation.1 hRelation.2.2 hkeyDomain htopDomain hinputSpec.2
        have hinputStage : input ∈ LStageZF θ :=
          (LStageZF_isTransitive θ).mem_trans hinputDomain hlocalDomainStage
        have hinputValueStage := hvalueStage input hinputDomain
        refine ⟨?_, input, hinputStage, solution.value input,
          hinputValueStage, hpair.symm, ?_, ?_⟩
        · rw [solution.graph_eq]
          have hmember := Constructible.pair_mem_predecessorRestrictionGraph
            solution.value hinputDomain
          rw [hpair] at hmember
          exact hmember
        · exact (hClass input hinputStage).mpr hinputSpec.1
        · exact (hRelationFormula input hinputStage top htopStage).mpr
            hinputSpec.2
      · rintro ⟨hpairGraph, input, hinputStage, output, _houtputStage,
          hpairEq, hinputFormula, hrelationFormula⟩
        have hinputDomainSet : input ∈ TextbookEBoundedDomain_l boundSet :=
          (hClass input hinputStage).mp hinputFormula
        have hinputRelation : Constructible.ClassRel
            (TextbookEBoundedRelation_l boundSet) input top :=
          (hRelationFormula input hinputStage top htopStage).mp
            hrelationFormula
        have hinputPredecessor : input ∈ Constructible.displayedPredecessors
            (TextbookEBoundedDomain_l boundSet)
            (TextbookEBoundedRelation_l boundSet) hRelation.2.2 top :=
          (Constructible.displayedPredecessors_spec
            hRelation.2.2 htopDomainSet input).mpr
              ⟨hinputDomainSet, hinputRelation⟩
        rw [solution.graph_eq] at hpairGraph
        rcases Constructible.mem_predecessorRestrictionGraph_iff.mp
            hpairGraph with ⟨source, _hsourceDomain, hsourcePair⟩
        have hpairs : ZFSet.pair source (solution.value source) =
            ZFSet.pair input output := hsourcePair.trans hpairEq
        rcases ZFSet.pair_inj.mp hpairs with ⟨hsource, houtput⟩
        subst source
        subst output
        apply Constructible.mem_predecessorRestrictionGraph_iff.mpr
        exact ⟨input, hinputPredecessor, hpairEq.symm⟩
    · rw [solution.graph_eq]
      exact Constructible.pair_mem_predecessorRestrictionGraph
        solution.value htopDomain
    · have hStep := textbookEBoundedStep_absoluteAt_stage_l
        hθ hω ha hboundStage hBoundOmega
      apply (hStep.2 top restriction (solution.value top)
        htopStage hrestrictionStage htopValueStage).mpr
      refine ⟨htopDomainSet, ?_⟩
      simpa only [restriction] using solution.satisfies top htopDomain

/-- 任意层内截断局部解公式见证都解码成真实教材局部解。 -/
theorem exists_textbookEBoundedLocalSolution_of_satisfiesIn_stage_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) (code arity bound : Nat)
    {a graph : ZFSet.{u}} (ha : a ∈ LStageZF θ)
    (hgraph : graph ∈ LStageZF θ)
    (hArity : arity < bound)
    (hformula : Constructible.Model.SatisfiesIn
      (LStageZF θ : Set ZFSet.{u})
      (Constructible.Model.localSolutionFormula
        TextbookEBoundedFormula_l.domainFormula
        TextbookEBoundedFormula_l.relationFormula
        TextbookEBoundedFormula_l.stepFormula)
      ![a, natCode bound,
        ZFSet.pair (natCode code) (natCode arity), graph]) :
    ∃ solution : Constructible.TextbookLocalSolution
        (TextbookEBoundedDomain_l (natCode bound : ZFSet.{u}))
        (TextbookEBoundedRelation_l (natCode bound : ZFSet.{u}))
        (textbookEBoundedRelation_hasSetPredecessorsOn_l
          (natCode_subset_textbookEOmega_l bound))
        (Constructible.textbookEStep a)
        (ZFSet.pair (natCode code) (natCode arity)),
      solution.graph = graph := by
  let boundSet : ZFSet.{u} := natCode bound
  let key : ZFSet.{u} := ZFSet.pair (natCode code) (natCode arity)
  let hBoundOmega : boundSet ⊆ Constructible.textbookEOmegaZF :=
    natCode_subset_textbookEOmega_l bound
  let hRelation := textbookEBoundedRelation_isWellFoundedSetLikeOn_l hBoundOmega
  have hboundStage : boundSet ∈ LStageZF θ :=
    natCode_mem_LStageZF_of_isSuccLimit hθ bound
  have hkeyStage : key ∈ LStageZF θ :=
    orderedPair_mem_LStageZF_of_isSuccLimit hθ
      (natCode_mem_LStageZF_of_isSuccLimit hθ code)
      (natCode_mem_LStageZF_of_isSuccLimit hθ arity)
  have hkeyDomain : key ∈ TextbookEBoundedDomain_l boundSet :=
    textbookEKey_mem_boundedDomain_l code arity bound hArity
  have hParameters : ∀ position : Fin 2,
      ![a, boundSet] position ∈ LStageZF θ := by
    intro position
    fin_cases position
    · exact ha
    · exact hboundStage
  have hClass : ∀ z, z ∈ LStageZF θ →
      (Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
          TextbookEBoundedFormula_l.domainFormula
          (snoc ![a, boundSet] z) ↔
        z ∈ TextbookEBoundedDomain_l boundSet) := by
    intro z hz
    have hAssignment : snoc ![a, boundSet] z = ![a, boundSet, z] := by
      funext position
      fin_cases position <;> rfl
    rw [hAssignment]
    exact satisfiesIn_textbookEBoundedDomainFormula_stage_iff_l
      hθ hω ha hboundStage hz
  have hRelationFormula : ∀ y, y ∈ LStageZF θ →
      ∀ z, z ∈ LStageZF θ →
      (Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
          TextbookEBoundedFormula_l.relationFormula
          (snoc (snoc ![a, boundSet] y) z) ↔
        Constructible.ClassRel (TextbookEBoundedRelation_l boundSet) y z) := by
    intro y hy z hz
    have hAssignment : snoc (snoc ![a, boundSet] y) z =
        ![a, boundSet, y, z] := by
      funext position
      fin_cases position <;> rfl
    rw [hAssignment]
    exact satisfiesIn_textbookEBoundedRelationFormula_stage_iff_l
      hθ hω ha hboundStage hBoundOmega hy hz
  have hformula' : Constructible.Model.SatisfiesIn
      (LStageZF θ : Set ZFSet.{u})
      (Constructible.Model.localSolutionFormula
        TextbookEBoundedFormula_l.domainFormula
        TextbookEBoundedFormula_l.relationFormula
        TextbookEBoundedFormula_l.stepFormula)
      (snoc (snoc ![a, boundSet] key) graph) := by
    have hAssignment : snoc (snoc ![a, boundSet] key) graph =
        ![a, boundSet, key, graph] := by
      funext position
      fin_cases position <;> rfl
    rw [hAssignment]
    simpa only [boundSet, key] using hformula
  exact exists_textbookLocalSolution_of_satisfiesIn_stage_l
    hθ TextbookEBoundedFormula_l.domainFormula
    TextbookEBoundedFormula_l.relationFormula
    TextbookEBoundedFormula_l.stepFormula ![a, boundSet]
    hRelation hParameters hClass hRelationFormula
    (textbookEBoundedRelation_predecessorsClosedIn_stage_l
      hθ hω hboundStage)
    (textbookEBoundedStep_absoluteAt_stage_l
      hθ hω ha hboundStage hBoundOmega)
    hkeyStage hkeyDomain hgraph
    (textbookEBounded_localRecursionDomain_mem_LStageZF_l
      hθ code arity bound hArity)
    hformula'

/-- 截断递归值公式在安全锥中精确给出完整 textbook E 值。 -/
theorem satisfiesIn_textbookEBoundedRecursionValueFormula_natCode_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) (code arity bound : Nat)
    {a output : ZFSet.{u}} (ha : a ∈ LStageZF θ)
    (houtput : output ∈ LStageZF θ) (hSafe : arity + code < bound) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        TextbookEBoundedFormula_l.recursionValueFormula
        ![a, natCode bound,
          ZFSet.pair (natCode code) (natCode arity), output] ↔
      output = Constructible.textbookEZF a (natCode arity) (natCode code) := by
  let boundSet : ZFSet.{u} := natCode bound
  let key : ZFSet.{u} := ZFSet.pair (natCode code) (natCode arity)
  have hArity : arity < bound := by omega
  have hboundStage : boundSet ∈ LStageZF θ :=
    natCode_mem_LStageZF_of_isSuccLimit hθ bound
  have hkeyStage : key ∈ LStageZF θ :=
    orderedPair_mem_LStageZF_of_isSuccLimit hθ
      (natCode_mem_LStageZF_of_isSuccLimit hθ code)
      (natCode_mem_LStageZF_of_isSuccLimit hθ arity)
  have hParameters : ∀ position : Fin 2,
      ![a, boundSet] position ∈ LStageZF θ := by
    intro position
    fin_cases position
    · exact ha
    · exact hboundStage
  rw [TextbookEBoundedFormula_l.recursionValueFormula]
  have hSemantic := Constructible.Model.satisfiesIn_recursionValueFormula_iff
    (LStageZF_isTransitive θ)
    TextbookEBoundedFormula_l.domainFormula
    TextbookEBoundedFormula_l.relationFormula
    TextbookEBoundedFormula_l.stepFormula
    ![a, boundSet] key output hParameters hkeyStage houtput
  have hAssignment : snoc (snoc ![a, boundSet] key) output =
      ![a, boundSet, key, output] := by
    funext position
    fin_cases position <;> rfl
  rw [hAssignment] at hSemantic
  rw [show ![a, natCode bound,
      ZFSet.pair (natCode code) (natCode arity), output] =
      ![a, boundSet, key, output] by rfl,
    hSemantic]
  constructor
  · rintro ⟨_hkeyDomainFormula, graph, hgraphStage,
      hlocalFormula, hpairGraph⟩
    rcases exists_textbookEBoundedLocalSolution_of_satisfiesIn_stage_l
        hθ hω code arity bound ha hgraphStage hArity hlocalFormula with
      ⟨solution, hsolutionGraph⟩
    have hpairSolution : ZFSet.pair key output ∈ solution.graph := by
      rw [hsolutionGraph]
      exact hpairGraph
    rw [solution.graph_eq] at hpairSolution
    rcases Constructible.mem_predecessorRestrictionGraph_iff.mp
        hpairSolution with ⟨source, _hsourceDomain, hsourcePair⟩
    have hcoordinates := ZFSet.pair_inj.mp hsourcePair
    have houtputValue : output = solution.value key := by
      rw [hcoordinates.1] at hcoordinates
      exact hcoordinates.2.symm
    exact houtputValue.trans
      (textbookEBoundedLocalSolution_eq_textbookEZF_of_add_lt_l
        code arity bound hArity solution
        code arity
        (Constructible.mem_localRecursionDomain_iff.mpr (Or.inl rfl)) hSafe)
  · intro houtputValue
    let solution := textbookEBoundedLocalSolution_l
      a code arity bound hArity
    refine ⟨?_, solution.graph,
      textbookEBoundedLocalSolution_graph_mem_stage_l
        hθ ha code arity bound hArity, ?_, ?_⟩
    · have hAssignment' : snoc ![a, boundSet] key =
          ![a, boundSet, key] := by
        funext position
        fin_cases position <;> rfl
      rw [hAssignment']
      exact (satisfiesIn_textbookEBoundedDomainFormula_stage_iff_l
        hθ hω ha hboundStage hkeyStage).mpr
          (textbookEKey_mem_boundedDomain_l code arity bound hArity)
    · have hLocal := satisfiesIn_textbookEBoundedLocalSolutionFormula_l
        hθ hω ha code arity bound hArity
      have hLocalAssignment :
          snoc (snoc ![a, boundSet] key) solution.graph =
            ![a, natCode bound,
              ZFSet.pair (natCode code) (natCode arity),
              (textbookEBoundedLocalSolution_l
                a code arity bound hArity).graph] := by
        funext position
        fin_cases position <;> rfl
      rw [hLocalAssignment]
      exact hLocal
    · rw [solution.graph_eq]
      apply Constructible.mem_predecessorRestrictionGraph_iff.mpr
      refine ⟨key,
        Constructible.mem_localRecursionDomain_iff.mpr (Or.inl rfl), ?_⟩
      apply congrArg (ZFSet.pair key)
      rw [textbookEBoundedLocalSolution_eq_textbookEZF_of_add_lt_l
        code arity bound hArity solution
        code arity
        (Constructible.mem_localRecursionDomain_iff.mpr (Or.inl rfl)) hSafe]
      exact houtputValue.symm

/-- 公开的层稳定 E 公式在标准自然数码处具有完整 textbook E 语义。 -/
theorem satisfiesIn_textbookEBoundedValueFormula_natCode_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) (arity code : Nat)
    {a output : ZFSet.{u}} (ha : a ∈ LStageZF θ)
    (houtput : output ∈ LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        TextbookEBoundedFormula_l.valueFormula
        ![a, natCode arity, natCode code, output] ↔
      output = Constructible.textbookEZF a (natCode arity) (natCode code) := by
  simp only [TextbookEBoundedFormula_l.valueFormula,
    Constructible.Model.SatisfiesIn]
  constructor
  · rintro ⟨omega, homegaStage, sum, hsumStage, bound, hboundStage,
      key, hkeyStage, hbody⟩
    have hBodyAssignment :
        snoc (snoc (snoc (snoc
          ![a, natCode arity, natCode code, output]
          omega) sum) bound) key =
        ![a, natCode arity, natCode code, output,
          omega, sum, bound, key] := by
      funext position
      fin_cases position <;> rfl
    rw [hBodyAssignment] at hbody
    simp only [TextbookEBoundedFormula_l.valueBody,
      Constructible.Model.SatisfiesIn,
      Constructible.Model.satisfiesIn_rename] at hbody
    rcases hbody with ⟨hAddition, hSuccessor, hPair, hRecursion⟩
    have hAdditionAssignment :
        (fun position =>
          ![a, natCode arity, natCode code, output,
            omega, sum, bound, key]
            (![(4 : Fin 8), (1 : Fin 8), (2 : Fin 8), (5 : Fin 8)]
              position)) =
          ![omega, natCode arity, natCode code, sum] := by
      funext position
      fin_cases position <;> rfl
    rw [hAdditionAssignment] at hAddition
    have hAdditionMembers : ∀ position : Fin 4,
        ![omega, natCode arity, natCode code, sum] position ∈
          LStageZF θ := by
      intro position
      fin_cases position
      · exact homegaStage
      · exact natCode_mem_LStageZF_of_isSuccLimit hθ arity
      · exact natCode_mem_LStageZF_of_isSuccLimit hθ code
      · exact hsumStage
    have homegaFormula : Constructible.Model.SatisfiesIn
        (LStageZF θ : Set ZFSet.{u})
        (Constructible.Model.standardOmegaAt (0 : Fin 4))
        ![omega, natCode arity, natCode code, sum] := by
      simpa only [Constructible.TextbookNatFormula.natAddFormula,
        Constructible.Model.SatisfiesIn] using hAddition.1
    have homega : omega = Ordinal.omega0.toZFSet :=
      (satisfiesIn_standardOmegaAt_stage_iff_l hθ hω (0 : Fin 4)
        ![omega, natCode arity, natCode code, sum]
        hAdditionMembers).mp homegaFormula
    subst omega
    have hsum : sum = natCode (arity + code) :=
      (satisfiesIn_natAddFormula_stage_natCode_iff_l
        hθ hω arity code hsumStage).mp hAddition
    subst sum
    have hFullAssignment : ∀ position : Fin 8,
        ![a, natCode arity, natCode code, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}),
          natCode (arity + code), bound, key] position ∈ LStageZF θ := by
      intro position
      fin_cases position
      · exact ha
      · exact natCode_mem_LStageZF_of_isSuccLimit hθ arity
      · exact natCode_mem_LStageZF_of_isSuccLimit hθ code
      · exact houtput
      · exact omega_toZFSet_mem_stage_l hω
      · exact natCode_mem_LStageZF_of_isSuccLimit hθ (arity + code)
      · exact hboundStage
      · exact hkeyStage
    have hboundRaw :=
      (satisfiesIn_successorAt_stage_iff_l
        (6 : Fin 8) (5 : Fin 8)
        ![a, natCode arity, natCode code, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}),
          natCode (arity + code), bound, key]
        hFullAssignment).mp hSuccessor
    have hbound : bound = natCode (arity + code + 1) :=
      hboundRaw.trans (natCode_succ_eq_insert (arity + code)).symm
    subst bound
    have hkey :=
      (satisfiesIn_kuratowskiPairEqAt_stage_iff_l
        (7 : Fin 8) (2 : Fin 8) (1 : Fin 8)
        ![a, natCode arity, natCode code, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}),
          natCode (arity + code), natCode (arity + code + 1), key]
        hFullAssignment).mp hPair
    have hkey' : key = ZFSet.pair (natCode code) (natCode arity) := by
      simpa using hkey
    subst key
    have hRecursionAssignment :
        (fun position =>
          ![a, natCode arity, natCode code, output,
            (Ordinal.omega0.toZFSet : ZFSet.{u}),
            natCode (arity + code), natCode (arity + code + 1),
            ZFSet.pair (natCode code) (natCode arity)]
            (![(0 : Fin 8), (6 : Fin 8), (7 : Fin 8), (3 : Fin 8)]
              position)) =
          ![a, natCode (arity + code + 1),
            ZFSet.pair (natCode code) (natCode arity), output] := by
      funext position
      fin_cases position <;> rfl
    rw [hRecursionAssignment] at hRecursion
    exact (satisfiesIn_textbookEBoundedRecursionValueFormula_natCode_iff_l
      hθ hω code arity (arity + code + 1) ha houtput (by omega)).mp
        hRecursion
  · intro hValue
    let omega : ZFSet.{u} := Ordinal.omega0.toZFSet
    let sum : ZFSet.{u} := natCode (arity + code)
    let bound : ZFSet.{u} := natCode (arity + code + 1)
    let key : ZFSet.{u} := ZFSet.pair (natCode code) (natCode arity)
    have homegaStage : omega ∈ LStageZF θ := omega_toZFSet_mem_stage_l hω
    have hsumStage : sum ∈ LStageZF θ :=
      natCode_mem_LStageZF_of_isSuccLimit hθ (arity + code)
    have hboundStage : bound ∈ LStageZF θ :=
      natCode_mem_LStageZF_of_isSuccLimit hθ (arity + code + 1)
    have hkeyStage : key ∈ LStageZF θ :=
      orderedPair_mem_LStageZF_of_isSuccLimit hθ
        (natCode_mem_LStageZF_of_isSuccLimit hθ code)
        (natCode_mem_LStageZF_of_isSuccLimit hθ arity)
    refine ⟨omega, homegaStage, sum, hsumStage, bound, hboundStage,
      key, hkeyStage, ?_⟩
    have hBodyAssignment :
        snoc (snoc (snoc (snoc
          ![a, natCode arity, natCode code, output]
          omega) sum) bound) key =
        ![a, natCode arity, natCode code, output,
          omega, sum, bound, key] := by
      funext position
      fin_cases position <;> rfl
    rw [hBodyAssignment]
    simp only [TextbookEBoundedFormula_l.valueBody,
      Constructible.Model.SatisfiesIn,
      Constructible.Model.satisfiesIn_rename]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hAdditionAssignment :
          (fun position =>
            ![a, natCode arity, natCode code, output,
              omega, sum, bound, key]
              (![(4 : Fin 8), (1 : Fin 8), (2 : Fin 8), (5 : Fin 8)]
                position)) =
            ![omega, natCode arity, natCode code, sum] := by
        funext position
        fin_cases position <;> rfl
      rw [hAdditionAssignment]
      exact (satisfiesIn_natAddFormula_stage_natCode_iff_l
        hθ hω arity code hsumStage).mpr rfl
    · have hFullAssignment : ∀ position : Fin 8,
          ![a, natCode arity, natCode code, output,
            omega, sum, bound, key] position ∈ LStageZF θ := by
        intro position
        fin_cases position
        · exact ha
        · exact natCode_mem_LStageZF_of_isSuccLimit hθ arity
        · exact natCode_mem_LStageZF_of_isSuccLimit hθ code
        · exact houtput
        · exact homegaStage
        · exact hsumStage
        · exact hboundStage
        · exact hkeyStage
      apply (satisfiesIn_successorAt_stage_iff_l
        (6 : Fin 8) (5 : Fin 8)
        ![a, natCode arity, natCode code, output,
          omega, sum, bound, key] hFullAssignment).mpr
      change (natCode (arity + code + 1) : ZFSet.{u}) =
        insert (natCode (arity + code)) (natCode (arity + code))
      exact natCode_succ_eq_insert (arity + code)
    · have hFullAssignment : ∀ position : Fin 8,
          ![a, natCode arity, natCode code, output,
            omega, sum, bound, key] position ∈ LStageZF θ := by
        intro position
        fin_cases position
        · exact ha
        · exact natCode_mem_LStageZF_of_isSuccLimit hθ arity
        · exact natCode_mem_LStageZF_of_isSuccLimit hθ code
        · exact houtput
        · exact homegaStage
        · exact hsumStage
        · exact hboundStage
        · exact hkeyStage
      apply (satisfiesIn_kuratowskiPairEqAt_stage_iff_l
        (7 : Fin 8) (2 : Fin 8) (1 : Fin 8)
        ![a, natCode arity, natCode code, output,
          omega, sum, bound, key] hFullAssignment).mpr
      rfl
    · have hRecursionAssignment :
          (fun position =>
            ![a, natCode arity, natCode code, output,
              omega, sum, bound, key]
              (![(0 : Fin 8), (6 : Fin 8), (7 : Fin 8), (3 : Fin 8)]
                position)) =
            ![a, natCode (arity + code + 1),
              ZFSet.pair (natCode code) (natCode arity), output] := by
        funext position
        fin_cases position <;> rfl
      rw [hRecursionAssignment]
      exact (satisfiesIn_textbookEBoundedRecursionValueFormula_natCode_iff_l
        hθ hω code arity (arity + code + 1) ha houtput (by omega)).mpr
          hValue

end

end YesMetaZFC.BMS.ConstructibleBridge
