import BMSConstructibleBridge.SecondOrderProgramExpansionEarlierParentCut
import BMSConstructibleBridge.SecondOrderProgramExpansionInsideCopies
import BMSConstructibleBridge.SecondOrderProgramExpansionSuccess
import BMSConstructibleBridge.SecondOrderProgramParentRelocation
import BMSConstructibleBridge.SecondOrderProgramUniformParentCandidate
import BMSConstructibleBridge.SecondOrderProgramUniformAncestorEntries
import BMSConstructibleBridge.SecondOrderProgramExpansionInsideCopyEntryOrder
import BMSConstructibleBridge.SecondOrderProgramExpansionCopyBoundaryActualIteration
import BMSConstructibleBridge.SecondOrderProgramExpansionCopyRootParent
import BMSConstructibleBridge.SecondOrderProgramAscendingAncestor
import BMSConstructibleBridge.SecondOrderProgramBlockCoordinates
import BMSConstructibleBridge.SecondOrderProgramUniformParentPrefix
import BMSConstructibleBridge.SecondOrderListInduction
import BMSConstructibleBridge.SecondOrderProgramTrimPositiveEntry
import BMSConstructibleBridge.SecondOrderProgramExpansionRawFirstEntry
import BMSConstructibleBridge.SecondOrderProgramTrimEntryBelow
import BMSConstructibleBridge.SecondOrderProgramExpansionSuccessRectangular

/-!
# 较早父边排除零号副本中的中间祖先候选

若实际目标的父列在较早副本，则零号副本首列与目标之间的任一候选祖先，
经完整展开中的同副本祖先对应会成为当前副本内不晚于首列的祖先，
与直接父列切断结论矛盾。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionEarlierParentCandidateCut

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderNumbers
open SecondOrderProgramSemantics
open SecondOrderProgramTotality
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramExpansion (expand_m)
open SecondOrderProgramExpansionSuccess (bad_m success_m)
open SecondOrderProgramAscending (ascending_m)
open SecondOrderProgramMaximalParentRow (maximal_m last_index_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramSubtraction (sub_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramOptionalLookup (optional_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramUniformParentPrefix (at_row_m at_row_syntax_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 父局部性公式的自由槽为
`[row, end, start, prefix, array, parentGraph]`。它断言区间 `(start,end)` 中每个目标
的实际父要么落在既定前缀 `prefix` 之前，要么仍落在该区间内。 -/
def row_locality_m : Formula signature_m []
    [.num, .num, .num, .num, .num, .set] :=
  .forallE .num (.imp
    (.conj
      (PrimitiveFormulas.lt_m (.fvar (.there (.there .here))) (.bvar .here))
      (PrimitiveFormulas.lt_m (.bvar .here) (.fvar (.there .here))))
    (.forallE .num (.imp
      (at_row_m (.fvar (.there (.there (.there (.there (.there .here))))))
        (.fvar (.there (.there (.there (.there .here))))) (.fvar .here)
        (.bvar (.there .here))
        (Term.app (σ := signature_m) .succ (.cons (.bvar .here) .nil)))
      (.disj
        (PrimitiveFormulas.lt_m (.bvar .here)
          (.fvar (.there (.there (.there .here)))))
        (.conj
          (.neg (PrimitiveFormulas.lt_m (.bvar .here)
            (.fvar (.there (.there .here)))))
          (PrimitiveFormulas.lt_m (.bvar .here) (.fvar (.there .here))))))))

/-- 行局部性实际是纯二阶算术公式；父图关系由原配对模板展开。 -/
theorem row_locality_language_m : language_m row_locality_m = true :=
  pure_language_m _ rfl

/-- 行局部性的语义形式：目标在开区间内时，父列位于既定好前缀或当前副本区间。 -/
def row_locality_l (P : set_l ℳ) (x goodBound start finish row : num_l ℳ) : Prop :=
  ∀ target, SecondOrderOrder.lt_l start target →
    SecondOrderOrder.lt_l target finish → ∀ found,
      relation_l P (value_l (value_l x row) target) (succ_l found) →
        SecondOrderOrder.lt_l found goodBound ∨
          (¬SecondOrderOrder.lt_l found start ∧ SecondOrderOrder.lt_l found finish)

/-- 若当前副本区间从好前缀界开始，则父程序的严格下降性直接给出局部性；
此分支涵盖复制号为零的全部行。 -/
theorem row_locality_at_prefix_l (hℳ : Theory.Models ℳ theory_m)
    {P : set_l ℳ} (hP : graph_semantics_l (graph_m parent_m) P)
    (x goodBound finish row : num_l ℳ) :
    row_locality_l P x goodBound goodBound finish row := by
  intro target hStart hTarget found hParent
  have hParentLt := SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hParent
  by_cases hGood : SecondOrderOrder.lt_l found goodBound
  · exact Or.inl hGood
  · exact Or.inr ⟨hGood, SecondOrderOrder.trans_l hℳ hParentLt hTarget⟩

private def row_locality_env (P : set_l ℳ) (x goodBound start finish : num_l ℳ) :
    Env ℳ [] [.num, .num, .num, .num, .set] := by
  let η₀ := (Env.empty (M := ℳ)).pushFree P
  let η₁ := η₀.pushFree x
  let η₂ := η₁.pushFree goodBound
  let η₃ := η₂.pushFree start
  exact η₃.pushFree finish

/-- 行局部性公式对齐到内部父图、前缀界与副本区间的语义。 -/
theorem row_locality_syntax_l (P : set_l ℳ) (x goodBound start finish row : num_l ℳ) :
    Formula.satisfies ((row_locality_env P x goodBound start finish).pushFree row)
      row_locality_m ↔
      row_locality_l P x goodBound start finish row := by
  simp only [row_locality_m, row_locality_l, Formula.satisfies, SecondOrderOrder.formula_l,
    row_locality_env, at_row_syntax_l, Term.eval, Arguments.eval,
    FirstOrder.Env.pushFree, FirstOrder.Env.pushBound, FirstOrder.Env.empty,
    FirstOrder.Assignment.push, and_imp]
  rfl

/-- 将行局部性归约为逐行强归纳步；归纳公式是上面的实际纯加乘公式。 -/
theorem row_locality_all_of_strong_step_l (hℳ : Theory.Models ℳ theory_m)
    (P : set_l ℳ) (x goodBound start finish : num_l ℳ)
    (hstep : ∀ row, (∀ s, SecondOrderOrder.lt_l s row →
      row_locality_l P x goodBound start finish s) →
        row_locality_l P x goodBound start finish row) :
    ∀ row, row_locality_l P x goodBound start finish row :=
  SecondOrderListInduction.strong_induct_l hℳ row_locality_m row_locality_language_m
    (row_locality_env P x goodBound start finish)
    (row_locality_l P x goodBound start finish)
    (fun row => row_locality_syntax_l P x goodBound start finish row) hstep

/-- 行号上界以下的局部性归纳；不要求上界及以上的行满足同一个归纳步。 -/
theorem row_locality_below_of_strong_step_l (hℳ : Theory.Models ℳ theory_m)
    (P : set_l ℳ) (x goodBound start finish bound : num_l ℳ)
    (hstep : ∀ row, SecondOrderOrder.lt_l row bound →
      (∀ s, SecondOrderOrder.lt_l s row →
        row_locality_l P x goodBound start finish s) →
      row_locality_l P x goodBound start finish row) :
    ∀ row, SecondOrderOrder.lt_l row bound →
      row_locality_l P x goodBound start finish row :=
  SecondOrderListInduction.strong_induct_below_l hℳ row_locality_m row_locality_language_m
    (row_locality_env P x goodBound start finish)
    (row_locality_l P x goodBound start finish)
    (fun row => row_locality_syntax_l P x goodBound start finish row) bound hstep

private def ancestor_locality_m {Γ Δ : SortContext signature_m}
    (M : Term signature_m Γ Δ .set) (x row goodBound start finish target :
      Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .imp (PrimitiveFormulas.lt_m start target)
    (.imp (PrimitiveFormulas.lt_m target finish)
      (.imp (.neg (SecondOrderProgramUniformAncestorRows.row_m M x row target start))
        (.forallE .num (.imp
          (SecondOrderProgramUniformAncestorRows.row_m
            (M.weakenBound sort_m.num) (x.weakenBound sort_m.num)
            (row.weakenBound sort_m.num) (target.weakenBound sort_m.num) (.bvar .here))
          (.disj
            (PrimitiveFormulas.lt_m (.bvar .here)
              (goodBound.weakenBound sort_m.num))
            (.conj
              (PrimitiveFormulas.lt_m (start.weakenBound sort_m.num) (.bvar .here))
              (PrimitiveFormulas.lt_m (.bvar .here)
                (finish.weakenBound sort_m.num))))))))

private def ancestor_locality_l (M : set_l ℳ) (x row goodBound start finish : num_l ℳ) :
    num_l ℳ → Prop := fun target =>
  SecondOrderOrder.lt_l start target →
    SecondOrderOrder.lt_l target finish →
    relation_l M (value_l (value_l (value_l x row) target) start) (zero_l ℳ) →
    ∀ found,
      ¬relation_l M (value_l (value_l (value_l x row) target) found) (zero_l ℳ) →
        SecondOrderOrder.lt_l found goodBound ∨
          (SecondOrderOrder.lt_l start found ∧ SecondOrderOrder.lt_l found finish)

private theorem ancestor_locality_formula_l {Γ Δ : SortContext signature_m}
    (η : Env ℳ Γ Δ) (M : Term signature_m Γ Δ .set)
    (x row goodBound start finish target : Term signature_m Γ Δ .num) :
    (ancestor_locality_m M x row goodBound start finish target).satisfies η ↔
      (SecondOrderOrder.lt_l (start.eval η) (target.eval η) →
        SecondOrderOrder.lt_l (target.eval η) (finish.eval η) →
        relation_l (M.eval η)
          (value_l (value_l (value_l (x.eval η) (row.eval η)) (target.eval η))
            (start.eval η)) (zero_l ℳ) →
        ∀ found,
          ¬relation_l (M.eval η)
            (value_l (value_l (value_l (x.eval η) (row.eval η)) (target.eval η)) found)
            (zero_l ℳ) →
          SecondOrderOrder.lt_l found (goodBound.eval η) ∨
            (SecondOrderOrder.lt_l (start.eval η) found ∧
              SecondOrderOrder.lt_l found (finish.eval η))) := by
  simp only [ancestor_locality_m, Formula.satisfies, SecondOrderOrder.formula_l,
    SecondOrderProgramUniformAncestorRows.row_formula_l,
    Term.eval_weakenBound]
  simp only [Term.eval, FirstOrder.Env.pushBound, FirstOrder.Assignment.push]
  simp only [Classical.not_not]

private def ancestor_locality_env (M : set_l ℳ) (x row goodBound start finish : num_l ℳ) :
    Env ℳ [] [.num, .num, .num, .num, .num, .set] :=
  (((((Env.empty (M := ℳ)).pushFree M).pushFree x).pushFree row).pushFree goodBound)
    |>.pushFree start |>.pushFree finish

private def ancestor_locality_rows_m : Formula signature_m []
    [.num, .num, .num, .num, .num, .num, .set] :=
  ancestor_locality_m
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there .here)))
    (.fvar (.there .here)) (.fvar .here)

private theorem ancestor_locality_syntax_l (M : set_l ℳ)
    (x row goodBound start finish target : num_l ℳ) :
    Formula.satisfies ((ancestor_locality_env M x row goodBound start finish).pushFree target)
      ancestor_locality_rows_m ↔ ancestor_locality_l M x row goodBound start finish target := by
  simpa only [ancestor_locality_rows_m, ancestor_locality_env, ancestor_locality_l, Term.eval,
    FirstOrder.Env.pushFree, FirstOrder.Assignment.push] using
    ancestor_locality_formula_l
      ((ancestor_locality_env M x row goodBound start finish).pushFree target)
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)

/-- 对固定行的祖先局部性同样使用实际纯公式作内部列强归纳。 -/
private theorem ancestor_locality_all_of_strong_step_l (hℳ : Theory.Models ℳ theory_m)
    (M : set_l ℳ) (x row goodBound start finish : num_l ℳ)
    (hstep : ∀ target,
      (∀ t, SecondOrderOrder.lt_l t target →
        ancestor_locality_l M x row goodBound start finish t) →
      ancestor_locality_l M x row goodBound start finish target) :
    ∀ target, ancestor_locality_l M x row goodBound start finish target :=
  SecondOrderListInduction.strong_induct_l hℳ ancestor_locality_rows_m
    (pure_language_m _ rfl) (ancestor_locality_env M x row goodBound start finish)
    (ancestor_locality_l M x row goodBound start finish)
    (fun target => ancestor_locality_syntax_l M x row goodBound start finish target) hstep

/-- 若某一行的直接父关系满足局部性，则该行任何目标的全部祖先也留在好前缀
或同一副本中。对目标列的递归使用实际纯公式强归纳。 -/
theorem ancestors_local_of_row_locality_l (hℳ : Theory.Models ℳ theory_m)
    {P M : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (x row goodBound start finish : num_l ℳ)
    (hrowLocal : row_locality_l P x goodBound start finish row) :
    ∀ target, ancestor_locality_l M x row goodBound start finish target := by
  letI := SecondOrderAlgebra.semiring_l hℳ
  letI := SecondOrderAlgebra.order_l hℳ
  letI := SecondOrderAlgebra.ordered_l hℳ
  apply ancestor_locality_all_of_strong_step_l hℳ M x row goodBound start finish
  intro target ih hStart hFinish hRootAbsent found hFound
  obtain ⟨parentOut, hParentOut, _⟩ :=
    function_of_semantics_l hℳ parent_m hP (value_l (value_l x row) target)
  rcases predecessor_l hℳ parentOut with hNone | ⟨parent, hParentOutEq⟩
  · subst parentOut
    exact False.elim (hFound (SecondOrderProgramAncestorNone.member_none_l
      hℳ parent_m hM hP hParentOut found))
  · have hParent : relation_l P (value_l (value_l x row) target) (succ_l parent) := by
      simpa only [hParentOutEq] using hParentOut
    have hParentLt :=
      SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hParent
    have hParentAncestor :=
      SecondOrderProgramUniformAncestorStructure.parent_l hℳ hP hM hParent
    have hParentBound := hrowLocal target hStart hFinish parent hParent
    rcases hParentBound with hParentGood | ⟨hParentNotBefore, hParentFinish⟩
    · rcases (SecondOrderProgramUniformAncestorStructure.member_some_l hℳ hP hM hParent).mp
        hFound with hFoundEq | hFoundParent
      · exact Or.inl (hFoundEq ▸ hParentGood)
      · have hFoundLt : SecondOrderOrder.lt_l found goodBound :=
          SecondOrderOrder.trans_l hℳ
          (SecondOrderProgramUniformParentOrder.member_lt_l hℳ hM hFoundParent)
          hParentGood
        exact Or.inl hFoundLt
    · have hParentNe : parent ≠ start := by
        intro hEq
        subst parent
        exact hParentAncestor hRootAbsent
      have hStartParent : SecondOrderOrder.lt_l start parent :=
        lt_of_le_of_ne (le_of_not_gt hParentNotBefore) (Ne.symm hParentNe)
      have hParentRootAbsent :
        relation_l M (value_l (value_l (value_l x row) parent) start) (zero_l ℳ) := by
        by_contra hParentRootAncestor
        exact (SecondOrderProgramUniformAncestorStructure.trans_l hℳ hM
          hParentAncestor hParentRootAncestor) hRootAbsent
      rcases (SecondOrderProgramUniformAncestorStructure.member_some_l hℳ hP hM hParent).mp
          hFound with hFoundEq | hFoundParent
      · exact Or.inr ⟨hFoundEq ▸ hStartParent,
          hFoundEq ▸ hParentFinish⟩
      · exact ih parent hParentLt hStartParent hParentFinish hParentRootAbsent found hFoundParent

/-- 若较低行的首列不是目标祖先，则较低行父局部性约束其全部祖先；
行间祖先包含遂把当前行的直接父也纳入同一前缀或副本。 -/
theorem parent_locality_of_lower_nonancestor_l (hℳ : Theory.Models ℳ theory_m)
    {P M : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (x goodBound start finish row lowerRow target found : num_l ℳ)
    (hLower : SecondOrderOrder.lt_l lowerRow row)
    (hLowerLocal : row_locality_l P x goodBound start finish lowerRow)
    (hStart : SecondOrderOrder.lt_l start target)
    (hFinish : SecondOrderOrder.lt_l target finish)
    (hFirstAbsent : relation_l M
      (value_l (value_l (value_l x lowerRow) target) start) (zero_l ℳ))
    (hParent : relation_l P (value_l (value_l x row) target) (succ_l found)) :
    SecondOrderOrder.lt_l found goodBound ∨
      (SecondOrderOrder.lt_l start found ∧ SecondOrderOrder.lt_l found finish) := by
  have hCurrentAncestor :=
    SecondOrderProgramUniformAncestorStructure.parent_l hℳ hP hM hParent
  have hLowerAncestor :=
    SecondOrderProgramUniformAncestorRows.row_le_l hℳ hM (Or.inr hLower) hCurrentAncestor
  exact (ancestors_local_of_row_locality_l hℳ hP hM x lowerRow goodBound start finish
    hLowerLocal target hStart hFinish hFirstAbsent found hLowerAncestor)

/-- 若首列并非在每个低行都是目标祖先，则可从一条反例低行和归纳假设
推出当前直接父列的局部性。 -/
theorem parent_locality_of_not_all_lower_roots_l (hℳ : Theory.Models ℳ theory_m)
    {P M : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (x goodBound start finish row target found : num_l ℳ)
    (hrowsLocal : ∀ s, SecondOrderOrder.lt_l s row →
      row_locality_l P x goodBound start finish s)
    (hnotAll : ¬ ∀ s, SecondOrderOrder.lt_l s row →
      ¬relation_l M (value_l (value_l (value_l x s) target) start) (zero_l ℳ))
    (hStart : SecondOrderOrder.lt_l start target)
    (hFinish : SecondOrderOrder.lt_l target finish)
    (hParent : relation_l P (value_l (value_l x row) target) (succ_l found)) :
    SecondOrderOrder.lt_l found goodBound ∨
      (SecondOrderOrder.lt_l start found ∧ SecondOrderOrder.lt_l found finish) := by
  classical
  push Not at hnotAll
  rcases hnotAll with ⟨lowerRow, hLower, hDoubleNeg⟩
  have hFirstAbsent : relation_l M
      (value_l (value_l (value_l x lowerRow) target) start) (zero_l ℳ) := hDoubleNeg
  exact parent_locality_of_lower_nonancestor_l hℳ hP hM x goodBound start finish row
    lowerRow target found hLower (hrowsLocal lowerRow hLower) hStart hFinish hFirstAbsent hParent

/-- 较早副本父边存在时，零号副本首列与局部目标之间不存在同一行祖先候选。 -/
theorem no_zero_copy_middle_ancestor_l (hℳ : Theory.Models ℳ theory_m)
    {X W P I B L E D J M : set_l ℳ}
    (hX : graph_semantics_l (graph_m expand_m) X)
    (hW : graph_semantics_l (graph_m maximal_m) W)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hI : graph_semantics_l (graph_m last_index_m) I)
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hD : graph_semantics_l (graph_m sub_m) D)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {x j p d k maximal b height y copy earlier localIndex row i found : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hmax : relation_l W x (succ_l maximal))
    (hlast : relation_l I x j)
    (hparentSource : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hb : relation_l B (value_l x (value_l k (value_l maximal p))) b)
    (hy : relation_l X (value_l x k) y)
    (hrow : SecondOrderOrder.lt_l row height)
    (hcopy : SecondOrderOrder.lt_l copy (succ_l k))
    (hi : SecondOrderOrder.lt_l i d)
    (hearlier : SecondOrderOrder.lt_l earlier copy)
    (hlocal : SecondOrderOrder.lt_l localIndex d)
    (hparentActual : relation_l P
      (value_l (value_l y row) (add_l p (add_l (mul_l d copy) i)))
      (succ_l (add_l p (add_l (mul_l d earlier) localIndex))))
    (hbetween : letI := order_l hℳ; p ≤ found)
    (hfoundTarget : SecondOrderOrder.lt_l found (add_l p i))
    (hancestor : ¬ relation_l M
      (value_l (value_l (value_l y row) (add_l p i)) found) (zero_l ℳ)) :
    False := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  obtain ⟨q, hq⟩ := (le_iff_l hℳ p found).mp hbetween
  have hqi : SecondOrderOrder.lt_l q i := by
    apply SecondOrderProgramParentRelocation.lt_of_add_lt_add_left_l hℳ
    calc
      add_l p q = found := hq
      _ < add_l p i := hfoundTarget
  have hqd : SecondOrderOrder.lt_l q d := SecondOrderOrder.trans_l hℳ hqi hi
  have hzeroAncestor : ¬ relation_l M
      (value_l (value_l (value_l y row) (add_l p i)) (add_l p q)) (zero_l ℳ) := by
    rw [← hq] at hancestor
    exact hancestor
  have hzeroCopyAncestor : ¬ relation_l M
      (value_l (value_l (value_l y row)
        (add_l p (add_l (mul_l d (zero_l ℳ)) i)))
        (add_l p (add_l (mul_l d (zero_l ℳ)) q))) (zero_l ℳ) := by
    simpa only [mul_zero_l hℳ d, zero_add_l hℳ, add_zero_l hℳ p] using hzeroAncestor
  have hcopyAncestor :=
    (SecondOrderProgramExpansionInsideCopies.member_congr_l hℳ
      hX hW hP hI hB hL hE hD hJ hM hx hmax hlast hparentSource hd hb hy
      (leftCopy := zero_l ℳ) (rightCopy := copy)
      (lt_of_le_of_lt (zero_le_l hℳ copy) hcopy) hcopy hrow hqd hi).mp
      hzeroCopyAncestor
  have hrootLe : add_l p (mul_l d copy) ≤
      add_l p (add_l (mul_l d copy) q) := by
    apply (add_le_add_iff_left p).mpr
    exact le_add_of_nonneg_right (zero_le_l hℳ q)
  rcases lt_or_eq_of_le hrootLe with hrootCandidate | hrootEq
  · exact hcopyAncestor <| SecondOrderProgramExpansionEarlierParentCut.earlier_copy_parent_cut_l
      hℳ hP hM hearlier hlocal hparentActual (Or.inr hrootCandidate)
  · exact hcopyAncestor <| SecondOrderProgramExpansionEarlierParentCut.earlier_copy_parent_cut_l
      hℳ hP hM hearlier hlocal hparentActual (Or.inl hrootEq)

/-- 较早副本父边禁止首列到目标之间的条目严格递增候选。 -/
theorem entry_not_lt_zero_copy_of_earlier_parent_l
    (hℳ : Theory.Models ℳ theory_m)
    {X W P I B L E D J M : set_l ℳ}
    (hX : graph_semantics_l (graph_m expand_m) X)
    (hW : graph_semantics_l (graph_m maximal_m) W)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hI : graph_semantics_l (graph_m last_index_m) I)
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hD : graph_semantics_l (graph_m sub_m) D)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {x j p d k maximal b height y copy earlier localIndex row i n a v : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hmax : relation_l W x (succ_l maximal))
    (hlast : relation_l I x j)
    (hparentSource : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hb : relation_l B (value_l x (value_l k (value_l maximal p))) b)
    (hy : relation_l X (value_l x k) y)
    (hrow : SecondOrderOrder.lt_l row height)
    (hcopy : SecondOrderOrder.lt_l copy (succ_l k))
    (hpositive : SecondOrderOrder.lt_l (zero_l ℳ) i)
    (hi : SecondOrderOrder.lt_l i d)
    (hearlier : SecondOrderOrder.lt_l earlier copy)
    (hlocal : SecondOrderOrder.lt_l localIndex d)
    (hn : relation_l L y n)
    (htargetBound : SecondOrderOrder.lt_l (add_l p i) n)
    (hparentActual : relation_l P
      (value_l (value_l y row) (add_l p (add_l (mul_l d copy) i)))
      (succ_l (add_l p (add_l (mul_l d earlier) localIndex))))
    (hentryFirst : relation_l J
      (value_l y (value_l p row)) (succ_l a))
    (hentryTarget : relation_l J
      (value_l y (value_l (add_l p i) row)) (succ_l v))
    (hbelowCopy : ∀ s, SecondOrderOrder.lt_l s row →
      ¬ relation_l M
        (value_l (value_l (value_l y s)
          (add_l p (add_l (mul_l d copy) i)))
          (add_l p (mul_l d copy))) (zero_l ℳ)) :
    ¬ SecondOrderOrder.lt_l a v := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  have hfirstTarget : SecondOrderOrder.lt_l p (add_l p i) :=
    lt_add_of_pos_right p hpositive
  have hzeroD : SecondOrderOrder.lt_l (zero_l ℳ) d :=
    SecondOrderOrder.trans_l hℳ hpositive hi
  have hlowCopyBound : SecondOrderOrder.lt_l (zero_l ℳ) (succ_l k) :=
    SecondOrderOrder.zero_succ_l hℳ k
  have hbelowZero : ∀ s, SecondOrderOrder.lt_l s row →
      ¬ relation_l M
        (value_l (value_l (value_l y s) (add_l p i)) p) (zero_l ℳ) := by
    intro s hs
    have hsHeight := SecondOrderOrder.trans_l hℳ hs hrow
    have hcopyEquiv := SecondOrderProgramExpansionInsideCopies.member_congr_l hℳ
      hX hW hP hI hB hL hE hD hJ hM hx hmax hlast hparentSource hd hb hy
      (leftCopy := zero_l ℳ) (rightCopy := copy) hlowCopyBound hcopy hsHeight
      (q := i) (i := zero_l ℳ) hzeroD hi
    have hzeroCopyAncestor : ¬ relation_l M
      (value_l (value_l (value_l y s)
          (add_l p (add_l (mul_l d (zero_l ℳ)) i)))
          (add_l p (add_l (mul_l d (zero_l ℳ)) (zero_l ℳ)))) (zero_l ℳ) := by
      have hbelowCopy' : ¬ relation_l M
          (value_l (value_l (value_l y s)
            (add_l p (add_l (mul_l d copy) i)))
            (add_l p (add_l (mul_l d copy) (zero_l ℳ)))) (zero_l ℳ) := by
        simpa only [add_zero_l hℳ (mul_l d copy)] using hbelowCopy s hs
      exact hcopyEquiv.mpr hbelowCopy'
    simpa only [mul_zero_l hℳ d, zero_add_l hℳ, add_zero_l hℳ p]
      using hzeroCopyAncestor
  apply SecondOrderProgramUniformParentCandidate.entry_not_lt_of_no_ancestor_l
    hℳ hP hM hJ hL hn htargetBound hfirstTarget hentryFirst hentryTarget hbelowZero
  intro found hfirstFound hfoundTarget
  by_contra hancestor
  have hbetween : p ≤ found := by
    rcases hfirstFound with heq | hlt
    · exact heq ▸ le_refl p
    · exact le_of_lt hlt
  exact no_zero_copy_middle_ancestor_l hℳ hX hW hP hI hB hL hE hD hJ hM
    hx hmax hlast hparentSource hd hb hy hrow hcopy hi hearlier hlocal
    hparentActual hbetween hfoundTarget hancestor

/-- 实际祖先的严格递增与零副本候选界相冲突，排除较早副本父边。 -/
theorem actual_ancestor_conflicts_with_zero_copy_bound_l
    (hℳ : Theory.Models ℳ theory_m)
    {X W P I S T Z B L E D J Asc M : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hX : graph_semantics_l (graph_m expand_m) X)
    (hW : graph_semantics_l (graph_m maximal_m) W)
    (hI : graph_semantics_l (graph_m last_index_m) I)
    (hS : graph_semantics_l (graph_m success_m) S)
    (hT : graph_semantics_l (graph_m SecondOrderProgramTrimArray.trim_m) T)
    (hZ : graph_semantics_l (graph_m SecondOrderProgramTrimHeight.trim_m) Z)
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hD : graph_semantics_l (graph_m sub_m) D)
    (hAsc : graph_semantics_l (graph_m ascending_m) Asc)
    {x j p d k maximal b height y copy earlier localIndex row i n v z : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hmax : relation_l W x (succ_l maximal))
    (hlast : relation_l I x j)
    (hparentSource : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hb : relation_l B (value_l x (value_l k (value_l maximal p))) b)
    (hy : relation_l X (value_l x k) y)
    (hv : relation_l S (value_l x (value_l k (value_l maximal p))) v)
    (hz : relation_l Z v z)
    (hrowTrim : SecondOrderOrder.lt_l row z)
    (hrow : SecondOrderOrder.lt_l row height)
    (hcopy : SecondOrderOrder.lt_l copy (succ_l k))
    (hpositive : SecondOrderOrder.lt_l (zero_l ℳ) i)
    (hi : SecondOrderOrder.lt_l i d)
    (hearlier : SecondOrderOrder.lt_l earlier copy)
    (hlocal : SecondOrderOrder.lt_l localIndex d)
    (hn : relation_l L y n)
    (htargetBound : SecondOrderOrder.lt_l (add_l p i) n)
    (hparentActual : relation_l P
      (value_l (value_l y row) (add_l p (add_l (mul_l d copy) i)))
      (succ_l (add_l p (add_l (mul_l d earlier) localIndex))))
    (hancestorCurrent : ¬ relation_l M
      (value_l (value_l (value_l y row) (add_l p (add_l (mul_l d copy) i))) p)
      (zero_l ℳ))
    (hbelowCopy : ∀ s, SecondOrderOrder.lt_l s row →
      ¬ relation_l M
        (value_l (value_l (value_l y s)
          (add_l p (add_l (mul_l d copy) i)))
          (add_l p (mul_l d copy))) (zero_l ℳ))
    (hzero : relation_l Asc
      (value_l (value_l x (value_l maximal p)) (value_l i row)) (zero_l ℳ)) :
    False := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  obtain ⟨v', z', hv', _, hz', hentries⟩ :=
    SecondOrderProgramExpansionInsideCopyEntryOrder.entry_value_congr_of_zero_l
      hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc hx hmax hlast hparentSource hd hb hy
      hcopy hi hzero
  have hv_eq : v' = v :=
    function_value_unique_l (function_of_semantics_l hℳ success_m hS) hv' hv
  have hz_eq : z' = z :=
    function_value_unique_l (function_of_semantics_l hℳ
      SecondOrderProgramTrimHeight.trim_m hZ) (hv_eq ▸ hz') hz
  have hrowz' : SecondOrderOrder.lt_l row z' := by
    simpa only [hz_eq] using hrowTrim
  obtain ⟨entryValue, hzeroEntry, hactualEntry⟩ := hentries hrowz'
  let hentriesSame : ∃ a, relation_l J
      (value_l y (value_l (add_l p i) row)) (succ_l a) ∧
        relation_l J
          (value_l y (value_l (add_l p (add_l (mul_l d copy) i)) row))
          (succ_l a) :=
    ⟨entryValue, hzeroEntry, hactualEntry⟩
  obtain ⟨a, b', hfirst, hcurrent, hab⟩ :=
    SecondOrderProgramUniformAncestorEntries.member_entries_lt_l hℳ hM hJ
      (x := y) (r := row)
      (t := add_l p (add_l (mul_l d copy) i)) (i := p) hancestorCurrent
  obtain ⟨v, hzero, hcurrentSame⟩ := hentriesSame
  have hbvSucc : succ_l b' = succ_l v := function_value_unique_l
    (function_of_semantics_l hℳ entry_m hJ) hcurrent hcurrentSame
  have hbv : b' = v := SecondOrderModel.injective_l hℳ hbvSucc
  have hav : SecondOrderOrder.lt_l a v := hbv ▸ hab
  have hnot := entry_not_lt_zero_copy_of_earlier_parent_l hℳ
    hX hW hP hI hB hL hE hD hJ hM hx hmax hlast hparentSource hd hb hy hrow hcopy
    hpositive hi hearlier hlocal hn htargetBound hparentActual hfirst hzero hbelowCopy
  exact hnot hav

/-- 若零号副本输出中首列 `p` 在每个较低行都是局部目标 `p+i` 的祖先，完整
展开的同副本祖先等价便给出：当前副本首列在每个较低输出行也是对应目标的祖先。 -/
theorem current_copy_root_ancestor_of_all_lower_source_roots_l
    (hℳ : Theory.Models ℳ theory_m)
    {X W P I B L E D J M : set_l ℳ}
    (hX : graph_semantics_l (graph_m expand_m) X)
    (hW : graph_semantics_l (graph_m maximal_m) W)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hI : graph_semantics_l (graph_m last_index_m) I)
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hD : graph_semantics_l (graph_m sub_m) D)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {x j p d k maximal b height y copy row i : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hmax : relation_l W x (succ_l maximal))
    (hlast : relation_l I x j)
    (hparentSource : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hb : relation_l B (value_l x (value_l k (value_l maximal p))) b)
    (hy : relation_l X (value_l x k) y)
    (hcopy : SecondOrderOrder.lt_l copy (succ_l k))
    (hrow : SecondOrderOrder.lt_l row height)
    (hpositive : SecondOrderOrder.lt_l (zero_l ℳ) i)
    (hi : SecondOrderOrder.lt_l i d)
    (hzeroCopy : ∀ s, SecondOrderOrder.lt_l s row →
      ¬relation_l M
        (value_l (value_l (value_l y s) (add_l p i)) p) (zero_l ℳ)) :
    ∀ s, SecondOrderOrder.lt_l s row →
      ¬relation_l M
        (value_l (value_l (value_l y s) (add_l p (add_l (mul_l d copy) i)))
          (add_l p (mul_l d copy))) (zero_l ℳ) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  intro s hs
  have hzeroD : SecondOrderOrder.lt_l (zero_l ℳ) d :=
    SecondOrderOrder.trans_l hℳ hpositive hi
  have hcopyEquiv := SecondOrderProgramExpansionInsideCopies.member_congr_l
    hℳ hX hW hP hI hB hL hE hD hJ hM hx hmax hlast hparentSource hd hb hy
    (leftCopy := zero_l ℳ) (rightCopy := copy)
    (SecondOrderOrder.zero_succ_l hℳ k) hcopy
    (SecondOrderOrder.trans_l hℳ hs hrow) hzeroD hi
  have hzeroCopy' : ¬relation_l M
      (value_l (value_l (value_l y s)
        (add_l p (add_l (mul_l d (zero_l ℳ)) i)))
        (add_l p (add_l (mul_l d (zero_l ℳ)) (zero_l ℳ)))) (zero_l ℳ) := by
    simpa only [mul_zero_l hℳ d, zero_add_l hℳ, add_zero_l hℳ p] using hzeroCopy s hs
  have hsource' : ¬relation_l M
      (value_l (value_l (value_l y s)
        (add_l p (add_l (mul_l d copy) i)))
        (add_l p (add_l (mul_l d copy) (zero_l ℳ)))) (zero_l ℳ) :=
    hcopyEquiv.mp hzeroCopy'
  simpa only [add_zero_l hℳ (mul_l d copy)] using hsource'

/-- “所有低行首列皆为祖先”分支的零上升情形。低行祖先性先由副本等价传递到
当前副本，再由较早父边把零号首列连至目标；与零上升引出的条目界矛盾。 -/
theorem earlier_parent_impossible_of_all_lower_roots_and_zero_l
    (hℳ : Theory.Models ℳ theory_m)
    {X W P I S T Z B L E D J Asc M O : set_l ℳ}
    (hX : graph_semantics_l (graph_m expand_m) X)
    (hW : graph_semantics_l (graph_m maximal_m) W)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hI : graph_semantics_l (graph_m last_index_m) I)
    (hS : graph_semantics_l (graph_m success_m) S)
    (hT : graph_semantics_l (graph_m SecondOrderProgramTrimArray.trim_m) T)
    (hZ : graph_semantics_l (graph_m SecondOrderProgramTrimHeight.trim_m) Z)
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hD : graph_semantics_l (graph_m sub_m) D)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hAsc : graph_semantics_l (graph_m ascending_m) Asc)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hO : graph_semantics_l (graph_m optional_m) O)
    {x j p d k maximal bad height y v z row copy earlier localIndex i n
      entry : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hmax : relation_l W x (succ_l maximal))
    (hlast : relation_l I x j)
    (hparentSource : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hbad : relation_l B (value_l x (value_l k (value_l maximal p))) bad)
    (hy : relation_l X (value_l x k) y)
    (hv : relation_l S (value_l x (value_l k (value_l maximal p))) v)
    (htrim : relation_l T v y)
    (hz : relation_l Z v z)
    (hrowMax : SecondOrderOrder.lt_l row maximal)
    (hrowTrim : SecondOrderOrder.lt_l row z)
    (hrowHeight : SecondOrderOrder.lt_l row height)
    (hcopyPos : SecondOrderOrder.lt_l (zero_l ℳ) copy)
    (hcopy : SecondOrderOrder.lt_l copy (succ_l k))
    (hcopyBound : copy = k ∨ SecondOrderOrder.lt_l copy k)
    (hn : relation_l L y n)
    (htargetBound : SecondOrderOrder.lt_l
      (add_l p (add_l (mul_l d copy) i)) n)
    (hzeroTargetBound : SecondOrderOrder.lt_l (add_l p i) n)
    (hfirstTarget : SecondOrderOrder.lt_l (add_l p (mul_l d copy))
      (add_l p (add_l (mul_l d copy) i)))
    (hentry : relation_l J
      (value_l y (value_l (add_l p (mul_l d copy)) row)) (succ_l entry))
    (hearlier : SecondOrderOrder.lt_l earlier copy)
    (hlocal : SecondOrderOrder.lt_l localIndex d)
    (hparentActual : relation_l P
      (value_l (value_l y row) (add_l p (add_l (mul_l d copy) i)))
      (succ_l (add_l p (add_l (mul_l d earlier) localIndex))))
    (hpositive : SecondOrderOrder.lt_l (zero_l ℳ) i)
    (hi : SecondOrderOrder.lt_l i d)
    (hzeroCopyRoots : ∀ s, SecondOrderOrder.lt_l s row →
      ¬relation_l M (value_l (value_l (value_l y s) (add_l p i)) p) (zero_l ℳ))
    (hzero : relation_l Asc
      (value_l (value_l x (value_l maximal p)) (value_l i row)) (zero_l ℳ)) :
    False := by
  letI := semiring_l hℳ
  have hbelowCopy := current_copy_root_ancestor_of_all_lower_source_roots_l hℳ
    hX hW hP hI hB hL hE hD hJ hM hx hmax hlast hparentSource hd hbad hy
    hcopy hrowHeight hpositive hi hzeroCopyRoots
  have hancestorCurrent :=
    SecondOrderProgramExpansionCopyBoundaryActualIteration.zero_first_to_target_of_earlier_parent_l
      hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc hM hO
      hx hmax hlast hparentSource hd hbad hy hv htrim hz hrowMax hrowTrim
      hcopyPos hcopyBound hn htargetBound hearlier hlocal hfirstTarget hentry
      hparentActual hbelowCopy
  exact actual_ancestor_conflicts_with_zero_copy_bound_l hℳ
    hP hM hJ hX hW hI hS hT hZ hB hL hE hD hAsc
    hx hmax hlast hparentSource hd hbad hy hv hz hrowTrim hrowHeight hcopy
    hpositive hi hearlier hlocal hn hzeroTargetBound hparentActual hancestorCurrent
    hbelowCopy hzero

/-- 非零上升时源父列为局部祖先，因此实际展开的直接父列必留在当前副本块。 -/
theorem actual_parent_in_copy_of_nonzero_ascending_l
    (hℳ : Theory.Models ℳ theory_m)
    {X W P I B L E D J O M Asc : set_l ℳ}
    (hX : graph_semantics_l (graph_m expand_m) X)
    (hW : graph_semantics_l (graph_m maximal_m) W)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hI : graph_semantics_l (graph_m last_index_m) I)
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hD : graph_semantics_l (graph_m sub_m) D)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hAsc : graph_semantics_l (graph_m ascending_m) Asc)
    {x j p d k maximal bad height y row copy i found : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hmax : relation_l W x (succ_l maximal))
    (hlast : relation_l I x j)
    (hparentSource : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hbad : relation_l B (value_l x (value_l k (value_l maximal p))) bad)
    (hy : relation_l X (value_l x k) y)
    (hcopy : SecondOrderOrder.lt_l copy (succ_l k))
    (hi : SecondOrderOrder.lt_l i d)
    (hiNe : i ≠ zero_l ℳ)
    (hasc : ¬relation_l Asc
      (value_l (value_l x (value_l maximal p)) (value_l i row)) (zero_l ℳ))
    (houtputParent : relation_l P
      (value_l (value_l y row) (add_l p (add_l (mul_l d copy) i)))
        (succ_l found)) :
    (add_l p (mul_l d copy) = found ∨
      SecondOrderOrder.lt_l (add_l p (mul_l d copy)) found) ∧
      SecondOrderOrder.lt_l found (add_l p (mul_l d (succ_l copy))) := by
  obtain ⟨hrowSource, hsourceAncestor⟩ :=
    SecondOrderProgramAscendingAncestor.source_ancestor_of_nonzero_l
      hℳ hAsc hM hiNe hasc
  exact SecondOrderProgramExpansionCopyRootParent.parent_in_copy_l
    hℳ hX hW hP hI hB hL hE hD hJ hO hM
    hx hmax hlast hparentSource hd hbad hy hrowSource hcopy hi hsourceAncestor houtputParent

/-- 若零号副本首列在所有低行都是局部目标的祖先，则上升标记的两种情况都排除
较早副本父边：零标记由边界祖先与条目比较导出矛盾，非零标记由副本内父界导出矛盾。 -/
theorem earlier_parent_impossible_of_all_lower_roots_l
    (hℳ : Theory.Models ℳ theory_m)
    {X W P I S T Z B L E D J Asc M O : set_l ℳ}
    (hX : graph_semantics_l (graph_m expand_m) X)
    (hW : graph_semantics_l (graph_m maximal_m) W)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hI : graph_semantics_l (graph_m last_index_m) I)
    (hS : graph_semantics_l (graph_m success_m) S)
    (hT : graph_semantics_l (graph_m SecondOrderProgramTrimArray.trim_m) T)
    (hZ : graph_semantics_l (graph_m SecondOrderProgramTrimHeight.trim_m) Z)
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hD : graph_semantics_l (graph_m sub_m) D)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hAsc : graph_semantics_l (graph_m ascending_m) Asc)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hO : graph_semantics_l (graph_m optional_m) O)
    {x j p d k maximal bad height y v z row copy earlier localIndex i n
      entry : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hmax : relation_l W x (succ_l maximal))
    (hlast : relation_l I x j)
    (hparentSource : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hbad : relation_l B (value_l x (value_l k (value_l maximal p))) bad)
    (hy : relation_l X (value_l x k) y)
    (hv : relation_l S (value_l x (value_l k (value_l maximal p))) v)
    (htrim : relation_l T v y)
    (hz : relation_l Z v z)
    (hrowMax : SecondOrderOrder.lt_l row maximal)
    (hrowTrim : SecondOrderOrder.lt_l row z)
    (hrowHeight : SecondOrderOrder.lt_l row height)
    (hcopyPos : SecondOrderOrder.lt_l (zero_l ℳ) copy)
    (hcopy : SecondOrderOrder.lt_l copy (succ_l k))
    (hcopyBound : copy = k ∨ SecondOrderOrder.lt_l copy k)
    (hn : relation_l L y n)
    (htargetBound : SecondOrderOrder.lt_l
      (add_l p (add_l (mul_l d copy) i)) n)
    (hzeroTargetBound : SecondOrderOrder.lt_l (add_l p i) n)
    (hfirstTarget : SecondOrderOrder.lt_l (add_l p (mul_l d copy))
      (add_l p (add_l (mul_l d copy) i)))
    (hentry : relation_l J
      (value_l y (value_l (add_l p (mul_l d copy)) row)) (succ_l entry))
    (hearlier : SecondOrderOrder.lt_l earlier copy)
    (hlocal : SecondOrderOrder.lt_l localIndex d)
    (hparentActual : relation_l P
      (value_l (value_l y row) (add_l p (add_l (mul_l d copy) i)))
      (succ_l (add_l p (add_l (mul_l d earlier) localIndex))))
    (hpositive : SecondOrderOrder.lt_l (zero_l ℳ) i)
    (hi : SecondOrderOrder.lt_l i d)
    (hzeroCopyRoots : ∀ s, SecondOrderOrder.lt_l s row →
      ¬relation_l M (value_l (value_l (value_l y s) (add_l p i)) p) (zero_l ℳ)) :
    False := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  by_cases hzero : relation_l Asc
      (value_l (value_l x (value_l maximal p)) (value_l i row)) (zero_l ℳ)
  · exact earlier_parent_impossible_of_all_lower_roots_and_zero_l hℳ
      hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc hM hO
      hx hmax hlast hparentSource hd hbad hy hv htrim hz hrowMax hrowTrim hrowHeight
      hcopyPos hcopy hcopyBound hn htargetBound hzeroTargetBound hfirstTarget hentry
      hearlier hlocal hparentActual hpositive hi hzeroCopyRoots hzero
  · have hwithin := actual_parent_in_copy_of_nonzero_ascending_l hℳ
      hX hW hP hI hB hL hE hD hJ hO hM hAsc
      hx hmax hlast hparentSource hd hbad hy hcopy hi (ne_of_gt hpositive) hzero hparentActual
    rcases hwithin.1 with heq | hlt
    · have hbefore := SecondOrderProgramExpansionEarlierParentCut.earlier_copy_column_lt_l
        hℳ (p := p) hearlier hlocal
      rw [heq] at hbefore
      exact (SecondOrderOrder.irrefl_l hℳ _) hbefore
    · have hbefore := SecondOrderProgramExpansionEarlierParentCut.earlier_copy_column_lt_l
        hℳ (p := p) hearlier hlocal
      exact (SecondOrderOrder.irrefl_l hℳ _)
        (SecondOrderOrder.trans_l hℳ hbefore hlt)

/-- 全低行祖先分支中，目标实际父列只能在前缀 `p` 之前或当前副本块内。
若父列落在当前首列之前，内部带余除法把它写成较早块号与局部余数，再由上升标记
分叉排除该父边；无需在宿主自然数上枚举副本。 -/
theorem parent_locality_of_all_lower_roots_l
    (hℳ : Theory.Models ℳ theory_m)
    {X W P I S T Z B L E D J Asc M O : set_l ℳ}
    (hX : graph_semantics_l (graph_m expand_m) X)
    (hW : graph_semantics_l (graph_m maximal_m) W)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hI : graph_semantics_l (graph_m last_index_m) I)
    (hS : graph_semantics_l (graph_m success_m) S)
    (hT : graph_semantics_l (graph_m SecondOrderProgramTrimArray.trim_m) T)
    (hZ : graph_semantics_l (graph_m SecondOrderProgramTrimHeight.trim_m) Z)
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hD : graph_semantics_l (graph_m sub_m) D)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hAsc : graph_semantics_l (graph_m ascending_m) Asc)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hO : graph_semantics_l (graph_m optional_m) O)
    {x j p d k maximal bad height y v z row copy i n found entry : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hmax : relation_l W x (succ_l maximal))
    (hlast : relation_l I x j)
    (hparentSource : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hbad : relation_l B (value_l x (value_l k (value_l maximal p))) bad)
    (hy : relation_l X (value_l x k) y)
    (hv : relation_l S (value_l x (value_l k (value_l maximal p))) v)
    (htrim : relation_l T v y)
    (hz : relation_l Z v z)
    (hrowMax : SecondOrderOrder.lt_l row maximal)
    (hrowTrim : SecondOrderOrder.lt_l row z)
    (hrowHeight : SecondOrderOrder.lt_l row height)
    (hcopyPos : SecondOrderOrder.lt_l (zero_l ℳ) copy)
    (hcopy : SecondOrderOrder.lt_l copy (succ_l k))
    (hcopyBound : copy = k ∨ SecondOrderOrder.lt_l copy k)
    (hn : relation_l L y n)
    (htargetBound : SecondOrderOrder.lt_l
      (add_l p (add_l (mul_l d copy) i)) n)
    (hzeroTargetBound : SecondOrderOrder.lt_l (add_l p i) n)
    (hfirstTarget : SecondOrderOrder.lt_l (add_l p (mul_l d copy))
      (add_l p (add_l (mul_l d copy) i)))
    (htargetFinish : SecondOrderOrder.lt_l
      (add_l p (add_l (mul_l d copy) i)) (add_l p (mul_l d (succ_l copy))))
    (hentry : relation_l J
      (value_l y (value_l (add_l p (mul_l d copy)) row)) (succ_l entry))
    (hpositive : SecondOrderOrder.lt_l (zero_l ℳ) i)
    (hi : SecondOrderOrder.lt_l i d)
    (hzeroCopyRoots : ∀ s, SecondOrderOrder.lt_l s row →
      ¬relation_l M (value_l (value_l (value_l y s) (add_l p i)) p) (zero_l ℳ))
    (hParent : relation_l P
      (value_l (value_l y row) (add_l p (add_l (mul_l d copy) i))) (succ_l found)) :
    SecondOrderOrder.lt_l found p ∨
      (¬SecondOrderOrder.lt_l found (add_l p (mul_l d copy)) ∧
        SecondOrderOrder.lt_l found (add_l p (mul_l d (succ_l copy)))) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  by_cases hgood : SecondOrderOrder.lt_l found p
  · exact Or.inl hgood
  · have hpFound : p ≤ found := le_of_not_gt hgood
    have hparentLt := SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hParent
    by_cases hbefore : SecondOrderOrder.lt_l found (add_l p (mul_l d copy))
    · have hwidth : SecondOrderOrder.lt_l (zero_l ℳ) d :=
        SecondOrderOrder.trans_l hℳ hpositive hi
      have hpc : p = found ∨ SecondOrderOrder.lt_l p found := by
        rcases eq_or_lt_of_le hpFound with heq | hlt
        · exact Or.inl heq
        · exact Or.inr hlt
      obtain ⟨earlier, localIndex, hearlier, hlocal, hcoordinates⟩ :=
        SecondOrderProgramBlockCoordinates.offset_l hℳ hwidth hpc hbefore
      have hParentEarlier : relation_l P
          (value_l (value_l y row) (add_l p (add_l (mul_l d copy) i)))
          (succ_l (add_l p (add_l (mul_l d earlier) localIndex))) := by
        rw [hcoordinates]
        exact hParent
      exact False.elim (earlier_parent_impossible_of_all_lower_roots_l hℳ
        hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc hM hO
        hx hmax hlast hparentSource hd hbad hy hv htrim hz hrowMax hrowTrim hrowHeight
        hcopyPos hcopy hcopyBound hn htargetBound hzeroTargetBound hfirstTarget hentry
        hearlier hlocal hParentEarlier hpositive hi hzeroCopyRoots)
    · exact Or.inr ⟨hbefore,
        SecondOrderOrder.trans_l hℳ hparentLt htargetFinish⟩

/-- 行强归纳步的副本内部目标版本。按零号首列是否在全部低行到达局部目标分支：
若到达，调用上述带余坐标与上升标记排除；若未到达，借副本祖先等价转成实际输出的
低行反例，再用归纳假设约束其全部祖先。 -/
theorem parent_locality_at_expansion_copy_target_l
    (hℳ : Theory.Models ℳ theory_m)
    {X W P I S T Z B L E D J Asc M O : set_l ℳ}
    (hX : graph_semantics_l (graph_m expand_m) X)
    (hW : graph_semantics_l (graph_m maximal_m) W)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hI : graph_semantics_l (graph_m last_index_m) I)
    (hS : graph_semantics_l (graph_m success_m) S)
    (hT : graph_semantics_l (graph_m SecondOrderProgramTrimArray.trim_m) T)
    (hZ : graph_semantics_l (graph_m SecondOrderProgramTrimHeight.trim_m) Z)
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hD : graph_semantics_l (graph_m sub_m) D)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hAsc : graph_semantics_l (graph_m ascending_m) Asc)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hO : graph_semantics_l (graph_m optional_m) O)
    {x j p d k maximal bad height y v z row copy i n found entry : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hmax : relation_l W x (succ_l maximal))
    (hlast : relation_l I x j)
    (hparentSource : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hbad : relation_l B (value_l x (value_l k (value_l maximal p))) bad)
    (hy : relation_l X (value_l x k) y)
    (hv : relation_l S (value_l x (value_l k (value_l maximal p))) v)
    (htrim : relation_l T v y)
    (hz : relation_l Z v z)
    (hrowMax : SecondOrderOrder.lt_l row maximal)
    (hrowTrim : SecondOrderOrder.lt_l row z)
    (hrowHeight : SecondOrderOrder.lt_l row height)
    (hcopyPos : SecondOrderOrder.lt_l (zero_l ℳ) copy)
    (hcopy : SecondOrderOrder.lt_l copy (succ_l k))
    (hcopyBound : copy = k ∨ SecondOrderOrder.lt_l copy k)
    (hn : relation_l L y n)
    (htargetBound : SecondOrderOrder.lt_l
      (add_l p (add_l (mul_l d copy) i)) n)
    (hzeroTargetBound : SecondOrderOrder.lt_l (add_l p i) n)
    (hfirstTarget : SecondOrderOrder.lt_l (add_l p (mul_l d copy))
      (add_l p (add_l (mul_l d copy) i)))
    (htargetFinish : SecondOrderOrder.lt_l
      (add_l p (add_l (mul_l d copy) i)) (add_l p (mul_l d (succ_l copy))))
    (hentry : relation_l J
      (value_l y (value_l (add_l p (mul_l d copy)) row)) (succ_l entry))
    (hpositive : SecondOrderOrder.lt_l (zero_l ℳ) i)
    (hi : SecondOrderOrder.lt_l i d)
    (hrowsLocal : ∀ s, SecondOrderOrder.lt_l s row →
      row_locality_l P y p (add_l p (mul_l d copy))
        (add_l p (mul_l d (succ_l copy))) s)
    (hParent : relation_l P
      (value_l (value_l y row) (add_l p (add_l (mul_l d copy) i))) (succ_l found)) :
    SecondOrderOrder.lt_l found p ∨
      (¬SecondOrderOrder.lt_l found (add_l p (mul_l d copy)) ∧
        SecondOrderOrder.lt_l found (add_l p (mul_l d (succ_l copy)))) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  by_cases hzeroCopyRoots : ∀ s, SecondOrderOrder.lt_l s row →
      ¬relation_l M (value_l (value_l (value_l y s) (add_l p i)) p) (zero_l ℳ)
  · exact parent_locality_of_all_lower_roots_l hℳ
      hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc hM hO
      hx hmax hlast hparentSource hd hbad hy hv htrim hz hrowMax hrowTrim hrowHeight
      hcopyPos hcopy hcopyBound hn htargetBound hzeroTargetBound hfirstTarget
      htargetFinish hentry hpositive hi hzeroCopyRoots hParent
  · have hnotAllCurrent : ¬∀ s, SecondOrderOrder.lt_l s row →
        ¬relation_l M
          (value_l (value_l (value_l y s) (add_l p (add_l (mul_l d copy) i)))
            (add_l p (mul_l d copy))) (zero_l ℳ) := by
      intro hallCurrent
      apply hzeroCopyRoots
      intro s hs
      have hcopyEquiv := SecondOrderProgramExpansionInsideCopies.member_congr_l
        hℳ hX hW hP hI hB hL hE hD hJ hM hx hmax hlast hparentSource hd hbad hy
        (leftCopy := zero_l ℳ) (rightCopy := copy)
        (SecondOrderOrder.zero_succ_l hℳ k) hcopy
        (SecondOrderOrder.trans_l hℳ hs hrowHeight)
        (SecondOrderOrder.trans_l hℳ hpositive hi) hi
      have hcurrent' : ¬relation_l M
          (value_l (value_l (value_l y s)
            (add_l p (add_l (mul_l d copy) i)))
            (add_l p (add_l (mul_l d copy) (zero_l ℳ)))) (zero_l ℳ) := by
        simpa only [add_zero_l hℳ (mul_l d copy)] using hallCurrent s hs
      have hzero' := hcopyEquiv.mpr hcurrent'
      simpa only [mul_zero_l hℳ d, zero_add_l hℳ, add_zero_l hℳ p] using hzero'
    have hnotAllResult := parent_locality_of_not_all_lower_roots_l hℳ hP hM y p
      (add_l p (mul_l d copy)) (add_l p (mul_l d (succ_l copy))) row
      (add_l p (add_l (mul_l d copy) i)) found hrowsLocal hnotAllCurrent
      hfirstTarget htargetFinish hParent
    rcases hnotAllResult with hgood | ⟨hstart, hfinish⟩
    · exact Or.inl hgood
    · exact Or.inr ⟨fun hbefore =>
        (SecondOrderOrder.irrefl_l hℳ _)
          (SecondOrderOrder.trans_l hℳ hbefore hstart), hfinish⟩

/-- 实际目标位于半开区间 `[start,start+width)` 且严格大于 `start` 时，原截断减法
图给出唯一差值；差值为正且严格小于区间宽度。 -/
theorem positive_offset_below_width_l (hℳ : Theory.Models ℳ theory_m)
    {D : set_l ℳ} (hD : graph_semantics_l (graph_m sub_m) D)
    {target start width : num_l ℳ}
    (hstart : SecondOrderOrder.lt_l start target)
    (hend : SecondOrderOrder.lt_l target (add_l start width)) :
    ∃ i, SecondOrderOrder.lt_l (zero_l ℳ) i ∧ SecondOrderOrder.lt_l i width ∧
      target = add_l start i := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  obtain ⟨i, hsub, _⟩ := function_of_semantics_l hℳ sub_m hD (value_l target start)
  rcases (SecondOrderProgramSubtraction.sub_rel_l hℳ hD target start i).mp hsub with
    hdiff | ⟨rfl, hle⟩
  · have htarget : target = add_l start i :=
      hdiff.symm.trans (SecondOrderNumbers.add_comm_l hℳ i start)
    have hstartOffset : SecondOrderOrder.lt_l start (add_l start i) := by
      simpa only [htarget] using hstart
    obtain ⟨k, hk⟩ := hstartOffset
    have hki : succ_l k = i :=
      (SecondOrderNumbers.add_cancel_l hℳ start _ _).mp hk
    have hiPos : SecondOrderOrder.lt_l (zero_l ℳ) i := by
      rw [← hki]
      exact SecondOrderOrder.zero_succ_l hℳ k
    have hendOffset : SecondOrderOrder.lt_l (add_l start i) (add_l start width) := by
      simpa only [htarget] using hend
    obtain ⟨k', hk'⟩ := hendOffset
    have hcancel : add_l start (add_l i (succ_l k')) = add_l start width := by
      calc
        add_l start (add_l i (succ_l k')) =
            add_l (add_l start i) (succ_l k') :=
          (SecondOrderNumbers.add_assoc_l hℳ start i (succ_l k')).symm
        _ = add_l start width := hk'
    have hiWidth : add_l i (succ_l k') = width :=
      (SecondOrderNumbers.add_cancel_l hℳ start _ _).mp hcancel
    exact ⟨i, hiPos, ⟨k', hiWidth⟩, htarget⟩
  · have hnot : ¬SecondOrderOrder.lt_l start target := by
      exact fun h => (not_lt_of_ge hle) h
    exact False.elim (hnot hstart)

/-- 真实正父边本身给出目标列合法性，并通过其正条目排除裁剪掉该行。 -/
theorem positive_parent_row_below_trim_l
    (hℳ : Theory.Models ℳ theory_m)
    {P M L J O E Z : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hZ : graph_semantics_l (graph_m SecondOrderProgramTrimHeight.trim_m) Z)
    {y n z row target found : num_l ℳ}
    (hn : relation_l L y n)
    (hz : relation_l Z y z)
    (hParent : relation_l P (value_l (value_l y row) target) (succ_l found)) :
    SecondOrderOrder.lt_l target n ∧ SecondOrderOrder.lt_l row z := by
  letI := order_l hℳ
  rcases predecessor_l hℳ row with rfl | ⟨r, rfl⟩
  · obtain ⟨Q, _, hQ⟩ := graph_total_l hℳ SecondOrderProgramParentZero.parent_zero_m
    have htarget : SecondOrderOrder.lt_l target n := by
      by_contra hnot
      exact (nonzero_l hℳ found).symm
        ((SecondOrderProgramUniformParentState.parent_past_end_l
          hℳ hP hL hn (zero_l ℳ) target (succ_l found)
          (le_of_not_gt hnot)).mp hParent)
    have hq := (SecondOrderProgramUniformParentLookup.parent_zero_l
      hℳ hP hQ hL y n target (succ_l found) hn htarget).mp hParent
    have hspec := (SecondOrderProgramParentZero.parent_zero_some_l
      hℳ hQ hL hJ hn target found).mp hq
    obtain ⟨a, b, _, htargetEntry, hab⟩ := hspec.2.2.1
    have hbpos : SecondOrderOrder.lt_l (zero_l ℳ) b := by
      rcases predecessor_l hℳ b with rfl | ⟨c, rfl⟩
      · exact False.elim ((SecondOrderOrder.irrefl_l hℳ (zero_l ℳ))
          (lt_of_le_of_lt (zero_le_l hℳ a) hab))
      · exact SecondOrderOrder.zero_succ_l hℳ c
    exact ⟨hspec.1,
      SecondOrderProgramTrimPositiveEntry.row_lt_l hℳ hZ hJ hO hL hE
        hn hz hspec.1 htargetEntry hbpos⟩
  · have hspec := (SecondOrderProgramUniformParentSpecification.parent_succ_some_l
      hℳ hP hL hM hJ hn r target found).mp hParent
    obtain ⟨a, b, _, htargetEntry, hab⟩ := hspec.2.2.1.2
    have hbpos : SecondOrderOrder.lt_l (zero_l ℳ) b := by
      rcases predecessor_l hℳ b with rfl | ⟨c, rfl⟩
      · exact False.elim ((SecondOrderOrder.irrefl_l hℳ (zero_l ℳ))
          (lt_of_le_of_lt (zero_le_l hℳ a) hab))
      · exact SecondOrderOrder.zero_succ_l hℳ c
    exact ⟨hspec.1,
      SecondOrderProgramTrimPositiveEntry.row_lt_l hℳ hZ hJ hO hL hE
        hn hz hspec.1 htargetEntry hbpos⟩

/-- 成功展开中的任意副本首列，在最大父行以下且保留的行上仍有 some 条目。
先由未裁剪成功正文的首列公式取值，再经真实截断等价搬到展开输出。 -/
theorem expansion_copy_root_entry_l
    (hℳ : Theory.Models ℳ theory_m)
    {P I S B L E D J T Z : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hI : graph_semantics_l (graph_m last_index_m) I)
    (hS : graph_semantics_l (graph_m success_m) S)
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hD : graph_semantics_l (graph_m sub_m) D)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hT : graph_semantics_l (graph_m SecondOrderProgramTrimArray.trim_m) T)
    (hZ : graph_semantics_l (graph_m SecondOrderProgramTrimHeight.trim_m) Z)
    {x j p d k maximal bad height v y z copy row : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hlast : relation_l I x j)
    (hparentSource : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hbad : relation_l B (value_l x (value_l k (value_l maximal p))) bad)
    (hv : relation_l S (value_l x (value_l k (value_l maximal p))) v)
    (htrim : relation_l T v y)
    (hz : relation_l Z v z)
    (hcopy : SecondOrderOrder.lt_l copy (succ_l k))
    (hrowMax : SecondOrderOrder.lt_l row maximal)
    (hrowTrim : SecondOrderOrder.lt_l row z) :
    ∃ entry, relation_l J
      (value_l y (value_l (add_l p (mul_l d copy)) row)) (succ_l entry) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  have hpj := SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hparentSource
  have hdpos := SecondOrderProgramExpansionParameterEntries.width_pos_l
    hℳ hD hpj hd
  obtain ⟨a, c, gap, ha, hc, hgap, hgapPos, hsum, hraw⟩ :=
    SecondOrderProgramExpansionRawFirstEntry.entry_l
      hℳ hP hI hS hB hL hE hD hJ hx hlast hparentSource hd hbad hv
      hcopy hrowMax
  have hbr := SecondOrderProgramExpansionSuccessRectangular.bad_rectangular_l
    hℳ hB hL hE hD hx (Or.inr hpj) hd hbad
  have hvr0 := SecondOrderProgramExpansionSuccessRectangular.success_rectangular_l
    hℳ hS hB hL hE hx hbad hbr hv
  have hpn : p ≤ succ_l j :=
    Or.inr (SecondOrderOrder.trans_l hℳ hpj (lt_own_succ_l hℳ j))
  have hvr : rectangular_l L E v (add_l p (mul_l d (succ_l k))) height := by
    simpa only [min_eq_right hpn] using hvr0
  have hcol : SecondOrderOrder.lt_l (add_l p (mul_l d copy))
      (add_l p (mul_l d (succ_l k))) :=
    (add_lt_add_iff_left p).mpr (mul_lt_mul_of_pos_left hcopy hdpos)
  have hkeep := SecondOrderProgramTrimEntryBelow.entry_l
    hℳ hT hZ hJ hL hE hvr hz htrim hcol hrowTrim (succ_l (add_l a (mul_l copy gap)))
  exact ⟨add_l a (mul_l copy gap), hkeep.mp hraw⟩

/-- 将副本内部目标的局部性从显式平坦坐标推广到整个开块区间。差值由真实减法图
取得，而不是通过宿主 `Nat` 计算或标准数归纳。 -/
theorem parent_locality_at_expansion_copy_interval_l
    (hℳ : Theory.Models ℳ theory_m)
    {X W P I S T Z B L E D J Asc M O : set_l ℳ}
    (hX : graph_semantics_l (graph_m expand_m) X)
    (hW : graph_semantics_l (graph_m maximal_m) W)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hI : graph_semantics_l (graph_m last_index_m) I)
    (hS : graph_semantics_l (graph_m success_m) S)
    (hT : graph_semantics_l (graph_m SecondOrderProgramTrimArray.trim_m) T)
    (hZ : graph_semantics_l (graph_m SecondOrderProgramTrimHeight.trim_m) Z)
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hD : graph_semantics_l (graph_m sub_m) D)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hAsc : graph_semantics_l (graph_m ascending_m) Asc)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hO : graph_semantics_l (graph_m optional_m) O)
    {x j p d k maximal bad height y v z row copy n target found entry : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hmax : relation_l W x (succ_l maximal))
    (hlast : relation_l I x j)
    (hparentSource : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hbad : relation_l B (value_l x (value_l k (value_l maximal p))) bad)
    (hy : relation_l X (value_l x k) y)
    (hv : relation_l S (value_l x (value_l k (value_l maximal p))) v)
    (htrim : relation_l T v y)
    (hz : relation_l Z v z)
    (hrowMax : SecondOrderOrder.lt_l row maximal)
    (hrowTrim : SecondOrderOrder.lt_l row z)
    (hrowHeight : SecondOrderOrder.lt_l row height)
    (hcopyPos : SecondOrderOrder.lt_l (zero_l ℳ) copy)
    (hcopy : SecondOrderOrder.lt_l copy (succ_l k))
    (hcopyBound : copy = k ∨ SecondOrderOrder.lt_l copy k)
    (hn : relation_l L y n)
    (htargetBound : SecondOrderOrder.lt_l target n)
    (hentry : relation_l J
      (value_l y (value_l (add_l p (mul_l d copy)) row)) (succ_l entry))
    (hrowsLocal : ∀ s, SecondOrderOrder.lt_l s row →
      row_locality_l P y p (add_l p (mul_l d copy))
        (add_l p (mul_l d (succ_l copy))) s)
    (hstart : SecondOrderOrder.lt_l (add_l p (mul_l d copy)) target)
    (hfinish : SecondOrderOrder.lt_l target (add_l p (mul_l d (succ_l copy))))
    (hParent : relation_l P (value_l (value_l y row) target) (succ_l found)) :
    SecondOrderOrder.lt_l found p ∨
      (¬SecondOrderOrder.lt_l found (add_l p (mul_l d copy)) ∧
        SecondOrderOrder.lt_l found (add_l p (mul_l d (succ_l copy)))) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  have hfinishEq : add_l p (mul_l d (succ_l copy)) =
      add_l (add_l p (mul_l d copy)) d := by
    rw [mul_succ_l hℳ]
    exact (SecondOrderNumbers.add_assoc_l hℳ p (mul_l d copy) d).symm
  have hfinishOffset : SecondOrderOrder.lt_l target
      (add_l (add_l p (mul_l d copy)) d) := by
    rw [← hfinishEq]
    exact hfinish
  obtain ⟨i, hpositive, hi, htargetOffset⟩ :=
    positive_offset_below_width_l hℳ hD hstart hfinishOffset
  have htargetCoord : target = add_l p (add_l (mul_l d copy) i) := by
    calc
      target = add_l (add_l p (mul_l d copy)) i := htargetOffset
      _ = add_l p (add_l (mul_l d copy) i) :=
        SecondOrderNumbers.add_assoc_l hℳ p (mul_l d copy) i
  have hinnerLe : i ≤ add_l (mul_l d copy) i := by
    calc
      i = add_l (zero_l ℳ) i := (zero_add_l hℳ i).symm
      _ ≤ add_l (mul_l d copy) i :=
        add_le_add_left (zero_le_l hℳ (mul_l d copy)) i
  have htargetCoordBound : SecondOrderOrder.lt_l
      (add_l p (add_l (mul_l d copy) i)) n := by
    rw [← htargetCoord]
    exact htargetBound
  have hzeroTargetBound : SecondOrderOrder.lt_l (add_l p i) n := by
    exact lt_of_le_of_lt ((add_le_add_iff_left p).mpr hinnerLe) htargetCoordBound
  have hfirstTarget : SecondOrderOrder.lt_l (add_l p (mul_l d copy))
      (add_l p (add_l (mul_l d copy) i)) := by
    rw [← htargetCoord]
    exact hstart
  have htargetFinish : SecondOrderOrder.lt_l
      (add_l p (add_l (mul_l d copy) i)) (add_l p (mul_l d (succ_l copy))) := by
    rw [← htargetCoord]
    exact hfinish
  have hParent' : relation_l P
      (value_l (value_l y row) (add_l p (add_l (mul_l d copy) i))) (succ_l found) := by
    rw [← htargetCoord]
    exact hParent
  exact parent_locality_at_expansion_copy_target_l hℳ
    hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc hM hO
    hx hmax hlast hparentSource hd hbad hy hv htrim hz hrowMax hrowTrim hrowHeight
    hcopyPos hcopy hcopyBound hn htargetCoordBound hzeroTargetBound hfirstTarget htargetFinish
    hentry hpositive hi hrowsLocal hParent'

/-- 区间局部性归纳步的闭合接口：正父边自动给出合法目标和保留行，成功正文给出
副本首列的 some 条目；因此调用者只需提供逐行归纳假设与实际目标所处的副本区间。 -/
theorem parent_locality_step_at_expansion_copy_interval_l
    (hℳ : Theory.Models ℳ theory_m)
    {X W P I S T Z B L E D J Asc M O : set_l ℳ}
    (hX : graph_semantics_l (graph_m expand_m) X)
    (hW : graph_semantics_l (graph_m maximal_m) W)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hI : graph_semantics_l (graph_m last_index_m) I)
    (hS : graph_semantics_l (graph_m success_m) S)
    (hT : graph_semantics_l (graph_m SecondOrderProgramTrimArray.trim_m) T)
    (hZ : graph_semantics_l (graph_m SecondOrderProgramTrimHeight.trim_m) Z)
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hD : graph_semantics_l (graph_m sub_m) D)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hAsc : graph_semantics_l (graph_m ascending_m) Asc)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hO : graph_semantics_l (graph_m optional_m) O)
    {x j p d k maximal bad height y v z row copy n target found : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hmax : relation_l W x (succ_l maximal))
    (hlast : relation_l I x j)
    (hparentSource : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hbad : relation_l B (value_l x (value_l k (value_l maximal p))) bad)
    (hy : relation_l X (value_l x k) y)
    (hv : relation_l S (value_l x (value_l k (value_l maximal p))) v)
    (htrim : relation_l T v y)
    (hz : relation_l Z v z)
    (hrowMax : SecondOrderOrder.lt_l row maximal)
    (hcopyPos : SecondOrderOrder.lt_l (zero_l ℳ) copy)
    (hcopy : SecondOrderOrder.lt_l copy (succ_l k))
    (hn : relation_l L y n)
    (hrowsLocal : ∀ s, SecondOrderOrder.lt_l s row →
      row_locality_l P y p (add_l p (mul_l d copy))
        (add_l p (mul_l d (succ_l copy))) s)
    (hstart : SecondOrderOrder.lt_l (add_l p (mul_l d copy)) target)
    (hfinish : SecondOrderOrder.lt_l target (add_l p (mul_l d (succ_l copy))))
    (hParent : relation_l P (value_l (value_l y row) target) (succ_l found)) :
    SecondOrderOrder.lt_l found p ∨
      (¬SecondOrderOrder.lt_l found (add_l p (mul_l d copy)) ∧
        SecondOrderOrder.lt_l found (add_l p (mul_l d (succ_l copy)))) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  have hpj := SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hparentSource
  have hbr := SecondOrderProgramExpansionSuccessRectangular.bad_rectangular_l
    hℳ hB hL hE hD hx (Or.inr hpj) hd hbad
  have hvr0 := SecondOrderProgramExpansionSuccessRectangular.success_rectangular_l
    hℳ hS hB hL hE hx hbad hbr hv
  have hpn : p ≤ succ_l j :=
    Or.inr (SecondOrderOrder.trans_l hℳ hpj (lt_own_succ_l hℳ j))
  have hvr : rectangular_l L E v (add_l p (mul_l d (succ_l k))) height := by
    simpa only [min_eq_right hpn] using hvr0
  obtain ⟨z', hz', _⟩ := function_of_semantics_l hℳ
    SecondOrderProgramTrimHeight.trim_m hZ y
  have hzEq := SecondOrderProgramTrimNormalized.height_eq_l
    hℳ hT hZ hL hE hvr hz htrim hz'
  have hzOutput : relation_l Z y z := by rw [← hzEq]; exact hz'
  obtain ⟨htargetBound, hrowTrim⟩ := positive_parent_row_below_trim_l
    hℳ hP hM hL hJ hO hE hZ hn hzOutput hParent
  have hzle := SecondOrderProgramRectangularHeight.trim_le_l hℳ hZ hL hE hvr hz
  have hrowHeight : SecondOrderOrder.lt_l row height := lt_of_lt_of_le hrowTrim hzle
  obtain ⟨entry, hentry⟩ := expansion_copy_root_entry_l
    hℳ hP hI hS hB hL hE hD hJ hT hZ hx hlast hparentSource hd hbad hv htrim hz
      hcopy hrowMax hrowTrim
  obtain ⟨q, hq⟩ := hcopy
  have hcopyAgain : SecondOrderOrder.lt_l copy (succ_l k) := ⟨q, hq⟩
  have hsuccEq : succ_l (add_l copy q) = succ_l k := by
    calc
      succ_l (add_l copy q) = add_l copy (succ_l q) :=
        (add_succ_l hℳ copy q).symm
      _ = succ_l k := hq
  have hsum : add_l copy q = k := (injective_l hℳ).eq_iff.mp hsuccEq
  have hcopyBound : copy = k ∨ SecondOrderOrder.lt_l copy k := by
    rcases predecessor_l hℳ q with rfl | ⟨q', rfl⟩
    · exact Or.inl ((add_zero_l hℳ copy).symm.trans hsum)
    · exact Or.inr ⟨q', hsum⟩
  exact parent_locality_at_expansion_copy_interval_l hℳ
    hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc hM hO
    hx hmax hlast hparentSource hd hbad hy hv htrim hz hrowMax hrowTrim hrowHeight
    hcopyPos hcopyAgain hcopyBound hn htargetBound hentry hrowsLocal hstart hfinish hParent

#print axioms no_zero_copy_middle_ancestor_l
#print axioms entry_not_lt_zero_copy_of_earlier_parent_l
#print axioms actual_ancestor_conflicts_with_zero_copy_bound_l
#print axioms row_locality_language_m
#print axioms row_locality_below_of_strong_step_l
#print axioms ancestor_locality_all_of_strong_step_l
#print axioms ancestors_local_of_row_locality_l
#print axioms parent_locality_of_lower_nonancestor_l
#print axioms parent_locality_of_not_all_lower_roots_l
#print axioms current_copy_root_ancestor_of_all_lower_source_roots_l
#print axioms earlier_parent_impossible_of_all_lower_roots_and_zero_l
#print axioms actual_parent_in_copy_of_nonzero_ascending_l
#print axioms earlier_parent_impossible_of_all_lower_roots_l
#print axioms parent_locality_of_all_lower_roots_l
#print axioms parent_locality_at_expansion_copy_target_l
#print axioms positive_offset_below_width_l
#print axioms positive_parent_row_below_trim_l
#print axioms expansion_copy_root_entry_l
#print axioms parent_locality_at_expansion_copy_interval_l
#print axioms parent_locality_step_at_expansion_copy_interval_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionEarlierParentCandidateCut
