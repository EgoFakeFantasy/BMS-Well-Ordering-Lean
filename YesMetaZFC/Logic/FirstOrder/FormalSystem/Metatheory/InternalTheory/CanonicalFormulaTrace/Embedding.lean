import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.CanonicalFormulaTrace.Compiler
/-! # 项目公式嵌入、quotation 对应与对象序列契约 -/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
set_option autoImplicit false
/-! ## 项目公式的统一轨迹入口 -/
/--
项目 bound-variable 重命名的两张索引图在 quotation 深度上实现一次 cutoff-shift。
源公式落在 `sourceDepth`，目标公式落在相邻深度 `sourceDepth + 1`。
-/
def CanonicalProjectIndexShift
    {originalDepth sourceDepth : Nat} (cutoff : Nat) (sourceMap : Fin originalDepth → Fin sourceDepth) (targetMap : Fin originalDepth → Fin (sourceDepth + 1)) :
    Prop :=
  ∀ entry,
    canonical_project_shift_depth cutoff (sourceDepth - (sourceMap entry).val - 1) = (sourceDepth + 1) - (targetMap entry).val - 1
/-- 索引图穿过一个新 binder 时，cutoff-shift 合同保持成立。 -/
theorem CanonicalProjectIndexShift.lift
    {originalDepth sourceDepth cutoff : Nat}
    {sourceMap : Fin originalDepth → Fin sourceDepth}
    {targetMap : Fin originalDepth → Fin (sourceDepth + 1)} (shift :
      CanonicalProjectIndexShift cutoff sourceMap targetMap) (hCutoff : cutoff ≤ sourceDepth) :
    CanonicalProjectIndexShift cutoff (_root_.YesMetaZFC.SetTheory.BoundEmbedding.lift sourceMap)
      (_root_.YesMetaZFC.SetTheory.BoundEmbedding.lift targetMap) := by
  intro entry
  refine Fin.cases ?_ (fun previous => ?_) entry
  · simp [_root_.YesMetaZFC.SetTheory.BoundEmbedding.lift,
      canonical_project_shift_depth_of_le hCutoff]
  · simpa [_root_.YesMetaZFC.SetTheory.BoundEmbedding.lift] using
      shift previous
/--
项目 bound 重命名的 substitution lifting 与公共 `BoundEmbedding.lift` 逐点一致。
-/
theorem project_lift_bound_renaming
    {sourceDepth targetDepth : Nat} (indexMap : Fin sourceDepth → Fin targetDepth) :
    _root_.YesMetaZFC.SetTheory.Definitional.Term.liftSubstitution (fun entry =>
          _root_.YesMetaZFC.SetTheory.Definitional.Term.bound (indexMap entry)) = (fun entry =>
        _root_.YesMetaZFC.SetTheory.Definitional.Term.bound (_root_.YesMetaZFC.SetTheory.BoundEmbedding.lift
            indexMap entry)) := by
  funext entry
  refine Fin.cases ?_ (fun previous => ?_) entry
  · rfl
  · rfl
/--
项目项沿 bound 索引图重命名后，若索引图的像避开某个绝对深度，则嵌入项也避开该
深度。
-/
theorem fs_embed_project_renamed_term_avoids_bound_depth
    {originalDepth sourceDepth targetDepth : Nat} (term : FsProjectTerm originalDepth) (indexMap : Fin originalDepth → Fin sourceDepth) (hMap :
      ∀ entry,
        sourceDepth - (indexMap entry).val - 1 ≠
          targetDepth) :
    GodelQuotation.quotation_term_avoids_bound_depth
      sourceDepth targetDepth (fs_embed_project_term (term.rename indexMap)) := by
  cases term with
  | bound entry =>
      simpa [
        _root_.YesMetaZFC.SetTheory.Definitional.Term.rename,
        _root_.YesMetaZFC.SetTheory.Definitional.Term.bind,
        fs_embed_project_term,
        GodelQuotation.quotation_term_avoids_bound_depth] using
        hMap entry
  | free id =>
      simp [
        _root_.YesMetaZFC.SetTheory.Definitional.Term.rename,
        _root_.YesMetaZFC.SetTheory.Definitional.Term.bind,
        fs_embed_project_term,
        GodelQuotation.quotation_term_avoids_bound_depth]
/--
项目公式沿一张避开 `targetDepth` 的 bound 索引图重命名后，其 Hilbert quotation
同样避开该绝对 binder 深度。
量词分支把索引图提升一层；新 binder 的绝对深度是旧入口深度，因此
`targetDepth < sourceDepth` 正好排除碰撞，而旧引用的绝对深度保持不变。
-/
theorem fs_embed_project_formula_rename_hilbert_avoids_bound_depth
    {availableStage originalDepth sourceDepth targetDepth : Nat} (formula : FsProjectFormula availableStage originalDepth)
    (indexMap : Fin originalDepth → Fin sourceDepth) (hTarget : targetDepth < sourceDepth) (hMap :
      ∀ entry,
        sourceDepth - (indexMap entry).val - 1 ≠
          targetDepth) :
    GodelQuotation.quotation_formula_avoids_bound_depth
      sourceDepth targetDepth (Formula.hilbertize SetSort.set (fs_embed_project_formula (formula.rename indexMap))) := by
  induction formula generalizing sourceDepth with
  | falsum =>
      simp [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.rename,
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.bind,
        fs_embed_project_formula, Formula.hilbertize,
        Formula.hilbert_falsum, Formula.hilbert_truth,
        GodelQuotation.quotation_formula_avoids_bound_depth,
        GodelQuotation.quotation_term_avoids_bound_depth]
      omega
  | truth =>
      simp [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.rename,
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.bind,
        fs_embed_project_formula, Formula.hilbertize,
        Formula.hilbert_truth,
        GodelQuotation.quotation_formula_avoids_bound_depth,
        GodelQuotation.quotation_term_avoids_bound_depth]
      omega
  | mem left right =>
      simpa [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.rename,
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.bind,
        fs_embed_project_formula, Formula.hilbertize,
        GodelQuotation.quotation_formula_avoids_bound_depth,
        GodelQuotation.quotation_terms_avoid_bound_depth] using
        And.intro (fs_embed_project_renamed_term_avoids_bound_depth
            left indexMap hMap) (And.intro (fs_embed_project_renamed_term_avoids_bound_depth
              right indexMap hMap)
            True.intro)
  | atom symbol hStage arguments =>
      cases symbol with
      | extensionalEq =>
          simpa [
            _root_.YesMetaZFC.SetTheory.Definitional.Formula.rename,
            _root_.YesMetaZFC.SetTheory.Definitional.Formula.bind,
            _root_.YesMetaZFC.SetTheory.Definitional.TermVector.rename,
            _root_.YesMetaZFC.SetTheory.Definitional.TermVector.get_bind,
            fs_embed_project_formula, Formula.hilbertize,
            GodelQuotation.quotation_formula_avoids_bound_depth] using
            And.intro (fs_embed_project_renamed_term_avoids_bound_depth (arguments 0) indexMap hMap) (fs_embed_project_renamed_term_avoids_bound_depth
                (arguments 1) indexMap hMap)
      | subset =>
          simpa [
            _root_.YesMetaZFC.SetTheory.Definitional.Formula.rename,
            _root_.YesMetaZFC.SetTheory.Definitional.Formula.bind,
            _root_.YesMetaZFC.SetTheory.Definitional.TermVector.rename,
            _root_.YesMetaZFC.SetTheory.Definitional.TermVector.get_bind,
            fs_embed_project_formula, Formula.hilbertize,
            GodelQuotation.quotation_formula_avoids_bound_depth,
            GodelQuotation.quotation_terms_avoid_bound_depth] using
            And.intro (fs_embed_project_renamed_term_avoids_bound_depth (arguments 0) indexMap hMap) (And.intro
                (fs_embed_project_renamed_term_avoids_bound_depth (arguments 1) indexMap hMap)
                True.intro)
  | neg body ih =>
      simpa [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.rename,
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.bind,
        fs_embed_project_formula, Formula.hilbertize,
        GodelQuotation.quotation_formula_avoids_bound_depth] using
        ih indexMap hTarget hMap
  | conj left right ihLeft ihRight =>
      simpa [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.rename,
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.bind,
        fs_embed_project_formula, Formula.hilbertize,
        Formula.hilbert_conj,
        GodelQuotation.quotation_formula_avoids_bound_depth] using
        And.intro (ihLeft indexMap hTarget hMap) (ihRight indexMap hTarget hMap)
  | disj left right ihLeft ihRight =>
      simpa [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.rename,
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.bind,
        fs_embed_project_formula, Formula.hilbertize,
        GodelQuotation.quotation_formula_avoids_bound_depth] using
        And.intro (ihLeft indexMap hTarget hMap) (ihRight indexMap hTarget hMap)
  | imp left right ihLeft ihRight =>
      simpa [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.rename,
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.bind,
        fs_embed_project_formula, Formula.hilbertize,
        GodelQuotation.quotation_formula_avoids_bound_depth] using
        And.intro (ihLeft indexMap hTarget hMap) (ihRight indexMap hTarget hMap)
  | iff left right ihLeft ihRight =>
      have hLeft :=
        ihLeft indexMap hTarget hMap
      have hRight :=
        ihRight indexMap hTarget hMap
      simpa [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.rename,
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.bind,
        fs_embed_project_formula, Formula.hilbertize,
        Formula.hilbert_iff, Formula.hilbert_conj,
        GodelQuotation.quotation_formula_avoids_bound_depth] using
        And.intro (And.intro hLeft hRight) (And.intro hRight hLeft)
  | forallE body ih =>
      have hLiftMap :
          ∀ entry,
            sourceDepth + 1 - ((_root_.YesMetaZFC.SetTheory.BoundEmbedding.lift
                  indexMap) entry).val - 1 ≠
              targetDepth := by
        intro entry
        refine Fin.cases ?_ (fun previous => ?_) entry
        · simp [
            _root_.YesMetaZFC.SetTheory.BoundEmbedding.lift]
          omega
        · have hArithmetic :
              sourceDepth + 1 - ((indexMap previous).val + 1) - 1 =
                sourceDepth - (indexMap previous).val - 1 := by
            omega
          simpa [
            _root_.YesMetaZFC.SetTheory.BoundEmbedding.lift,
            hArithmetic] using
            hMap previous
      have hBody :=
        ih (_root_.YesMetaZFC.SetTheory.BoundEmbedding.lift
            indexMap) (by omega) hLiftMap
      simpa [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.rename,
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.bind,
        project_lift_bound_renaming,
        _root_.YesMetaZFC.SetTheory.BoundEmbedding.lift,
        Function.comp_def,
        fs_embed_project_formula, Formula.hilbertize,
        GodelQuotation.quotation_formula_avoids_bound_depth] using
        And.intro (Nat.ne_of_gt hTarget) hBody
  | existsE body ih =>
      have hLiftMap :
          ∀ entry,
            sourceDepth + 1 - ((_root_.YesMetaZFC.SetTheory.BoundEmbedding.lift
                  indexMap) entry).val - 1 ≠
              targetDepth := by
        intro entry
        refine Fin.cases ?_ (fun previous => ?_) entry
        · simp [
            _root_.YesMetaZFC.SetTheory.BoundEmbedding.lift]
          omega
        · have hArithmetic :
              sourceDepth + 1 - ((indexMap previous).val + 1) - 1 =
                sourceDepth - (indexMap previous).val - 1 := by
            omega
          simpa [
            _root_.YesMetaZFC.SetTheory.BoundEmbedding.lift,
            hArithmetic] using
            hMap previous
      have hBody :=
        ih (_root_.YesMetaZFC.SetTheory.BoundEmbedding.lift
            indexMap) (by omega) hLiftMap
      simpa [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.rename,
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.bind,
        project_lift_bound_renaming,
        _root_.YesMetaZFC.SetTheory.BoundEmbedding.lift,
        Function.comp_def,
        fs_embed_project_formula, Formula.hilbertize,
        GodelQuotation.quotation_formula_avoids_bound_depth] using
        And.intro (Nat.ne_of_gt hTarget) hBody
/--
自由闭合项目项经两张同步索引图重命名后，其两次规范深度恢复正好相差
`canonical_project_shift_depth cutoff`。
-/
theorem fs_embed_project_renamed_term_variable_depths
    {originalDepth sourceDepth cutoff : Nat} (term : FsProjectTerm originalDepth) (sourceMap : Fin originalDepth → Fin sourceDepth)
    (targetMap : Fin originalDepth → Fin (sourceDepth + 1)) (hClosed :
      _root_.YesMetaZFC.SetTheory.Definitional.Term.freeSupport
        term = []) (hShift :
      CanonicalProjectIndexShift cutoff sourceMap targetMap) :
    ∃ variableDepth,
      canonical_project_variable_depth? sourceDepth (fs_embed_project_term (term.rename sourceMap)) =
        some variableDepth ∧
      canonical_project_variable_depth? (sourceDepth + 1) (fs_embed_project_term (term.rename targetMap)) =
        some (canonical_project_shift_depth
          cutoff variableDepth) := by
  cases term with
  | bound entry =>
      refine ⟨sourceDepth - (sourceMap entry).val - 1, ?_, ?_⟩
      · simp [
          _root_.YesMetaZFC.SetTheory.Definitional.Term.rename,
          _root_.YesMetaZFC.SetTheory.Definitional.Term.bind,
          fs_embed_project_term,
          canonical_project_variable_depth?, (sourceMap entry).isLt]
      · simp [
          _root_.YesMetaZFC.SetTheory.Definitional.Term.rename,
          _root_.YesMetaZFC.SetTheory.Definitional.Term.bind,
          fs_embed_project_term,
          canonical_project_variable_depth?, (targetMap entry).isLt]
        exact (hShift entry).symm
  | free id =>
      simp at hClosed
/--
任意自由闭合项目公式沿同步索引图重命名后，其 Hilbert 化结果满足公式级
cutoff-shift。
本定理对项目公式结构递归，量词分支用 `CanonicalProjectIndexShift.lift` 同时提升
两张索引图；因此内部任意深度的 binder 都自动纳入同一平移合同。
-/
theorem fs_embed_project_formula_rename_hilbert_shift
    {availableStage originalDepth sourceDepth cutoff : Nat} (formula : FsProjectFormula availableStage originalDepth)
    (sourceMap : Fin originalDepth → Fin sourceDepth) (targetMap : Fin originalDepth → Fin (sourceDepth + 1)) (hClosed :
      _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed
        formula) (hCutoff : cutoff ≤ sourceDepth) (hShift :
      CanonicalProjectIndexShift cutoff sourceMap targetMap) :
    CanonicalProjectFormulaShift cutoff sourceDepth (Formula.hilbertize SetSort.set (fs_embed_project_formula (formula.rename sourceMap)))
      (Formula.hilbertize SetSort.set (fs_embed_project_formula (formula.rename targetMap))) := by
  induction formula generalizing sourceDepth with
  | falsum =>
      simpa [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.rename,
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.bind,
        fs_embed_project_formula, Formula.hilbertize] using
        CanonicalProjectFormulaShift.hilbert_falsum hCutoff
  | truth =>
      simpa [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.rename,
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.bind,
        fs_embed_project_formula, Formula.hilbertize] using
        CanonicalProjectFormulaShift.hilbert_truth hCutoff
  | mem left right =>
      simp only [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hClosed
      rcases fs_embed_project_renamed_term_variable_depths
          left sourceMap targetMap hClosed.1 hShift with
        ⟨leftDepth, hSourceLeft, hTargetLeft⟩
      rcases fs_embed_project_renamed_term_variable_depths
          right sourceMap targetMap hClosed.2 hShift with
        ⟨rightDepth, hSourceRight, hTargetRight⟩
      simpa [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.rename,
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.bind,
        fs_embed_project_formula, Formula.hilbertize] using
        CanonicalProjectFormulaShift.membership
          hSourceLeft hSourceRight hTargetLeft hTargetRight
  | atom symbol hStage arguments =>
      simp only [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed,
        _root_.YesMetaZFC.SetTheory.Definitional.TermVector.FreeClosed] at hClosed
      rcases fs_embed_project_renamed_term_variable_depths (arguments 0) sourceMap targetMap (hClosed 0) hShift with
        ⟨leftDepth, hSourceLeft, hTargetLeft⟩
      rcases fs_embed_project_renamed_term_variable_depths (arguments 1) sourceMap targetMap (hClosed 1) hShift with
        ⟨rightDepth, hSourceRight, hTargetRight⟩
      cases symbol with
      | extensionalEq =>
          simpa [
            _root_.YesMetaZFC.SetTheory.Definitional.Formula.rename,
            _root_.YesMetaZFC.SetTheory.Definitional.Formula.bind,
            _root_.YesMetaZFC.SetTheory.Definitional.TermVector.rename,
            _root_.YesMetaZFC.SetTheory.Definitional.TermVector.get_bind,
            fs_embed_project_formula, Formula.hilbertize] using
            CanonicalProjectFormulaShift.equality
              hSourceLeft hSourceRight hTargetLeft hTargetRight
      | subset =>
          simpa [
            _root_.YesMetaZFC.SetTheory.Definitional.Formula.rename,
            _root_.YesMetaZFC.SetTheory.Definitional.Formula.bind,
            _root_.YesMetaZFC.SetTheory.Definitional.TermVector.rename,
            _root_.YesMetaZFC.SetTheory.Definitional.TermVector.get_bind,
            fs_embed_project_formula, Formula.hilbertize] using
            CanonicalProjectFormulaShift.subset
              hSourceLeft hSourceRight hTargetLeft hTargetRight
  | neg body ih =>
      simp only [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hClosed
      simpa [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.rename,
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.bind,
        fs_embed_project_formula, Formula.hilbertize] using (ih sourceMap targetMap hClosed hCutoff hShift).negation
  | conj left right ihLeft ihRight =>
      simp only [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hClosed
      simpa [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.rename,
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.bind,
        fs_embed_project_formula, Formula.hilbertize] using (ihLeft sourceMap targetMap hClosed.1 hCutoff hShift).hilbert_conjunction
          (ihRight sourceMap targetMap hClosed.2 hCutoff hShift)
  | disj left right ihLeft ihRight =>
      simp only [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hClosed
      simpa [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.rename,
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.bind,
        fs_embed_project_formula, Formula.hilbertize] using (ihLeft sourceMap targetMap hClosed.1 hCutoff hShift).negation.implication
          (ihRight sourceMap targetMap hClosed.2 hCutoff hShift)
  | imp left right ihLeft ihRight =>
      simp only [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hClosed
      simpa [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.rename,
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.bind,
        fs_embed_project_formula, Formula.hilbertize] using (ihLeft sourceMap targetMap hClosed.1 hCutoff hShift).implication
          (ihRight sourceMap targetMap hClosed.2 hCutoff hShift)
  | iff left right ihLeft ihRight =>
      simp only [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hClosed
      simpa [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.rename,
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.bind,
        fs_embed_project_formula, Formula.hilbertize] using (ihLeft sourceMap targetMap hClosed.1 hCutoff hShift).hilbert_biconditional
          (ihRight sourceMap targetMap hClosed.2 hCutoff hShift)
  | forallE body ih =>
      simp only [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hClosed
      have hBody :=
        ih (_root_.YesMetaZFC.SetTheory.BoundEmbedding.lift sourceMap) (_root_.YesMetaZFC.SetTheory.BoundEmbedding.lift targetMap)
          hClosed (by omega) (hShift.lift hCutoff)
      simpa [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.rename,
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.bind,
        project_lift_bound_renaming,
        _root_.YesMetaZFC.SetTheory.BoundEmbedding.lift,
        Function.comp_def,
        fs_embed_project_formula, Formula.hilbertize] using
        hBody.universal
  | existsE body ih =>
      simp only [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hClosed
      have hBody :=
        ih (_root_.YesMetaZFC.SetTheory.BoundEmbedding.lift sourceMap) (_root_.YesMetaZFC.SetTheory.BoundEmbedding.lift targetMap)
          hClosed (by omega) (hShift.lift hCutoff)
      simpa [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.rename,
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.bind,
        project_lift_bound_renaming,
        _root_.YesMetaZFC.SetTheory.BoundEmbedding.lift,
        Function.comp_def,
        fs_embed_project_formula, Formula.hilbertize] using
        hBody.negation.universal.negation
/-- 自由闭合的项目项嵌入后总能恢复为当前 scope 中的规范 binder 深度。 -/
theorem fs_embed_project_term_variable_depth?_exists
    {depth : Nat} (term : FsProjectTerm depth) (hClosed :
      _root_.YesMetaZFC.SetTheory.Definitional.Term.freeSupport
        term = []) :
    ∃ variableDepth,
      canonical_project_variable_depth? depth (fs_embed_project_term term) =
        some variableDepth := by
  cases term with
  | bound entry =>
      exact ⟨depth - entry.val - 1, by
        simp [fs_embed_project_term,
          canonical_project_variable_depth?,
          entry.isLt]⟩
  | free id =>
      simp at hClosed
/--
任意自由闭合项目公式在其 intrinsically scoped 深度处，经 Hilbert 化后都能生成规范轨迹。
-/
theorem fs_embed_project_formula_hilbert_traceable
    {availableStage depth : Nat} (formula : FsProjectFormula availableStage depth) (hClosed :
      _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed
        formula) :
    CanonicalProjectTraceable depth (Formula.hilbertize SetSort.set (fs_embed_project_formula formula)) := by
  induction formula with
  | falsum =>
      simpa [fs_embed_project_formula, Formula.hilbertize] using
        canonical_project_traceable_hilbert_falsum _
  | truth =>
      simpa [fs_embed_project_formula, Formula.hilbertize] using
        canonical_project_traceable_hilbert_truth _
  | mem left right =>
      simp only [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hClosed
      simpa [fs_embed_project_formula, Formula.hilbertize] using
        canonical_project_traceable_membership (fs_embed_project_term_variable_depth?_exists
            left hClosed.1) (fs_embed_project_term_variable_depth?_exists
            right hClosed.2)
  | atom symbol hStage arguments =>
      simp only [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed,
        _root_.YesMetaZFC.SetTheory.Definitional.TermVector.FreeClosed] at hClosed
      cases symbol with
      | extensionalEq =>
          simpa [fs_embed_project_formula, Formula.hilbertize] using
            canonical_project_traceable_equality (fs_embed_project_term_variable_depth?_exists (arguments 0) (hClosed 0))
              (fs_embed_project_term_variable_depth?_exists (arguments 1) (hClosed 1))
      | subset =>
          simpa [fs_embed_project_formula, Formula.hilbertize] using
            canonical_project_traceable_subset (fs_embed_project_term_variable_depth?_exists (arguments 0) (hClosed 0))
              (fs_embed_project_term_variable_depth?_exists (arguments 1) (hClosed 1))
  | neg body ih =>
      simp only [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hClosed
      simpa [fs_embed_project_formula, Formula.hilbertize] using (ih hClosed).negation
  | conj left right ihLeft ihRight =>
      simp only [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hClosed
      simpa [fs_embed_project_formula, Formula.hilbertize,
        Formula.hilbert_conj] using (ihLeft hClosed.1).hilbert_conjunction (ihRight hClosed.2)
  | disj left right ihLeft ihRight =>
      simp only [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hClosed
      simpa [fs_embed_project_formula, Formula.hilbertize] using (ihLeft hClosed.1).negation.implication (ihRight hClosed.2)
  | imp left right ihLeft ihRight =>
      simp only [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hClosed
      simpa [fs_embed_project_formula, Formula.hilbertize] using (ihLeft hClosed.1).implication (ihRight hClosed.2)
  | iff left right ihLeft ihRight =>
      simp only [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hClosed
      simpa [fs_embed_project_formula, Formula.hilbertize,
        Formula.hilbert_iff] using (ihLeft hClosed.1).hilbert_biconditional (ihRight hClosed.2)
  | forallE body ih =>
      simp only [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hClosed
      simpa [fs_embed_project_formula, Formula.hilbertize] using (ih hClosed).universal
  | existsE body ih =>
      simp only [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hClosed
      simpa [fs_embed_project_formula, Formula.hilbertize] using (ih hClosed).negation.universal.negation
/-- 自由闭合项目公式在任意连续起点都有规范 quotation 轨迹。 -/
theorem fs_embed_project_formula_hilbert_trace_from?_exists
    {availableStage depth start : Nat} (formula : FsProjectFormula availableStage depth) (hClosed :
      _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed
        formula) :
    ∃ trace,
      canonical_project_hilbert_trace_from?
          start depth (Formula.hilbertize SetSort.set (fs_embed_project_formula formula)) =
        some trace :=
  fs_embed_project_formula_hilbert_traceable
    formula hClosed start
/-- 从第零行开始的项目公式规范 quotation 轨迹总存在。 -/
theorem fs_embed_project_formula_hilbert_trace?_exists
    {availableStage depth : Nat} (formula : FsProjectFormula availableStage depth) (hClosed :
      _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed
        formula) :
    ∃ trace,
      canonical_project_hilbert_trace?
          depth (Formula.hilbertize SetSort.set (fs_embed_project_formula formula)) =
        some trace :=
  fs_embed_project_formula_hilbert_trace_from?_exists
    formula hClosed
/-! ## 编译器与 quotation 的对应 -/
/--
成功编译的轨迹根代码与同一入口深度下的规范 Hilbert quotation 完全一致。
-/
theorem canonical_project_hilbert_trace_from?_root_quote
    {start entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace_from?
        start entryDepth formula = some trace) :
    GodelQuotation.Numbered.quote_hilbert_with?
        GodelQuotation.free_name
        GodelQuotation.bound_name (GodelQuotation.canonical_bound_names
          entryDepth)
        entryDepth formula =
      some trace.rootCode := by
  induction formula generalizing start entryDepth trace with
  | falsum =>
      simp [canonical_project_hilbert_trace_from?] at hTrace
  | truth =>
      simp [canonical_project_hilbert_trace_from?] at hTrace
  | rel relation arguments =>
      cases relation <;>
        cases arguments with
        | nil =>
            simp [canonical_project_hilbert_trace_from?] at hTrace
        | cons left rest =>
            cases rest with
            | nil =>
                simp [canonical_project_hilbert_trace_from?] at hTrace
            | cons right tail =>
                cases tail with
                | cons extra tail =>
                    simp [canonical_project_hilbert_trace_from?] at hTrace
                | nil =>
                    simp only [canonical_project_hilbert_trace_from?] at hTrace
                    all_goals
                      cases hLeftDepth :
                          canonical_project_variable_depth?
                            entryDepth left <;>
                        try simp [hLeftDepth] at hTrace
                    all_goals
                      cases hRightDepth :
                          canonical_project_variable_depth?
                            entryDepth right <;>
                        try simp [hRightDepth] at hTrace
                    all_goals
                      subst trace
                      have hLeftQuote :=
                        canonical_project_variable_depth?_quote
                          hLeftDepth
                      have hRightQuote :=
                        canonical_project_variable_depth?_quote
                          hRightDepth
                      simp [GodelQuotation.Numbered.quote_hilbert_with?,
                        GodelQuotation.Numbered.quote_relation_with?,
                        hLeftQuote, hRightQuote,
                        CanonicalProjectTrace.atomic,
                        project_subset_atomic_code_term,
                        GodelQuotation.Numbered.argument_sequence,
                        GodelQuotation.fs_relation_kind_eq_predicate (relation := RelationSymbol.subset) (by decide)]
  | equal left right =>
      simp only [canonical_project_hilbert_trace_from?] at hTrace
      cases hLeftDepth :
          canonical_project_variable_depth?
            entryDepth left <;>
        try simp [hLeftDepth] at hTrace
      cases hRightDepth :
          canonical_project_variable_depth?
            entryDepth right <;>
        try simp [hRightDepth] at hTrace
      subst trace
      have hLeftQuote :=
        canonical_project_variable_depth?_quote hLeftDepth
      have hRightQuote :=
        canonical_project_variable_depth?_quote hRightDepth
      simp [GodelQuotation.Numbered.quote_hilbert_with?,
        hLeftQuote, hRightQuote,
        CanonicalProjectTrace.atomic]
  | neg body ih =>
      simp only [canonical_project_hilbert_trace_from?] at hTrace
      cases hBody :
          canonical_project_hilbert_trace_from?
            start entryDepth body with
      | none =>
          simp [hBody] at hTrace
      | some bodyTrace =>
          simp [hBody] at hTrace
          subst trace
          have hBodyQuote := ih hBody
          simp [GodelQuotation.Numbered.quote_hilbert_with?,
            hBodyQuote, CanonicalProjectTrace.negation]
  | conj left right ihLeft ihRight =>
      simp [canonical_project_hilbert_trace_from?] at hTrace
  | disj left right ihLeft ihRight =>
      simp [canonical_project_hilbert_trace_from?] at hTrace
  | imp left right ihLeft ihRight =>
      simp only [canonical_project_hilbert_trace_from?] at hTrace
      cases hLeft :
          canonical_project_hilbert_trace_from?
            start entryDepth left with
      | none =>
          simp [hLeft] at hTrace
      | some leftTrace =>
          simp [hLeft] at hTrace
          cases hRight :
              canonical_project_hilbert_trace_from? (start + leftTrace.rows.length)
                entryDepth right with
          | none =>
              simp [hRight] at hTrace
          | some rightTrace =>
              simp [hRight] at hTrace
              subst trace
              have hLeftQuote := ihLeft hLeft
              have hRightQuote := ihRight hRight
              simp [GodelQuotation.Numbered.quote_hilbert_with?,
                hLeftQuote, hRightQuote,
                CanonicalProjectTrace.implication]
  | iff left right ihLeft ihRight =>
      simp [canonical_project_hilbert_trace_from?] at hTrace
  | forallE sort body ih =>
      cases sort
      simp only [canonical_project_hilbert_trace_from?] at hTrace
      cases hBody :
          canonical_project_hilbert_trace_from?
            start (entryDepth + 1) body with
      | none =>
          simp [hBody] at hTrace
      | some bodyTrace =>
          simp [hBody] at hTrace
          subst trace
          have hBodyQuote := ih hBody
          rw [GodelQuotation.canonical_bound_names] at hBodyQuote
          simp [GodelQuotation.Numbered.quote_hilbert_with?,
            hBodyQuote, CanonicalProjectTrace.universal]
  | existsE sort body ih =>
      simp [canonical_project_hilbert_trace_from?] at hTrace
/-- 第零行编译器的根代码对应定理。 -/
theorem canonical_project_hilbert_trace?_root_quote
    {entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace?
        entryDepth formula = some trace) :
    GodelQuotation.Numbered.quote_hilbert_with?
        GodelQuotation.free_name
        GodelQuotation.bound_name (GodelQuotation.canonical_bound_names
          entryDepth)
      entryDepth formula =
      some trace.rootCode :=
  canonical_project_hilbert_trace_from?_root_quote hTrace
/-! ## 根公式对齐 -/
/-- 成功编译的轨迹根公式就是编译输入。 -/
theorem canonical_project_hilbert_trace_from?_root_formula
    {start entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace_from?
        start entryDepth formula = some trace) :
    trace.rootFormula = formula := by
  induction formula generalizing start entryDepth trace with
  | falsum =>
      simp [canonical_project_hilbert_trace_from?] at hTrace
  | truth =>
      simp [canonical_project_hilbert_trace_from?] at hTrace
  | rel relation arguments =>
      cases relation <;>
        cases arguments with
        | nil =>
            simp [canonical_project_hilbert_trace_from?] at hTrace
        | cons left rest =>
            cases rest with
            | nil =>
                simp [canonical_project_hilbert_trace_from?] at hTrace
            | cons right tail =>
                cases tail with
                | cons extra tail =>
                    simp [canonical_project_hilbert_trace_from?] at hTrace
                | nil =>
                    simp only [canonical_project_hilbert_trace_from?] at hTrace
                    all_goals
                      cases hLeftDepth :
                          canonical_project_variable_depth?
                            entryDepth left <;>
                        try simp [hLeftDepth] at hTrace
                    all_goals
                      cases hRightDepth :
                          canonical_project_variable_depth?
                            entryDepth right <;>
                        try simp [hRightDepth] at hTrace
                    all_goals
                      subst trace
                      rfl
  | equal left right =>
      simp only [canonical_project_hilbert_trace_from?] at hTrace
      cases hLeftDepth :
          canonical_project_variable_depth?
            entryDepth left <;>
        try simp [hLeftDepth] at hTrace
      cases hRightDepth :
          canonical_project_variable_depth?
            entryDepth right <;>
        try simp [hRightDepth] at hTrace
      subst trace
      rfl
  | neg body ih =>
      simp only [canonical_project_hilbert_trace_from?] at hTrace
      cases hBody :
          canonical_project_hilbert_trace_from?
            start entryDepth body with
      | none =>
          simp [hBody] at hTrace
      | some bodyTrace =>
          simp [hBody] at hTrace
          subst trace
          simp [CanonicalProjectTrace.negation, ih hBody]
  | conj left right ihLeft ihRight =>
      simp [canonical_project_hilbert_trace_from?] at hTrace
  | disj left right ihLeft ihRight =>
      simp [canonical_project_hilbert_trace_from?] at hTrace
  | imp left right ihLeft ihRight =>
      simp only [canonical_project_hilbert_trace_from?] at hTrace
      cases hLeft :
          canonical_project_hilbert_trace_from?
            start entryDepth left with
      | none =>
          simp [hLeft] at hTrace
      | some leftTrace =>
          simp [hLeft] at hTrace
          cases hRight :
              canonical_project_hilbert_trace_from? (start + leftTrace.rows.length)
                entryDepth right with
          | none =>
              simp [hRight] at hTrace
          | some rightTrace =>
              simp [hRight] at hTrace
              subst trace
              simp [CanonicalProjectTrace.implication,
                ihLeft hLeft, ihRight hRight]
  | iff left right ihLeft ihRight =>
      simp [canonical_project_hilbert_trace_from?] at hTrace
  | forallE sort body ih =>
      cases sort
      simp only [canonical_project_hilbert_trace_from?] at hTrace
      cases hBody :
          canonical_project_hilbert_trace_from?
            start (entryDepth + 1) body with
      | none =>
          simp [hBody] at hTrace
      | some bodyTrace =>
          simp [hBody] at hTrace
          subst trace
          simp [CanonicalProjectTrace.universal, ih hBody]
  | existsE sort body ih =>
      simp [canonical_project_hilbert_trace_from?] at hTrace
/-- 根行以自身保存的来源公式读取时满足规范 quotation。 -/
theorem canonical_project_hilbert_trace_from?_root_row_quote
    {start entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace_from?
        start entryDepth formula = some trace) :
    GodelQuotation.Numbered.quote_hilbert_with?
        GodelQuotation.free_name
        GodelQuotation.bound_name (GodelQuotation.canonical_bound_names entryDepth)
        entryDepth trace.rootFormula =
      some trace.rootCode := by
  rw [canonical_project_hilbert_trace_from?_root_formula hTrace]
  exact canonical_project_hilbert_trace_from?_root_quote hTrace
/-! ## 每一行的 quotation 来源 -/
/-- 轨迹中的每一行都确实引用其记录的来源子公式。 -/
def CanonicalProjectTrace.RowsQuoted (trace : CanonicalProjectTrace) : Prop :=
  ∀ row, row ∈ trace.rows →
    GodelQuotation.Numbered.quote_hilbert_with?
        GodelQuotation.free_name
        GodelQuotation.bound_name (GodelQuotation.canonical_bound_names row.depth)
        row.depth row.formula =
      some row.code
/-- 编译成功自动给出整条轨迹的逐行 quotation 证书。 -/
theorem canonical_project_hilbert_trace_from?_rows_quoted
    {start entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace_from?
        start entryDepth formula = some trace) :
    trace.RowsQuoted := by
  induction formula generalizing start entryDepth trace with
  | falsum =>
      simp [canonical_project_hilbert_trace_from?] at hTrace
  | truth =>
      simp [canonical_project_hilbert_trace_from?] at hTrace
  | rel relation arguments =>
      have hRootRowQuote :=
        canonical_project_hilbert_trace_from?_root_row_quote
          hTrace
      cases relation <;>
        cases arguments with
        | nil =>
            simp [canonical_project_hilbert_trace_from?] at hTrace
        | cons left rest =>
            cases rest with
            | nil =>
                simp [canonical_project_hilbert_trace_from?] at hTrace
            | cons right tail =>
                cases tail with
                | cons extra tail =>
                    simp [canonical_project_hilbert_trace_from?] at hTrace
                | nil =>
                    simp only [canonical_project_hilbert_trace_from?] at hTrace
                    all_goals
                      cases hLeftDepth :
                          canonical_project_variable_depth?
                            entryDepth left <;>
                        try simp [hLeftDepth] at hTrace
                    all_goals
                      cases hRightDepth :
                          canonical_project_variable_depth?
                            entryDepth right <;>
                        try simp [hRightDepth] at hTrace
                    all_goals
                      subst trace
                      intro row hRow
                      simp [CanonicalProjectTrace.atomic] at hRow
                      subst row
                      simpa [CanonicalProjectTrace.atomic] using
                        hRootRowQuote
  | equal left right =>
      have hRootRowQuote :=
        canonical_project_hilbert_trace_from?_root_row_quote
          hTrace
      simp only [canonical_project_hilbert_trace_from?] at hTrace
      cases hLeftDepth :
          canonical_project_variable_depth?
            entryDepth left <;>
        try simp [hLeftDepth] at hTrace
      cases hRightDepth :
          canonical_project_variable_depth?
            entryDepth right <;>
        try simp [hRightDepth] at hTrace
      subst trace
      intro row hRow
      simp [CanonicalProjectTrace.atomic] at hRow
      subst row
      simpa [CanonicalProjectTrace.atomic] using hRootRowQuote
  | neg body ih =>
      have hRootRowQuote :=
        canonical_project_hilbert_trace_from?_root_row_quote
          hTrace
      simp only [canonical_project_hilbert_trace_from?] at hTrace
      cases hBody :
          canonical_project_hilbert_trace_from?
            start entryDepth body with
      | none =>
          simp [hBody] at hTrace
      | some bodyTrace =>
          simp [hBody] at hTrace
          subst trace
          intro row hRow
          rcases List.mem_append.mp hRow with
            hBodyRow | hRootRow
          · exact ih hBody row hBodyRow
          · simp only [List.mem_singleton] at hRootRow
            subst row
            simpa [CanonicalProjectTrace.negation] using
              hRootRowQuote
  | conj left right ihLeft ihRight =>
      simp [canonical_project_hilbert_trace_from?] at hTrace
  | disj left right ihLeft ihRight =>
      simp [canonical_project_hilbert_trace_from?] at hTrace
  | imp left right ihLeft ihRight =>
      have hRootRowQuote :=
        canonical_project_hilbert_trace_from?_root_row_quote
          hTrace
      simp only [canonical_project_hilbert_trace_from?] at hTrace
      cases hLeft :
          canonical_project_hilbert_trace_from?
            start entryDepth left with
      | none =>
          simp [hLeft] at hTrace
      | some leftTrace =>
          simp [hLeft] at hTrace
          cases hRight :
              canonical_project_hilbert_trace_from? (start + leftTrace.rows.length)
                entryDepth right with
          | none =>
              simp [hRight] at hTrace
          | some rightTrace =>
              simp [hRight] at hTrace
              subst trace
              intro row hRow
              rcases List.mem_append.mp hRow with
                hChildren | hRootRow
              · rcases List.mem_append.mp hChildren with
                  hLeftRow | hRightRow
                · exact ihLeft hLeft row hLeftRow
                · exact ihRight hRight row hRightRow
              · simp only [List.mem_singleton] at hRootRow
                subst row
                simpa [CanonicalProjectTrace.implication] using
                  hRootRowQuote
  | iff left right ihLeft ihRight =>
      simp [canonical_project_hilbert_trace_from?] at hTrace
  | forallE sort body ih =>
      have hRootRowQuote :=
        canonical_project_hilbert_trace_from?_root_row_quote
          hTrace
      cases sort
      simp only [canonical_project_hilbert_trace_from?] at hTrace
      cases hBody :
          canonical_project_hilbert_trace_from?
            start (entryDepth + 1) body with
      | none =>
          simp [hBody] at hTrace
      | some bodyTrace =>
          simp [hBody] at hTrace
          subst trace
          intro row hRow
          rcases List.mem_append.mp hRow with
            hBodyRow | hRootRow
          · exact ih hBody row hBodyRow
          · simp only [List.mem_singleton] at hRootRow
            subst row
            simpa [CanonicalProjectTrace.universal] using
              hRootRowQuote
  | existsE sort body ih =>
      simp [canonical_project_hilbert_trace_from?] at hTrace
/-! ## 轨迹到对象有限序列的边界 -/
/--
任意连续片段中，根行的绝对编号恰在该片段的最后一行。
`start` 使这条合同可递归用于蕴含右子树等非零起点的片段；第零行实例随后直接给出
对象有限序列的末行索引。
-/
theorem canonical_project_hilbert_trace_from?_root_index
    {start entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace_from?
        start entryDepth formula = some trace) :
    trace.rootIndex + 1 =
      start + trace.rows.length := by
  cases formula with
  | falsum =>
      simp [canonical_project_hilbert_trace_from?] at hTrace
  | truth =>
      simp [canonical_project_hilbert_trace_from?] at hTrace
  | rel relation arguments =>
      cases relation <;>
        cases arguments with
        | nil =>
            simp [canonical_project_hilbert_trace_from?] at hTrace
        | cons left rest =>
            cases rest with
            | nil =>
                simp [canonical_project_hilbert_trace_from?] at hTrace
            | cons right tail =>
                cases tail with
                | cons extra tail =>
                    simp [canonical_project_hilbert_trace_from?] at hTrace
                | nil =>
                    simp only [canonical_project_hilbert_trace_from?] at hTrace
                    all_goals
                      cases hLeftDepth :
                          canonical_project_variable_depth?
                            entryDepth left <;>
                        try simp [hLeftDepth] at hTrace
                    all_goals
                      cases hRightDepth :
                          canonical_project_variable_depth?
                            entryDepth right <;>
                        try simp [hRightDepth] at hTrace
                    all_goals
                      subst trace
                      simp [CanonicalProjectTrace.atomic]
  | equal left right =>
      simp only [canonical_project_hilbert_trace_from?] at hTrace
      cases hLeftDepth :
          canonical_project_variable_depth?
            entryDepth left <;>
        try simp [hLeftDepth] at hTrace
      cases hRightDepth :
          canonical_project_variable_depth?
            entryDepth right <;>
        try simp [hRightDepth] at hTrace
      subst trace
      simp [CanonicalProjectTrace.atomic]
  | neg body =>
      simp only [canonical_project_hilbert_trace_from?] at hTrace
      cases hBody :
          canonical_project_hilbert_trace_from?
            start entryDepth body with
      | none =>
          simp [hBody] at hTrace
      | some bodyTrace =>
          simp [hBody] at hTrace
          subst trace
          simp [CanonicalProjectTrace.negation]
          omega
  | conj left right =>
      simp [canonical_project_hilbert_trace_from?] at hTrace
  | disj left right =>
      simp [canonical_project_hilbert_trace_from?] at hTrace
  | imp left right =>
      simp only [canonical_project_hilbert_trace_from?] at hTrace
      cases hLeft :
          canonical_project_hilbert_trace_from?
            start entryDepth left with
      | none =>
          simp [hLeft] at hTrace
      | some leftTrace =>
          simp [hLeft] at hTrace
          cases hRight :
              canonical_project_hilbert_trace_from? (start + leftTrace.rows.length)
                entryDepth right with
          | none =>
              simp [hRight] at hTrace
          | some rightTrace =>
              simp [hRight] at hTrace
              subst trace
              simp [CanonicalProjectTrace.implication]
              omega
  | iff left right =>
      simp [canonical_project_hilbert_trace_from?] at hTrace
  | forallE sort body =>
      cases sort
      simp only [canonical_project_hilbert_trace_from?] at hTrace
      cases hBody :
          canonical_project_hilbert_trace_from?
            start (entryDepth + 1) body with
      | none =>
          simp [hBody] at hTrace
      | some bodyTrace =>
          simp [hBody] at hTrace
          subst trace
          simp [CanonicalProjectTrace.universal]
          omega
  | existsE sort body =>
      simp [canonical_project_hilbert_trace_from?] at hTrace
/-- 第零行轨迹中根行编号就是对象列表的最后位置。 -/
theorem canonical_project_hilbert_trace?_root_index
    {entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace?
        entryDepth formula = some trace) :
    trace.rootIndex + 1 = trace.rows.length := by
  simpa using (canonical_project_hilbert_trace_from?_root_index hTrace)
/--
编译轨迹的两条对象列表都以根行结束。
这条结构合同把后序编译器与对象分类器的“末行是目标公式码及入口深度”要求直接
对齐；后续只需证明标准序列定义域的最大元确为该末行位置。
-/
theorem canonical_project_hilbert_trace_from?_terminal_terms
    {start entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace_from?
        start entryDepth formula = some trace) :
    ∃ codePrefix depthPrefix,
      trace.code_terms =
          codePrefix ++ [trace.rootCode] ∧
        trace.depth_terms =
          depthPrefix ++ [numₘ(entryDepth)] := by
  cases formula with
  | falsum =>
      simp [canonical_project_hilbert_trace_from?] at hTrace
  | truth =>
      simp [canonical_project_hilbert_trace_from?] at hTrace
  | rel relation arguments =>
      cases relation <;>
        cases arguments with
        | nil =>
            simp [canonical_project_hilbert_trace_from?] at hTrace
        | cons left rest =>
            cases rest with
            | nil =>
                simp [canonical_project_hilbert_trace_from?] at hTrace
            | cons right tail =>
                cases tail with
                | cons extra tail =>
                    simp [canonical_project_hilbert_trace_from?] at hTrace
                | nil =>
                    simp only [canonical_project_hilbert_trace_from?] at hTrace
                    all_goals
                      cases hLeftDepth :
                          canonical_project_variable_depth?
                            entryDepth left <;>
                        try simp [hLeftDepth] at hTrace
                    all_goals
                      cases hRightDepth :
                          canonical_project_variable_depth?
                            entryDepth right <;>
                        try simp [hRightDepth] at hTrace
                    all_goals
                      subst trace
                      refine ⟨List.nil, List.nil, ?_⟩
                      simp [CanonicalProjectTrace.code_terms,
                        CanonicalProjectTrace.depth_terms,
                        CanonicalProjectTrace.atomic]
  | equal left right =>
      simp only [canonical_project_hilbert_trace_from?] at hTrace
      cases hLeftDepth :
          canonical_project_variable_depth?
            entryDepth left <;>
        try simp [hLeftDepth] at hTrace
      cases hRightDepth :
          canonical_project_variable_depth?
            entryDepth right <;>
        try simp [hRightDepth] at hTrace
      subst trace
      refine ⟨List.nil, List.nil, ?_⟩
      simp [CanonicalProjectTrace.code_terms,
        CanonicalProjectTrace.depth_terms,
        CanonicalProjectTrace.atomic]
  | neg body =>
      simp only [canonical_project_hilbert_trace_from?] at hTrace
      cases hBody :
          canonical_project_hilbert_trace_from?
            start entryDepth body with
      | none =>
          simp [hBody] at hTrace
      | some bodyTrace =>
          simp [hBody] at hTrace
          subst trace
          exact ⟨bodyTrace.code_terms, bodyTrace.depth_terms, by
            simp [CanonicalProjectTrace.code_terms,
              CanonicalProjectTrace.depth_terms,
              CanonicalProjectTrace.negation]⟩
  | conj left right =>
      simp [canonical_project_hilbert_trace_from?] at hTrace
  | disj left right =>
      simp [canonical_project_hilbert_trace_from?] at hTrace
  | imp left right =>
      simp only [canonical_project_hilbert_trace_from?] at hTrace
      cases hLeft :
          canonical_project_hilbert_trace_from?
            start entryDepth left with
      | none =>
          simp [hLeft] at hTrace
      | some leftTrace =>
          simp [hLeft] at hTrace
          cases hRight :
              canonical_project_hilbert_trace_from? (start + leftTrace.rows.length)
                entryDepth right with
          | none =>
              simp [hRight] at hTrace
          | some rightTrace =>
              simp [hRight] at hTrace
              subst trace
              exact ⟨
                leftTrace.code_terms ++ rightTrace.code_terms,
                leftTrace.depth_terms ++ rightTrace.depth_terms,
                by
                  simp [CanonicalProjectTrace.code_terms,
                    CanonicalProjectTrace.depth_terms,
                    CanonicalProjectTrace.implication,
                    List.map_append, List.append_assoc]⟩
  | iff left right =>
      simp [canonical_project_hilbert_trace_from?] at hTrace
  | forallE sort body =>
      cases sort
      simp only [canonical_project_hilbert_trace_from?] at hTrace
      cases hBody :
          canonical_project_hilbert_trace_from?
            start (entryDepth + 1) body with
      | none =>
          simp [hBody] at hTrace
      | some bodyTrace =>
          simp [hBody] at hTrace
          subst trace
          exact ⟨bodyTrace.code_terms, bodyTrace.depth_terms, by
            simp [CanonicalProjectTrace.code_terms,
              CanonicalProjectTrace.depth_terms,
              CanonicalProjectTrace.universal]⟩
  | existsE sort body =>
      simp [canonical_project_hilbert_trace_from?] at hTrace
/--
连续片段中根行的公式码在相对起点的局部位置精确读回。
这条形式保留了 `start`，可直接用于蕴含右子树和量词体等递归片段。
-/
theorem canonical_project_hilbert_trace_from?_root_code_getElem_local
    {start entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace_from?
        start entryDepth formula = some trace) :
    trace.code_terms[trace.rootIndex - start]? =
      some trace.rootCode := by
  rcases canonical_project_hilbert_trace_from?_terminal_terms hTrace with
    ⟨codePrefix, _, hCodes, _⟩
  have hRoot :=
    canonical_project_hilbert_trace_from?_root_index hTrace
  have hTermsLength :
      trace.code_terms.length = trace.rows.length := by
    simp [CanonicalProjectTrace.code_terms]
  have hRootLocal : trace.rootIndex - start = codePrefix.length := by
    rw [hCodes] at hTermsLength
    simp only [List.length_append, List.length_singleton] at hTermsLength
    omega
  rw [hCodes, hRootLocal]
  simp
/--
连续片段中根行的入口深度在相对起点的局部位置精确读回。
-/
theorem canonical_project_hilbert_trace_from?_root_depth_getElem_local
    {start entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace_from?
        start entryDepth formula = some trace) :
    trace.depth_terms[trace.rootIndex - start]? =
      some numₘ(entryDepth) := by
  rcases canonical_project_hilbert_trace_from?_terminal_terms hTrace with
    ⟨_, depthPrefix, _, hDepths⟩
  have hRoot :=
    canonical_project_hilbert_trace_from?_root_index hTrace
  have hTermsLength :
      trace.depth_terms.length = trace.rows.length := by
    simp [CanonicalProjectTrace.depth_terms]
  have hRootLocal : trace.rootIndex - start = depthPrefix.length := by
    rw [hDepths] at hTermsLength
    simp only [List.length_append, List.length_singleton] at hTermsLength
    omega
  rw [hDepths, hRootLocal]
  simp
/-- 成功编译的轨迹至少含有根行。 -/
theorem canonical_project_hilbert_trace_from?_rows_nonempty
    {start entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace_from?
        start entryDepth formula = some trace) :
    trace.rows ≠ [] := by
  rcases canonical_project_hilbert_trace_from?_terminal_terms hTrace with
    ⟨codePrefix, _, hCodes, _⟩
  intro hRows
  have hEmpty : trace.code_terms = [] := by
    simp [CanonicalProjectTrace.code_terms, hRows]
  rw [hCodes] at hEmpty
  simp at hEmpty
/-- 连续编译片段的根编号位于该片段覆盖的绝对半开区间内。 -/
theorem canonical_project_hilbert_trace_from?_root_bounds
    {start entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace_from?
        start entryDepth formula = some trace) :
    start ≤ trace.rootIndex ∧
      trace.rootIndex < start + trace.rows.length := by
  have hRoot :=
    canonical_project_hilbert_trace_from?_root_index hTrace
  have hRows : trace.rows.length ≠ 0 := by
    intro hLength
    apply canonical_project_hilbert_trace_from?_rows_nonempty hTrace
    exact List.eq_nil_of_length_eq_zero hLength
  omega
/-- 编译器成功返回时，整条连续轨迹带有真实前驱行的归纳证据。 -/
theorem canonical_project_hilbert_trace_from?_rows_evidence
    {start entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace}
    (hTrace :
      canonical_project_hilbert_trace_from?
        start entryDepth formula = some trace) :
    trace.RowsEvidenceFrom start := by
  induction formula generalizing start entryDepth trace with
  | falsum =>
      simp [canonical_project_hilbert_trace_from?] at hTrace
  | truth =>
      simp [canonical_project_hilbert_trace_from?] at hTrace
  | rel relation arguments =>
      cases relation <;>
        cases arguments with
        | nil =>
            simp [canonical_project_hilbert_trace_from?] at hTrace
        | cons left rest =>
            cases rest with
            | nil =>
                simp [canonical_project_hilbert_trace_from?] at hTrace
            | cons right tail =>
                cases tail with
                | cons extra tail =>
                    simp [canonical_project_hilbert_trace_from?] at hTrace
                | nil =>
                    simp only [
                      canonical_project_hilbert_trace_from?] at hTrace
                    all_goals
                      cases hLeftDepth :
                          canonical_project_variable_depth?
                            entryDepth left <;>
                        try simp [hLeftDepth] at hTrace
                    all_goals
                      cases hRightDepth :
                          canonical_project_variable_depth?
                            entryDepth right <;>
                        try simp [hRightDepth] at hTrace
                    all_goals
                      subst trace
                      first
                      | simpa using
                          (CanonicalProjectTrace.atomic_rows_evidence
                            start entryDepth
                            (.rel RelationSymbol.membership [left, right])
                            .membership _ _
                            (canonical_project_variable_depth?_lt
                              hLeftDepth)
                            (canonical_project_variable_depth?_lt
                              hRightDepth))
                      | simpa using
                          (CanonicalProjectTrace.atomic_rows_evidence
                            start entryDepth
                            (.rel RelationSymbol.subset [left, right])
                            .subset _ _
                            (canonical_project_variable_depth?_lt
                              hLeftDepth)
                            (canonical_project_variable_depth?_lt
                              hRightDepth))
  | equal left right =>
      simp only [canonical_project_hilbert_trace_from?] at hTrace
      cases hLeftDepth :
          canonical_project_variable_depth?
            entryDepth left <;>
        try simp [hLeftDepth] at hTrace
      cases hRightDepth :
          canonical_project_variable_depth?
            entryDepth right <;>
        try simp [hRightDepth] at hTrace
      subst trace
      simpa using
        (CanonicalProjectTrace.atomic_rows_evidence
          start entryDepth (.equal left right)
          .equality _ _
          (canonical_project_variable_depth?_lt hLeftDepth)
          (canonical_project_variable_depth?_lt hRightDepth))
  | neg body ih =>
      simp only [canonical_project_hilbert_trace_from?] at hTrace
      cases hBody :
          canonical_project_hilbert_trace_from?
            start entryDepth body with
      | none =>
          simp [hBody] at hTrace
      | some bodyTrace =>
          simp [hBody] at hTrace
          subst trace
          exact CanonicalProjectTrace.negation_rows_evidence
            bodyTrace (ih hBody)
            (canonical_project_hilbert_trace_from?_root_bounds hBody)
            (canonical_project_hilbert_trace_from?_root_code_getElem_local
              hBody)
            (canonical_project_hilbert_trace_from?_root_depth_getElem_local
              hBody)
  | conj left right ihLeft ihRight =>
      simp [canonical_project_hilbert_trace_from?] at hTrace
  | disj left right ihLeft ihRight =>
      simp [canonical_project_hilbert_trace_from?] at hTrace
  | imp left right ihLeft ihRight =>
      simp only [canonical_project_hilbert_trace_from?] at hTrace
      cases hLeft :
          canonical_project_hilbert_trace_from?
            start entryDepth left with
      | none =>
          simp [hLeft] at hTrace
      | some leftTrace =>
          simp [hLeft] at hTrace
          cases hRight :
              canonical_project_hilbert_trace_from?
                (start + leftTrace.rows.length)
                entryDepth right with
          | none =>
              simp [hRight] at hTrace
          | some rightTrace =>
              simp [hRight] at hTrace
              subst trace
              exact
                CanonicalProjectTrace.implication_rows_evidence
                  leftTrace rightTrace
                  (ihLeft hLeft) (ihRight hRight)
                  (canonical_project_hilbert_trace_from?_root_bounds
                    hLeft)
                  (canonical_project_hilbert_trace_from?_root_bounds
                    hRight)
                  (canonical_project_hilbert_trace_from?_root_code_getElem_local
                    hLeft)
                  (canonical_project_hilbert_trace_from?_root_code_getElem_local
                    hRight)
                  (canonical_project_hilbert_trace_from?_root_depth_getElem_local
                    hLeft)
                  (canonical_project_hilbert_trace_from?_root_depth_getElem_local
                    hRight)
  | iff left right ihLeft ihRight =>
      simp [canonical_project_hilbert_trace_from?] at hTrace
  | forallE sort body ih =>
      cases sort
      simp only [canonical_project_hilbert_trace_from?] at hTrace
      cases hBody :
          canonical_project_hilbert_trace_from?
            start (entryDepth + 1) body with
      | none =>
          simp [hBody] at hTrace
      | some bodyTrace =>
          simp [hBody] at hTrace
          subst trace
          exact CanonicalProjectTrace.universal_rows_evidence
            bodyTrace (ih hBody)
            (canonical_project_hilbert_trace_from?_root_bounds hBody)
            (canonical_project_hilbert_trace_from?_root_code_getElem_local
              hBody)
            (canonical_project_hilbert_trace_from?_root_depth_getElem_local
              hBody)
  | existsE sort body ih =>
      simp [canonical_project_hilbert_trace_from?] at hTrace

/-- 第零行编译器生成的每一行都带有真实前驱行证据。 -/
theorem canonical_project_hilbert_trace?_rows_evidence
    {entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace}
    (hTrace :
      canonical_project_hilbert_trace?
        entryDepth formula = some trace) :
    trace.RowsEvidenceFrom 0 :=
  canonical_project_hilbert_trace_from?_rows_evidence hTrace

/-- 第零行编译器生成的公式码对象列表非空。 -/
theorem canonical_project_hilbert_trace?_code_terms_nonempty
    {entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace?
        entryDepth formula = some trace) :
    trace.code_terms ≠ [] := by
  rcases canonical_project_hilbert_trace_from?_terminal_terms hTrace with
    ⟨codePrefix, _, hCodes, _⟩
  rw [hCodes]
  simp
/-- 第零行编译器生成的入口深度对象列表非空。 -/
theorem canonical_project_hilbert_trace?_depth_terms_nonempty
    {entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace?
        entryDepth formula = some trace) :
    trace.depth_terms ≠ [] := by
  rcases canonical_project_hilbert_trace_from?_terminal_terms hTrace with
    ⟨_, depthPrefix, _, hDepths⟩
  rw [hDepths]
  simp
/-- 根公式码在公式码列表的最后位置精确读回。 -/
theorem canonical_project_hilbert_trace?_root_code_getElem?
    {entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace?
        entryDepth formula = some trace) :
    trace.code_terms[trace.rootIndex]? =
      some trace.rootCode := by
  rcases canonical_project_hilbert_trace_from?_terminal_terms hTrace with
    ⟨codePrefix, _, hCodes, _⟩
  have hRoot :
      trace.rootIndex + 1 = trace.rows.length :=
    canonical_project_hilbert_trace?_root_index hTrace
  have hTermsLength :
      trace.code_terms.length = trace.rows.length := by
    simp [CanonicalProjectTrace.code_terms]
  have hRootIndex : trace.rootIndex = codePrefix.length := by
    rw [hCodes] at hTermsLength
    simp only [List.length_append, List.length_singleton] at hTermsLength
    omega
  rw [hCodes, hRootIndex]
  simp
/-- 根入口深度在深度列表的最后位置精确读回。 -/
theorem canonical_project_hilbert_trace?_root_depth_getElem?
    {entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace?
        entryDepth formula = some trace) :
    trace.depth_terms[trace.rootIndex]? =
      some numₘ(entryDepth) := by
  rcases canonical_project_hilbert_trace_from?_terminal_terms hTrace with
    ⟨_, depthPrefix, _, hDepths⟩
  have hRoot :
      trace.rootIndex + 1 = trace.rows.length :=
    canonical_project_hilbert_trace?_root_index hTrace
  have hTermsLength :
      trace.depth_terms.length = trace.rows.length := by
    simp [CanonicalProjectTrace.depth_terms]
  have hRootIndex : trace.rootIndex = depthPrefix.length := by
    rw [hDepths] at hTermsLength
    simp only [List.length_append, List.length_singleton] at hTermsLength
    omega
  rw [hDepths, hRootIndex]
  simp
/-- 轨迹行的 quotation 结果具有统一对象项边界。 -/
theorem canonical_project_hilbert_trace_from?_row_code_boundary
    {start entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace_from?
        start entryDepth formula = some trace)
    {row : CanonicalProjectTraceRow} (hRow : row ∈ trace.rows) :
    GodelQuotation.Numbered.CodeBoundary row.code := by
  exact GodelQuotation.Numbered.quote_hilbert_with?_code_boundary
    GodelQuotation.free_name
    GodelQuotation.bound_name ((canonical_project_hilbert_trace_from?_rows_quoted
      hTrace) row hRow)
/-- 轨迹中的每个公式码都属于对象集合 `FormulaCodeₘ`。 -/
theorem canonical_project_hilbert_trace_from?_row_formula_code_mem
    {start entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace_from?
        start entryDepth formula = some trace)
    {row : CanonicalProjectTraceRow} (hRow : row ∈ trace.rows) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      row.code ∈ₘ FormulaCodeₘ := by
  exact GodelQuotation.Numbered.quote_hilbert_with?_formula_code_mem
    GodelQuotation.free_name
    GodelQuotation.bound_name ((canonical_project_hilbert_trace_from?_rows_quoted
      hTrace) row hRow)
/-- 轨迹公式码列表的每一项都满足对象项 admissibility。 -/
theorem canonical_project_hilbert_trace_from?_code_terms_admissible
    {start entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace_from?
        start entryDepth formula = some trace) :
    ∀ code, code ∈ trace.code_terms →
      Term.Admissible code SetSort.set := by
  intro code hCode
  rcases List.mem_map.mp hCode with ⟨row, hRow, rfl⟩
  exact (canonical_project_hilbert_trace_from?_row_code_boundary
      hTrace hRow).1
/-- 轨迹公式码列表的每一项都是闭项。 -/
theorem canonical_project_hilbert_trace_from?_code_terms_closed
    {start entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace_from?
        start entryDepth formula = some trace) :
    ∀ code, code ∈ trace.code_terms →
      Term.freeSupport code = [] := by
  intro code hCode
  rcases List.mem_map.mp hCode with ⟨row, hRow, rfl⟩
  exact (canonical_project_hilbert_trace_from?_row_code_boundary
      hTrace hRow).2
/-- 任意轨迹入口深度列表的每一项都满足对象项 admissibility。 -/
theorem canonical_project_trace_depth_terms_admissible (trace : CanonicalProjectTrace) :
    ∀ depth, depth ∈ trace.depth_terms →
      Term.Admissible depth SetSort.set := by
  intro depth hDepth
  rcases List.mem_map.mp hDepth with ⟨row, _, rfl⟩
  exact finite_numeral_term_admissible row.depth
/-- 任意轨迹入口深度列表的每一项都是闭项。 -/
theorem canonical_project_trace_depth_terms_closed (trace : CanonicalProjectTrace) :
    ∀ depth, depth ∈ trace.depth_terms →
      Term.freeSupport depth = [] := by
  intro depth hDepth
  rcases List.mem_map.mp hDepth with ⟨row, _, rfl⟩
  exact finite_numeral_term_freeSupport row.depth
/-! ## 两条标准对象序列 -/
/-- 成功轨迹的根公式码属于完整公式编码集合。 -/
theorem canonical_project_hilbert_trace_from?_root_formula_code_mem
    {start entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace_from?
        start entryDepth formula = some trace) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      trace.rootCode ∈ₘ FormulaCodeₘ := by
  exact GodelQuotation.Numbered.quote_hilbert_with?_formula_code_mem
    GodelQuotation.free_name
    GodelQuotation.bound_name (canonical_project_hilbert_trace_from?_root_quote hTrace)
/-- 成功轨迹的根公式码具有统一对象项边界。 -/
theorem canonical_project_hilbert_trace_from?_root_code_boundary
    {start entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace_from?
        start entryDepth formula = some trace) :
    GodelQuotation.Numbered.CodeBoundary trace.rootCode := by
  exact GodelQuotation.Numbered.quote_hilbert_with?_code_boundary
    GodelQuotation.free_name
    GodelQuotation.bound_name (canonical_project_hilbert_trace_from?_root_quote hTrace)
/--
成功轨迹自身提供 `FormulaCodeₘ` 的非空见证。
这避免 quotation 轨迹反向依赖证明码模块中更晚建立的固定等式见证。
-/
theorem canonical_project_hilbert_trace_from?_formula_code_nonempty
    {start entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace_from?
        start entryDepth formula = some trace) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      FormulaCodeₘ ≠ₘ ∅ₘ := by
  have hImp :
      ⊢ₘ[GodelQuotation.godel_quotation_theory] (trace.rootCode ∈ₘ FormulaCodeₘ) ⟶ₘ (FormulaCodeₘ ≠ₘ ∅ₘ) := by
    apply GodelQuotation.gq_weaken_standard_sequence
    exact FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hFormula))))) (member_implies_set_nonempty
        trace.rootCode FormulaCodeₘ (canonical_project_hilbert_trace_from?_root_code_boundary
          hTrace).1
        formula_code_set_term_admissible)
  exact FirstOrder.Derives.impElim hImp (canonical_project_hilbert_trace_from?_root_formula_code_mem
      hTrace)
/-- 轨迹公式码的标准序列属于非空公式码序列空间。 -/
theorem canonical_project_hilbert_trace?_code_sequence_mem
    {entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace?
        entryDepth formula = some trace) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      trace.code_sequence ∈ₘ
        seq₊_spaceₘ(FormulaCodeₘ) := by
  simpa [CanonicalProjectTrace.code_sequence] using (GodelQuotation.standard_sequence_mem_nonempty_sequence_space_of_theory
      (T := GodelQuotation.godel_quotation_theory) (fun _ hFormula => Or.inl hFormula) (fun _ hFormula =>
        GodelQuotation.godel_quotation_theory_sentence hFormula)
      FormulaCodeₘ (canonical_project_hilbert_trace_from?_code_terms_admissible
        hTrace) (canonical_project_hilbert_trace_from?_code_terms_closed
        hTrace)
      formula_code_set_term_admissible (by native_decide) (canonical_project_hilbert_trace_from?_formula_code_nonempty
        hTrace) (by
        intro code hCode
        rcases List.mem_map.mp hCode with ⟨row, hRow, rfl⟩
        exact
          canonical_project_hilbert_trace_from?_row_formula_code_mem
            hTrace hRow) (canonical_project_hilbert_trace?_code_terms_nonempty
        hTrace))
/-- 轨迹入口深度的标准序列属于非空自然数序列空间。 -/
theorem canonical_project_hilbert_trace?_depth_sequence_mem
    {entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace?
        entryDepth formula = some trace) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      trace.depth_sequence ∈ₘ
        seq₊_spaceₘ(ωₘ) := by
  simpa [CanonicalProjectTrace.depth_sequence] using (GodelQuotation.standard_sequence_mem_nonempty_sequence_space_of_theory
      (T := GodelQuotation.godel_quotation_theory) (fun _ hFormula => Or.inl hFormula) (fun _ hFormula =>
        GodelQuotation.godel_quotation_theory_sentence hFormula)
      ωₘ (canonical_project_trace_depth_terms_admissible trace) (canonical_project_trace_depth_terms_closed trace)
      omega_term_admissible
      rfl (GodelQuotation.gq_weaken_standard_sequence
        GodelQuotation.standard_sequence_omega_ne_empty) (by
        intro depth hDepth
        rcases List.mem_map.mp hDepth with ⟨row, _, rfl⟩
        exact GodelQuotation.gq_weaken_standard_sequence (GodelQuotation.standard_sequence_finite_numeral_mem_omega
            row.depth)) (canonical_project_hilbert_trace?_depth_terms_nonempty
        hTrace))
/-- 轨迹公式码标准序列的定义域等于轨迹行数 numeral。 -/
theorem canonical_project_hilbert_trace?_code_sequence_domain
    {entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace?
        entryDepth formula = some trace) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      domₘ(trace.code_sequence) ≐ₘ
        numₘ(trace.rows.length) := by
  apply GodelQuotation.gq_weaken_standard_sequence
  simpa [CanonicalProjectTrace.code_sequence,
    CanonicalProjectTrace.code_terms] using (GodelQuotation.standard_sequence_domain_eq_numeral_length
      (canonical_project_hilbert_trace_from?_code_terms_admissible
        hTrace) (GodelQuotation.stdseq_element_fresh_of_support_nil
          (canonical_project_hilbert_trace_from?_code_terms_closed
            hTrace) 0)
        (GodelQuotation.stdseq_element_fresh_of_support_nil
          (canonical_project_hilbert_trace_from?_code_terms_closed
            hTrace) 1))
/-- 轨迹入口深度标准序列的定义域等于轨迹行数 numeral。 -/
theorem canonical_project_trace_depth_sequence_domain (trace : CanonicalProjectTrace) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      domₘ(trace.depth_sequence) ≐ₘ
        numₘ(trace.rows.length) := by
  apply GodelQuotation.gq_weaken_standard_sequence
  simpa [CanonicalProjectTrace.depth_sequence,
    CanonicalProjectTrace.depth_terms] using (GodelQuotation.standard_sequence_domain_eq_numeral_length (canonical_project_trace_depth_terms_admissible trace)
      (GodelQuotation.stdseq_element_fresh_of_support_nil
        (canonical_project_trace_depth_terms_closed trace) 0)
      (GodelQuotation.stdseq_element_fresh_of_support_nil
        (canonical_project_trace_depth_terms_closed trace) 1))
/-- 成功轨迹的公式码标准序列满足对象项边界。 -/
theorem canonical_project_hilbert_trace_from?_code_sequence_boundary
    {start entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace_from?
        start entryDepth formula = some trace) :
    GodelQuotation.Numbered.CodeBoundary trace.code_sequence := by
  constructor
  · exact GodelQuotation.seq_admissible_m 0 (canonical_project_hilbert_trace_from?_code_terms_admissible
        hTrace)
  · exact GodelQuotation.seq_support_nil_m 0 (canonical_project_hilbert_trace_from?_code_terms_closed
        hTrace)
/-- 任意轨迹的入口深度标准序列满足对象项边界。 -/
theorem canonical_project_trace_depth_sequence_boundary (trace : CanonicalProjectTrace) :
    GodelQuotation.Numbered.CodeBoundary trace.depth_sequence := by
  constructor
  · exact GodelQuotation.seq_admissible_m 0 (canonical_project_trace_depth_terms_admissible trace)
  · exact GodelQuotation.seq_support_nil_m 0 (canonical_project_trace_depth_terms_closed trace)
/-- 根行编号属于公式码标准序列的定义域。 -/
theorem canonical_project_hilbert_trace?_root_index_mem_domain
    {entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace?
        entryDepth formula = some trace) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      numₘ(trace.rootIndex) ∈ₘ
        domₘ(trace.code_sequence) := by
  have hRoot :
      trace.rootIndex < trace.rows.length := by
    have hRootIndex :=
      canonical_project_hilbert_trace?_root_index hTrace
    omega
  have hNumeral :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        numₘ(trace.rootIndex) ∈ₘ
          numₘ(trace.rows.length) :=
    GodelQuotation.gq_weaken_standard_sequence (GodelQuotation.standard_sequence_finite_numeral_mem_of_lt
        trace.rootIndex trace.rows.length hRoot)
  have hSequence :
      Term.Admissible trace.code_sequence SetSort.set := (canonical_project_hilbert_trace_from?_code_sequence_boundary
      hTrace).1
  have hTransport := membership_right_iff_of_equality (numₘ(trace.rootIndex)) (domₘ(trace.code_sequence)) (numₘ(trace.rows.length))
    (finite_numeral_term_admissible trace.rootIndex) (domain_term_admissible trace.code_sequence hSequence) (finite_numeral_term_admissible trace.rows.length)
    (canonical_project_hilbert_trace?_code_sequence_domain
      hTrace)
  exact FirstOrder.Derives.iffElimLeft
    hTransport hNumeral
/-- 公式码标准序列的定义域是根行编号的对象后继。 -/
theorem canonical_project_hilbert_trace?_domain_eq_root_successor
    {entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace?
        entryDepth formula = some trace) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      domₘ(trace.code_sequence) ≐ₘ
        Sₘ(numₘ(trace.rootIndex)) := by
  have hRoot :
      trace.rows.length = trace.rootIndex + 1 := by
    have hRootIndex :=
      canonical_project_hilbert_trace?_root_index hTrace
    omega
  simpa [hRoot, finite_numeral_term] using (canonical_project_hilbert_trace?_code_sequence_domain
      hTrace)
/-- 公式码标准序列在根行编号处求值为根公式码。 -/
theorem canonical_project_hilbert_trace?_root_code_value
    {entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace?
        entryDepth formula = some trace) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory] (trace.code_sequence ·ₘ
        numₘ(trace.rootIndex)) ≐ₘ
          trace.rootCode := by
  apply GodelQuotation.gq_weaken_standard_sequence
  simpa [CanonicalProjectTrace.code_sequence] using (GodelQuotation.standard_sequence_from_apply_getElem?
      0 (canonical_project_hilbert_trace?_root_code_getElem?
        hTrace) (canonical_project_hilbert_trace_from?_code_terms_admissible
        hTrace) (canonical_project_hilbert_trace_from?_code_terms_closed
        hTrace) (canonical_project_hilbert_trace_from?_root_code_boundary
        hTrace).1)
/-- 入口深度标准序列在根行编号处求值为入口深度 numeral。 -/
theorem canonical_project_hilbert_trace?_root_depth_value
    {entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace?
        entryDepth formula = some trace) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory] (trace.depth_sequence ·ₘ
        numₘ(trace.rootIndex)) ≐ₘ
          numₘ(entryDepth) := by
  apply GodelQuotation.gq_weaken_standard_sequence
  simpa [CanonicalProjectTrace.depth_sequence] using (GodelQuotation.standard_sequence_from_apply_getElem?
      0 (canonical_project_hilbert_trace?_root_depth_getElem?
        hTrace) (canonical_project_trace_depth_terms_admissible trace) (canonical_project_trace_depth_terms_closed trace)
      (finite_numeral_term_admissible entryDepth))
/-- 两条标准序列具有完全相同的对象定义域。 -/
theorem canonical_project_hilbert_trace?_sequence_domains_eq
    {entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace?
        entryDepth formula = some trace) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      domₘ(trace.code_sequence) ≐ₘ
        domₘ(trace.depth_sequence) := by
  have hCodeDomain :=
    canonical_project_hilbert_trace?_code_sequence_domain hTrace
  have hDepthDomain :=
    canonical_project_trace_depth_sequence_domain trace
  have hDepthSymm :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        numₘ(trace.rows.length) ≐ₘ
          domₘ(trace.depth_sequence) :=
    Metatheory.Derives.equality_symm
      hDepthDomain
  exact Metatheory.Derives.equality_trans (middle := numₘ(trace.rows.length))
    hCodeDomain hDepthSymm
/-- 非空标准轨迹的第零编号属于公式码序列定义域。 -/
theorem canonical_project_hilbert_trace?_zero_mem_domain
    {entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace?
        entryDepth formula = some trace) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      numₘ(0) ∈ₘ domₘ(trace.code_sequence) := by
  have hLengthPositive : 0 < trace.rows.length := by
    have hTermsNonempty :=
      canonical_project_hilbert_trace?_code_terms_nonempty hTrace
    cases hRows : trace.rows with
    | nil =>
        simp [CanonicalProjectTrace.code_terms, hRows] at hTermsNonempty
    | cons row rows =>
        simp
  have hNumeral :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        numₘ(0) ∈ₘ numₘ(trace.rows.length) :=
    GodelQuotation.gq_weaken_standard_sequence (GodelQuotation.standard_sequence_finite_numeral_mem_of_lt
        0 trace.rows.length hLengthPositive)
  have hSequence :
      Term.Admissible trace.code_sequence SetSort.set := (canonical_project_hilbert_trace_from?_code_sequence_boundary
      hTrace).1
  have hTransport := membership_right_iff_of_equality (numₘ(0)) (domₘ(trace.code_sequence)) (numₘ(trace.rows.length)) (finite_numeral_term_admissible 0)
    (domain_term_admissible trace.code_sequence hSequence) (finite_numeral_term_admissible trace.rows.length)
    (canonical_project_hilbert_trace?_code_sequence_domain
      hTrace)
  exact FirstOrder.Derives.iffElimLeft
    hTransport hNumeral
/--
根行提供普通规范分类器所需的末行合同，且不再依赖 `maxεₘ` 的有限最大元推理。
-/
theorem canonical_project_hilbert_trace?_terminal_contract
    {entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace?
        entryDepth formula = some trace) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      canonical_project_formula_terminal_condition (numₘ(entryDepth)) trace.rootCode
        trace.code_sequence trace.depth_sequence (numₘ(trace.rootIndex)) := by
  have hCodeValueSymm :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        trace.rootCode ≐ₘ (trace.code_sequence ·ₘ
            numₘ(trace.rootIndex)) :=
    Metatheory.Derives.equality_symm
      (canonical_project_hilbert_trace?_root_code_value
        hTrace)
  have hDepthValueSymm :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        numₘ(entryDepth) ≐ₘ (trace.depth_sequence ·ₘ
            numₘ(trace.rootIndex)) :=
    Metatheory.Derives.equality_symm
      (canonical_project_hilbert_trace?_root_depth_value
        hTrace)
  simpa [canonical_project_formula_terminal_condition] using (FirstOrder.Derives.conjIntro (FirstOrder.Derives.conjIntro
        (canonical_project_hilbert_trace?_root_index_mem_domain
          hTrace) (canonical_project_hilbert_trace?_domain_eq_root_successor
          hTrace)) (FirstOrder.Derives.conjIntro
        hCodeValueSymm hDepthValueSymm))
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
