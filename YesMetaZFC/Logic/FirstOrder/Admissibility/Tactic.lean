import YesMetaZFC.Logic.FirstOrder.Admissibility

/-!
# 合法性计算证书 tactic

本模块把局部定义的 zeta 归约、项目级证书 simp 集与纯函数归约统一封装起来，
使自然演绎规则的默认参数无需显式传递合法性证明。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder

universe u v w

namespace Term

/-- 函数实参列表逐位置携带纯函数合法性证书。 -/
inductive ArgsCheckCertificate
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] :
    List (Term σ) → List σ.SortSymbol → Prop
  | nil : ArgsCheckCertificate [] []
  | cons
      {term : Term σ} {terms : List (Term σ)}
      {sort : σ.SortSymbol} {sorts : List σ.SortSymbol}
      (hTerm : CheckCertificate term sort)
      (hTerms : ArgsCheckCertificate terms sorts) :
      ArgsCheckCertificate (term :: terms) (sort :: sorts)

namespace ArgsCheckCertificate

/-- 参数计算证书恢复原有逐位置 admissibility。 -/
theorem admissible
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {arguments : List (Term σ)}
    {sorts : List σ.SortSymbol}
    (hArguments :
      ArgsCheckCertificate arguments sorts) :
    ArgsAdmissible arguments sorts := by
  induction hArguments with
  | nil =>
      exact ArgsAdmissible.nil
  | cons hTerm _ ih =>
      exact ArgsAdmissible.cons
        hTerm.admissible ih

end ArgsCheckCertificate

namespace CheckCertificate

/-- 原始函数应用由逐参数计算证书直接合成。 -/
theorem app
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    (function : σ.FuncSymbol)
    {arguments : List (Term σ)}
    (hArguments :
      ArgsCheckCertificate arguments
        (σ.funcDomain function)) :
    CheckCertificate (.app function arguments)
      (σ.funcCodomain function) := by
  have hArgs := hArguments.admissible
  exact check_admissible_complete
    ⟨TermWellSorted.app function hArgs.1,
      TermScoped.app function arguments hArgs.2⟩

end CheckCertificate
end Term

namespace Formula

/--
等式节点不携带 sort；统一自动化以左项的可计算 sort 作为唯一目标，
并要求右项通过同一 sort 的检查。
-/
theorem CheckCertificate.equal_inferred
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {left right : Term σ}
    (hLeft :
      Term.CheckCertificate left
        (Term.inferredSort left))
    (hRight :
      Term.CheckCertificate right
        (Term.inferredSort left)) :
    CheckCertificate (.equal left right) :=
  CheckCertificate.equal hLeft hRight

/-- 等式公式证书精确反演为左右项在左项推断 sort 下的检查证书。 -/
@[formula_check]
theorem CheckCertificate.equal_iff
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {left right : Term σ} :
    CheckCertificate (.equal left right) ↔
      Term.CheckCertificate left (Term.inferredSort left) ∧
        Term.CheckCertificate right (Term.inferredSort left) := by
  simp only [CheckCertificate, Formula.check_admissible,
    Formula.check_wellFormed, Formula.check_scoped,
    Term.CheckCertificate, Term.check_admissible,
    Bool.and_eq_true_iff]
  constructor
  · rintro ⟨⟨hLeftSort, hRightSort⟩,
      hLeftScoped, hRightScoped⟩
    exact
      ⟨⟨hLeftSort, hLeftScoped⟩,
        ⟨hRightSort, hRightScoped⟩⟩
  · rintro ⟨⟨hLeftSort, hLeftScoped⟩,
      ⟨hRightSort, hRightScoped⟩⟩
    exact
      ⟨⟨hLeftSort, hRightSort⟩,
        hLeftScoped, hRightScoped⟩

/-- 关系原子由逐位置参数计算证书直接合成。 -/
theorem CheckCertificate.rel
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {relation : σ.RelSymbol}
    {arguments : List (Term σ)}
    (hArguments :
      Term.ArgsCheckCertificate arguments
        (σ.relDomain relation)) :
    CheckCertificate (.rel relation arguments) :=
  check_admissible_complete <|
    Admissible.rel hArguments.admissible

/-- 否定证书归约为内部公式证书。 -/
@[formula_check]
theorem CheckCertificate.neg_iff
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {formula : Formula σ} :
    CheckCertificate (.neg formula) ↔
      CheckCertificate formula :=
  ⟨fun hFormula =>
      check_admissible_complete <|
        Admissible.neg_body hFormula.admissible,
    CheckCertificate.neg⟩

/-- 合取证书归约为左右子公式证书。 -/
@[formula_check]
theorem CheckCertificate.conj_iff
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {left right : Formula σ} :
    CheckCertificate (.conj left right) ↔
      CheckCertificate left ∧ CheckCertificate right :=
  ⟨fun hConj =>
      ⟨check_admissible_complete <|
          Admissible.conj_left hConj.admissible,
        check_admissible_complete <|
          Admissible.conj_right hConj.admissible⟩,
    fun h => CheckCertificate.conj h.1 h.2⟩

/-- 析取证书归约为左右子公式证书。 -/
@[formula_check]
theorem CheckCertificate.disj_iff
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {left right : Formula σ} :
    CheckCertificate (.disj left right) ↔
      CheckCertificate left ∧ CheckCertificate right :=
  ⟨fun hDisj =>
      ⟨check_admissible_complete <|
          Admissible.disj_left hDisj.admissible,
        check_admissible_complete <|
          Admissible.disj_right hDisj.admissible⟩,
    fun h => CheckCertificate.disj h.1 h.2⟩

/-- 蕴含证书归约为前件与后件证书。 -/
@[formula_check]
theorem CheckCertificate.imp_iff
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {antecedent consequent : Formula σ} :
    CheckCertificate (.imp antecedent consequent) ↔
      CheckCertificate antecedent ∧
        CheckCertificate consequent :=
  ⟨fun hImp =>
      ⟨check_admissible_complete <|
          Admissible.imp_left hImp.admissible,
        check_admissible_complete <|
          Admissible.imp_right hImp.admissible⟩,
    fun h => CheckCertificate.imp h.1 h.2⟩

/-- 双条件证书归约为左右子公式证书。 -/
@[formula_check]
theorem CheckCertificate.iff_iff
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {left right : Formula σ} :
    CheckCertificate (.iff left right) ↔
      CheckCertificate left ∧ CheckCertificate right :=
  ⟨fun hIff =>
      ⟨check_admissible_complete <|
          Admissible.iff_left hIff.admissible,
        check_admissible_complete <|
          Admissible.iff_right hIff.admissible⟩,
    fun h => CheckCertificate.iff h.1 h.2⟩

/-- 关闭自由变量并加入全称量词保持计算证书。 -/
@[formula_check]
theorem CheckCertificate.forall_closeFreeAt
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {formula : Formula σ}
    (target : σ.SortSymbol) (id : FreeVarId)
    (hFormula : CheckCertificate formula) :
    CheckCertificate
      (Formula.forallE target
        (Formula.closeFreeAt target id 0 formula)) :=
  check_admissible_complete <|
    Admissible.forall_closeFreeAt
      target id hFormula.admissible

/-- 关闭自由变量并加入存在量词保持计算证书。 -/
@[formula_check]
theorem CheckCertificate.exists_closeFreeAt
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {formula : Formula σ}
    (target : σ.SortSymbol) (id : FreeVarId)
    (hFormula : CheckCertificate formula) :
    CheckCertificate
      (Formula.existsE target
        (Formula.closeFreeAt target id 0 formula)) :=
  check_admissible_complete <|
    Admissible.exists_closeFreeAt
      target id hFormula.admissible

/--
项目项证书规则的前提只在叶子处读取已有 admissibility。
对函数型前提先引入参数，再由局部假设完成转换，避免把转换定理加入全局 simp 搜索。
-/
macro "prove_term_check_leaf" : tactic =>
  `(tactic|
    solve
    | assumption
    | (repeat' intro
       apply Term.check_admissible_complete
       solve_by_elim))

/-- 不产生递归子目标的项证书叶规则。 -/
macro "prove_term_check_head" : tactic =>
  `(tactic|
    solve
    | exact (show Term.CheckCertificate _ _ from by assumption)
    | exact Term.check_admissible_complete (by assumption)
    | (apply Term.check_admissible_complete
       apply_assumption <;> simp)
    | exact Term.check_admissible_complete
        ⟨by assumption, by assumption⟩
    | (intro
       repeat' intro
       apply Term.check_admissible_complete
       solve_by_elim)
    | exact Term.CheckCertificate.fvar _ _
    | (solve
        | simp (config := { zetaDelta := true })
            (disch := prove_term_check_leaf) only
            [term_check])
    | (solve
        | simp (config := { zetaDelta := true }) only
            [Term.CheckCertificate, term_check])
    )

/-- 叶规则与应用分解均失败后才启用的证明层回退。 -/
macro "prove_term_check_fallback" : tactic =>
  `(tactic|
    solve
    | (solve
        | simp (config := { zetaDelta := true })
            (disch := prove_term_check_leaf) only
            [Term.CheckCertificate, term_check])
    | apply Term.check_admissible_complete <;> prove_term_admissible
    | native_decide)

/--
项证书的统一入口。函数应用先拆成逐参数证书，避免底层 Bool 归约越过
项目级 `[term_check]` 规则。
-/
macro "prove_term_check" : tactic =>
  `(tactic|
    solve
    | (repeat'
        first
        | exact Term.ArgsCheckCertificate.nil
        | apply Term.ArgsCheckCertificate.cons
        | prove_term_check_head
        | apply Term.CheckCertificate.app
        | prove_term_check_fallback))

/-- 递归组合公式结构，原子与项目定义公式交给证书 simp 集。 -/
macro "prove_formula_check_structural" : tactic =>
  `(tactic|
    solve
    | (repeat'
        first
        | exact (show Formula.CheckCertificate _ from by assumption)
        | exact Formula.check_admissible_complete (by assumption)
        | exact Formula.check_admissible_complete
            Formula.Admissible.falsum
        | exact Formula.check_admissible_complete
            Formula.Admissible.truth
        | (with_reducible_and_instances
            apply Formula.CheckCertificate.rel)
        | (with_reducible_and_instances
            apply Formula.CheckCertificate.equal_inferred)
        | (with_reducible_and_instances
            apply Formula.CheckCertificate.neg)
        | (with_reducible_and_instances
            apply Formula.CheckCertificate.conj)
        | (with_reducible_and_instances
            apply Formula.CheckCertificate.disj)
        | (with_reducible_and_instances
            apply Formula.CheckCertificate.imp)
        | (with_reducible_and_instances
            apply Formula.CheckCertificate.iff)
        | (with_reducible_and_instances
            apply Formula.CheckCertificate.forall_closeFreeAt)
        | (with_reducible_and_instances
            apply Formula.CheckCertificate.exists_closeFreeAt)
        | exact Term.ArgsCheckCertificate.nil
        | apply Term.ArgsCheckCertificate.cons
        | prove_term_check
        | (solve
            | simp (config := { zetaDelta := true })
                (disch := (first
                  | assumption
                  | prove_term_check))
                only [formula_check])
        | (solve
            | simp (config := { zetaDelta := true })
                (disch := (first
                  | assumption
                  | prove_term_check))
                only [Formula.CheckCertificate, formula_check,
                  true_and, and_true])
        ))

/-- 优先用已有数学前提，否则直接归约纯函数检查。 -/
macro "prove_formula_check_core" : tactic =>
  `(tactic|
    solve
    | prove_formula_check_structural
    | exact (show Formula.CheckCertificate _ from by assumption)
    | exact Formula.check_admissible_complete (by assumption)
    | exact Formula.check_admissible_complete
        Formula.Admissible.falsum
    | exact Formula.check_admissible_complete
        Formula.Admissible.truth
    | (solve
        | simp (config := { zetaDelta := true })
            (disch := (first
              | assumption
              | prove_term_check))
            only [formula_check])
    | (solve
        | simp (config := { zetaDelta := true })
            (disch := (first
              | assumption
              | prove_term_check))
            only [Formula.CheckCertificate, formula_check,
              true_and, and_true])
    | exact Formula.check_admissible_complete
        (Formula.Admissible.equal
          (by prove_term_admissible)
          (by prove_term_admissible))
    | exact Formula.CheckCertificate.conj_equal_of_admissible
        (by assumption) (by assumption)
        (by assumption) (by assumption)
    | exact Formula.check_admissible_complete
        (Formula.Admissible.forall_closeFreeAt _ _
          (by assumption))
    | exact Formula.check_admissible_complete
        (Formula.Admissible.exists_closeFreeAt _ _
          (by assumption))
    | apply Formula.check_admissible_complete
      exact Formula.Admissible.forall_openAt _ (by assumption)
        (by prove_term_admissible)
    | apply Formula.check_admissible_complete
      exact Formula.Admissible.exists_openAt _ (by assumption)
        (by prove_term_admissible)
    | apply Formula.check_admissible_complete <;> prove_admissible
    | native_decide)

/-- 公式计算证书的统一无感入口。 -/
macro "prove_formula_check" : tactic =>
  `(tactic| prove_formula_check_core)

end Formula
end FirstOrder
end Logic
end YesMetaZFC
