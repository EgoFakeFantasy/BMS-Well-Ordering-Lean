import YesMetaZFC.Logic.FirstOrder.Hilbert.Derived
/-!
# 自然演绎公式到内部 Hilbert 片段的归约
内部公式编码只以原子式、等式、否定、蕴含和全称量词为构造子。本模块把公共
`Formula` 的真、假、合取、析取、双条件与存在量词统一归约到该片段。
假命题取为一个闭真式的否定；闭真式使用 `∀x, x = x`，因此不会向翻译结果引入
新的自由变量。这个选择使全称引入的新鲜条件可以原样穿过翻译。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
universe u v w
namespace Formula
/-- 只用内部 Hilbert 构造子的闭真式。 -/
def hilbert_truth {σ : Signature.{u, v, w}} (anchorSort : σ.SortSymbol) : Formula σ :=
  Formula.forallE anchorSort (Formula.equal (Term.var (.bvar anchorSort 0)) (Term.var (.bvar anchorSort 0)))
/-- 内部 Hilbert 假式定义为闭真式的否定。 -/
def hilbert_falsum {σ : Signature.{u, v, w}} (anchorSort : σ.SortSymbol) : Formula σ :=
  Formula.neg (hilbert_truth anchorSort)
/-- Hilbert 编码合取 `¬(φ → ¬ψ)`。 -/
def hilbert_conj {σ : Signature.{u, v, w}} (left right : Formula σ) : Formula σ :=
  Formula.neg (Formula.imp left (Formula.neg right))
/-- Hilbert 编码双条件：两个方向蕴含的编码合取。 -/
def hilbert_iff {σ : Signature.{u, v, w}} (left right : Formula σ) : Formula σ :=
  hilbert_conj (Formula.imp left right) (Formula.imp right left)
namespace Admissible
/-- Hilbert 归约选取的闭真式是 admissible 公式。 -/
theorem hilbert_truth {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (anchorSort : σ.SortSymbol) :
    Formula.Admissible (Formula.hilbert_truth anchorSort) := by
  let eigen : FreeVarId := 0
  have hEquality :
      Formula.Admissible (Formula.equal (Term.var (.fvar anchorSort eigen)) (Term.var (.fvar anchorSort eigen))) :=
    ⟨.equal (TermWellSorted.fvar anchorSort eigen) (TermWellSorted.fvar anchorSort eigen),
      .equal (TermScoped.fvar anchorSort eigen) (TermScoped.fvar anchorSort eigen)⟩
  simpa [Formula.hilbert_truth, Formula.closeFreeAt,
    Term.closeFreeAt] using (Formula.Admissible.forall_closeFreeAt
      anchorSort eigen hEquality)
/-- Hilbert 归约选取的闭假式是 admissible 公式。 -/
theorem hilbert_falsum {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (anchorSort : σ.SortSymbol) :
    Formula.Admissible (Formula.hilbert_falsum anchorSort) :=
  Formula.Admissible.neg (Formula.Admissible.hilbert_truth anchorSort)
/-- 两个 admissible 公式组成 admissible 的 Hilbert 编码合取。 -/
theorem hilbert_conj {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {left right : Formula σ} (hLeft : Formula.Admissible left) (hRight : Formula.Admissible right) :
    Formula.Admissible (Formula.hilbert_conj left right) :=
  Formula.Admissible.neg (Formula.Admissible.imp hLeft (Formula.Admissible.neg hRight))
/-- Hilbert 编码合取 admissible 时，其左侧公式 admissible。 -/
theorem hilbert_conj_left {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {left right : Formula σ} (hConjunction :
      Formula.Admissible (Formula.hilbert_conj left right)) :
    Formula.Admissible left := by
  exact Formula.Admissible.imp_left <|
    Formula.Admissible.neg_body <| by
      simpa [Formula.hilbert_conj] using hConjunction
/-- Hilbert 编码合取 admissible 时，其右侧公式 admissible。 -/
theorem hilbert_conj_right {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {left right : Formula σ} (hConjunction :
      Formula.Admissible (Formula.hilbert_conj left right)) :
    Formula.Admissible right := by
  have hNegRight :
      Formula.Admissible (Formula.neg right) :=
    Formula.Admissible.imp_right <|
      Formula.Admissible.neg_body <| by
        simpa [Formula.hilbert_conj] using hConjunction
  exact Formula.Admissible.neg_body hNegRight
/-- 两个 admissible 公式组成 admissible 的 Hilbert 编码双条件。 -/
theorem hilbert_iff {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {left right : Formula σ} (hLeft : Formula.Admissible left) (hRight : Formula.Admissible right) :
    Formula.Admissible (Formula.hilbert_iff left right) :=
  Formula.Admissible.hilbert_conj (Formula.Admissible.imp hLeft hRight) (Formula.Admissible.imp hRight hLeft)
/-- admissible 存在公式的 `¬∀¬` Hilbert 编码仍然 admissible。 -/
theorem hilbert_exists {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {sort : σ.SortSymbol}
    {body : Formula σ} (hExistential :
      Formula.Admissible (Formula.existsE sort body)) :
    Formula.Admissible (Formula.neg (Formula.forallE sort (Formula.neg body))) := by
  rcases hExistential with ⟨hWellFormed, hScoped⟩
  cases hWellFormed with
  | existsE _ hBodyWellFormed =>
      cases hScoped with
      | existsE _ hBodyScoped =>
          exact
            ⟨.neg (.forallE sort (.neg hBodyWellFormed)),
              .neg (.forallE sort (.neg hBodyScoped))⟩
/-- admissible 的 `¬∀¬` 编码可反演出原存在公式 admissibility。 -/
theorem hilbert_exists_source {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {sort : σ.SortSymbol}
    {body : Formula σ} (hEncoded :
      Formula.Admissible (Formula.neg (Formula.forallE sort (Formula.neg body)))) :
    Formula.Admissible (Formula.existsE sort body) := by
  rcases hEncoded with ⟨hWellFormed, hScoped⟩
  cases hWellFormed with
  | neg hForallWellFormed =>
      cases hForallWellFormed with
      | forallE _ hNegWellFormed =>
          cases hNegWellFormed with
          | neg hBodyWellFormed =>
              cases hScoped with
              | neg hForallScoped =>
                  cases hForallScoped with
                  | forallE _ hNegScoped =>
                      cases hNegScoped with
                      | neg hBodyScoped =>
                          exact
                            ⟨.existsE sort hBodyWellFormed,
                              .existsE sort hBodyScoped⟩
end Admissible
/-- 把公共公式归约到 `¬/→/∀/=/原子` Hilbert 片段。 -/
def hilbertize {σ : Signature.{u, v, w}} (anchorSort : σ.SortSymbol) : Formula σ → Formula σ
  | .falsum => hilbert_falsum anchorSort
  | .truth => hilbert_truth anchorSort
  | .rel relation arguments => .rel relation arguments
  | .equal left right => .equal left right
  | .neg body => .neg (hilbertize anchorSort body)
  | .conj left right =>
      hilbert_conj (hilbertize anchorSort left) (hilbertize anchorSort right)
  | .disj left right =>
      .imp (.neg (hilbertize anchorSort left)) (hilbertize anchorSort right)
  | .imp antecedent consequent =>
      .imp (hilbertize anchorSort antecedent) (hilbertize anchorSort consequent)
  | .iff left right =>
      hilbert_iff (hilbertize anchorSort left) (hilbertize anchorSort right)
  | .forallE sort body =>
      .forallE sort (hilbertize anchorSort body)
  | .existsE sort body =>
      .neg (.forallE sort (.neg (hilbertize anchorSort body)))
namespace FormulaWellFormed
/-- Hilbert 归约保持公式的 sort/arity 良构性。 -/
theorem hilbertize {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {anchorSort : σ.SortSymbol}
    {formula : Formula σ} (hFormula : FormulaWellFormed formula) :
    FormulaWellFormed (Formula.hilbertize anchorSort formula) := by
  induction hFormula with
  | falsum =>
      exact (Formula.Admissible.hilbert_falsum anchorSort).1
  | truth =>
      exact (Formula.Admissible.hilbert_truth anchorSort).1
  | rel relation hArguments =>
      exact .rel relation hArguments
  | equal hLeft hRight =>
      exact .equal hLeft hRight
  | neg hBody ih =>
      exact .neg ih
  | conj hLeft hRight ihLeft ihRight =>
      exact .neg <| .imp ihLeft (.neg ihRight)
  | disj hLeft hRight ihLeft ihRight =>
      exact .imp (.neg ihLeft) ihRight
  | imp hLeft hRight ihLeft ihRight =>
      exact .imp ihLeft ihRight
  | iff hLeft hRight ihLeft ihRight =>
      exact .neg <| .imp (.imp ihLeft ihRight) (.neg (.imp ihRight ihLeft))
  | forallE sort hBody ih =>
      exact .forallE sort ih
  | existsE sort hBody ih =>
      exact .neg (.forallE sort (.neg ih))
/-- Hilbert 归约结果良构时，原公式同样良构。 -/
theorem hilbertize_source {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {anchorSort : σ.SortSymbol}
    {formula : Formula σ} (hFormula :
      FormulaWellFormed (Formula.hilbertize anchorSort formula)) :
    FormulaWellFormed formula := by
  induction formula with
  | falsum =>
      exact .falsum
  | truth =>
      exact .truth
  | rel relation arguments =>
      simpa [Formula.hilbertize] using hFormula
  | equal left right =>
      simpa [Formula.hilbertize] using hFormula
  | neg body ih =>
      change
        FormulaWellFormed (Formula.neg (Formula.hilbertize anchorSort body)) at hFormula
      cases hFormula with
      | neg hBody =>
          exact .neg (ih hBody)
  | conj left right ihLeft ihRight =>
      change
        FormulaWellFormed (Formula.neg (Formula.imp (Formula.hilbertize anchorSort left) (Formula.neg (Formula.hilbertize anchorSort right)))) at hFormula
      cases hFormula with
      | neg hImplication =>
          cases hImplication with
          | imp hLeft hNegRight =>
              cases hNegRight with
              | neg hRight =>
                  exact .conj (ihLeft hLeft) (ihRight hRight)
  | disj left right ihLeft ihRight =>
      change
        FormulaWellFormed (Formula.imp (Formula.neg (Formula.hilbertize anchorSort left)) (Formula.hilbertize anchorSort right)) at hFormula
      cases hFormula with
      | imp hNegLeft hRight =>
          cases hNegLeft with
          | neg hLeft =>
              exact .disj (ihLeft hLeft) (ihRight hRight)
  | imp antecedent consequent ihAntecedent ihConsequent =>
      change
        FormulaWellFormed (Formula.imp (Formula.hilbertize anchorSort antecedent) (Formula.hilbertize anchorSort consequent)) at hFormula
      cases hFormula with
      | imp hAntecedent hConsequent =>
          exact .imp (ihAntecedent hAntecedent) (ihConsequent hConsequent)
  | iff left right ihLeft ihRight =>
      change
        FormulaWellFormed (Formula.neg (Formula.imp (Formula.imp (Formula.hilbertize anchorSort left) (Formula.hilbertize anchorSort right)) (Formula.neg
                (Formula.imp (Formula.hilbertize anchorSort right) (Formula.hilbertize anchorSort left))))) at hFormula
      cases hFormula with
      | neg hOuterImp =>
          cases hOuterImp with
          | imp hForward hNegBackward =>
              cases hForward with
              | imp hLeft hRight =>
                  exact .iff (ihLeft hLeft) (ihRight hRight)
  | forallE sort body ih =>
      change
        FormulaWellFormed (Formula.forallE sort (Formula.hilbertize anchorSort body)) at hFormula
      cases hFormula with
      | forallE _ hBody =>
          exact .forallE sort (ih hBody)
  | existsE sort body ih =>
      change
        FormulaWellFormed (Formula.neg (Formula.forallE sort (Formula.neg (Formula.hilbertize anchorSort body)))) at hFormula
      cases hFormula with
      | neg hForall =>
          cases hForall with
          | forallE _ hNegBody =>
              cases hNegBody with
              | neg hBody =>
                  exact .existsE sort (ih hBody)
end FormulaWellFormed
namespace FormulaScoped
/-- Hilbert 归约保持任意 bound scope 下的变量作用域合法性。 -/
theorem hilbertize {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {anchorSort : σ.SortSymbol}
    {scope : Scope σ} {formula : Formula σ} (hFormula : FormulaScoped scope formula) :
    FormulaScoped scope (Formula.hilbertize anchorSort formula) := by
  induction hFormula with
  | falsum =>
      exact Formula.scoped_mono (Formula.Admissible.hilbert_falsum anchorSort).2 (fun sort => Nat.zero_le _)
  | truth =>
      exact Formula.scoped_mono (Formula.Admissible.hilbert_truth anchorSort).2 (fun sort => Nat.zero_le _)
  | rel relation arguments hArguments =>
      exact .rel relation arguments hArguments
  | equal hLeft hRight =>
      exact .equal hLeft hRight
  | neg hBody ih =>
      exact .neg ih
  | conj hLeft hRight ihLeft ihRight =>
      exact .neg <| .imp ihLeft (.neg ihRight)
  | disj hLeft hRight ihLeft ihRight =>
      exact .imp (.neg ihLeft) ihRight
  | imp hLeft hRight ihLeft ihRight =>
      exact .imp ihLeft ihRight
  | iff hLeft hRight ihLeft ihRight =>
      exact .neg <| .imp (.imp ihLeft ihRight) (.neg (.imp ihRight ihLeft))
  | forallE sort hBody ih =>
      exact .forallE sort ih
  | existsE sort hBody ih =>
      exact .neg (.forallE sort (.neg ih))
/-- Hilbert 归约结果在给定 scope 下合法时，原公式也在同一 scope 下合法。 -/
theorem hilbertize_source {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {anchorSort : σ.SortSymbol}
    {scope : Scope σ} {formula : Formula σ} (hFormula :
      FormulaScoped scope (Formula.hilbertize anchorSort formula)) :
    FormulaScoped scope formula := by
  induction formula generalizing scope with
  | falsum =>
      exact .falsum
  | truth =>
      exact .truth
  | rel relation arguments =>
      simpa [Formula.hilbertize] using hFormula
  | equal left right =>
      simpa [Formula.hilbertize] using hFormula
  | neg body ih =>
      change
        FormulaScoped scope (Formula.neg (Formula.hilbertize anchorSort body)) at hFormula
      cases hFormula with
      | neg hBody =>
          exact .neg (ih hBody)
  | conj left right ihLeft ihRight =>
      change
        FormulaScoped scope (Formula.neg (Formula.imp (Formula.hilbertize anchorSort left) (Formula.neg (Formula.hilbertize anchorSort right)))) at hFormula
      cases hFormula with
      | neg hImplication =>
          cases hImplication with
          | imp hLeft hNegRight =>
              cases hNegRight with
              | neg hRight =>
                  exact .conj (ihLeft hLeft) (ihRight hRight)
  | disj left right ihLeft ihRight =>
      change
        FormulaScoped scope (Formula.imp (Formula.neg (Formula.hilbertize anchorSort left)) (Formula.hilbertize anchorSort right)) at hFormula
      cases hFormula with
      | imp hNegLeft hRight =>
          cases hNegLeft with
          | neg hLeft =>
              exact .disj (ihLeft hLeft) (ihRight hRight)
  | imp antecedent consequent ihAntecedent ihConsequent =>
      change
        FormulaScoped scope (Formula.imp (Formula.hilbertize anchorSort antecedent) (Formula.hilbertize anchorSort consequent)) at hFormula
      cases hFormula with
      | imp hAntecedent hConsequent =>
          exact .imp (ihAntecedent hAntecedent) (ihConsequent hConsequent)
  | iff left right ihLeft ihRight =>
      change
        FormulaScoped scope (Formula.neg (Formula.imp (Formula.imp (Formula.hilbertize anchorSort left) (Formula.hilbertize anchorSort right)) (Formula.neg
                (Formula.imp (Formula.hilbertize anchorSort right) (Formula.hilbertize anchorSort left))))) at hFormula
      cases hFormula with
      | neg hOuterImp =>
          cases hOuterImp with
          | imp hForward hNegBackward =>
              cases hForward with
              | imp hLeft hRight =>
                  exact .iff (ihLeft hLeft) (ihRight hRight)
  | forallE sort body ih =>
      change
        FormulaScoped scope (Formula.forallE sort (Formula.hilbertize anchorSort body)) at hFormula
      cases hFormula with
      | forallE _ hBody =>
          exact .forallE sort (ih hBody)
  | existsE sort body ih =>
      change
        FormulaScoped scope (Formula.neg (Formula.forallE sort (Formula.neg (Formula.hilbertize anchorSort body)))) at hFormula
      cases hFormula with
      | neg hForall =>
          cases hForall with
          | forallE _ hNegBody =>
              cases hNegBody with
              | neg hBody =>
                  exact .existsE sort (ih hBody)
end FormulaScoped
namespace Admissible
/-- Hilbert 归约保持 proof-layer admissibility。 -/
theorem hilbertize {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {anchorSort : σ.SortSymbol}
    {formula : Formula σ} (hFormula : Formula.Admissible formula) :
    Formula.Admissible (Formula.hilbertize anchorSort formula) :=
  ⟨FormulaWellFormed.hilbertize hFormula.1,
    FormulaScoped.hilbertize hFormula.2⟩
/-- Hilbert 归约结果 admissible 时，原公式同样 admissible。 -/
theorem hilbertize_source {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {anchorSort : σ.SortSymbol}
    {formula : Formula σ} (hFormula :
      Formula.Admissible (Formula.hilbertize anchorSort formula)) :
    Formula.Admissible formula :=
  ⟨FormulaWellFormed.hilbertize_source hFormula.1,
    FormulaScoped.hilbertize_source hFormula.2⟩
end Admissible
/-- Hilbert 归约的结果再次归约时保持不变。 -/
@[simp]
theorem hilbertize_idempotent {σ : Signature.{u, v, w}} (anchorSort : σ.SortSymbol) (formula : Formula σ) :
    hilbertize anchorSort (hilbertize anchorSort formula) =
      hilbertize anchorSort formula := by
  induction formula with
  | falsum =>
      simp [hilbertize, hilbert_falsum, hilbert_truth]
  | truth =>
      simp [hilbertize, hilbert_truth]
  | rel relation arguments =>
      rfl
  | equal left right =>
      rfl
  | neg body ih =>
      simp [hilbertize, ih]
  | conj left right ihLeft ihRight =>
      simp [hilbertize, hilbert_conj, ihLeft, ihRight]
  | disj left right ihLeft ihRight =>
      simp [hilbertize, ihLeft, ihRight]
  | imp antecedent consequent ihAntecedent ihConsequent =>
      simp [hilbertize, ihAntecedent, ihConsequent]
  | iff left right ihLeft ihRight =>
      simp [hilbertize, hilbert_iff, hilbert_conj,
        ihLeft, ihRight]
  | forallE sort body ih =>
      simp [hilbertize, ih]
  | existsE sort body ih =>
      simp [hilbertize, ih]
/-- Hilbert 闭真式不含自由变量。 -/
@[simp]
theorem freeSupport_hilbert_truth {σ : Signature.{u, v, w}} (anchorSort : σ.SortSymbol) :
    Formula.freeSupport (hilbert_truth anchorSort) = [] :=
  rfl
/-- 打开外层 binder 不会改变 Hilbert 闭真式。 -/
@[simp]
theorem openAt_hilbert_truth {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (anchorSort target : σ.SortSymbol) (depth : Nat) (replacement : Term σ) :
    Formula.openAt target depth replacement (hilbert_truth anchorSort) =
      hilbert_truth anchorSort := by
  by_cases hSort : anchorSort = target
  · subst target
    simp [hilbert_truth, Formula.openAt, Formula.next_depth,
      Term.openAt]
  · simp [hilbert_truth, Formula.openAt, Formula.next_depth,
      Term.openAt, hSort]
/-- 关闭自由变量不会改变 Hilbert 闭真式。 -/
@[simp]
theorem closeFreeAt_hilbert_truth {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (anchorSort target : σ.SortSymbol) (id : FreeVarId) (depth : Nat) :
    Formula.closeFreeAt target id depth (hilbert_truth anchorSort) =
      hilbert_truth anchorSort := by
  by_cases hSort : anchorSort = target
  · subst target
    simp [hilbert_truth, Formula.closeFreeAt, Formula.next_depth,
      Term.closeFreeAt]
  · simp [hilbert_truth, Formula.closeFreeAt, Formula.next_depth,
      Term.closeFreeAt, hSort]
/-- 自由变量替换不会改变 Hilbert 闭真式。 -/
@[simp]
theorem substituteFree_hilbert_truth {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (anchorSort target : σ.SortSymbol) (id : FreeVarId) (replacement : Term σ) :
    Formula.substituteFree target id replacement (hilbert_truth anchorSort) =
      hilbert_truth anchorSort := by
  simp [hilbert_truth, Formula.substituteFree, Term.substituteFree]
/-- Hilbert 归约与 locally nameless 打开操作交换。 -/
theorem hilbertize_openAt {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (anchorSort target : σ.SortSymbol) (depth : Nat) (replacement : Term σ) (formula : Formula σ) :
    hilbertize anchorSort (Formula.openAt target depth replacement formula) =
      Formula.openAt target depth replacement (hilbertize anchorSort formula) := by
  induction formula generalizing depth with
  | falsum =>
      simp [hilbertize, hilbert_falsum, Formula.openAt]
  | truth =>
      simp [hilbertize, Formula.openAt]
  | rel relation arguments =>
      rfl
  | equal left right =>
      rfl
  | neg body ih =>
      simp [hilbertize, Formula.openAt, ih]
  | conj left right ihLeft ihRight =>
      simp [hilbertize, hilbert_conj, Formula.openAt,
        ihLeft, ihRight]
  | disj left right ihLeft ihRight =>
      simp [hilbertize, Formula.openAt, ihLeft, ihRight]
  | imp antecedent consequent ihAntecedent ihConsequent =>
      simp [hilbertize, Formula.openAt,
        ihAntecedent, ihConsequent]
  | iff left right ihLeft ihRight =>
      simp [hilbertize, hilbert_iff, hilbert_conj,
        Formula.openAt, ihLeft, ihRight]
  | forallE sort body ih =>
      simp [hilbertize, Formula.openAt, ih]
  | existsE sort body ih =>
      simp [hilbertize, Formula.openAt, ih]
/-- Hilbert 归约与关闭自由变量操作交换。 -/
theorem hilbertize_closeFreeAt {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (anchorSort target : σ.SortSymbol) (id : FreeVarId) (depth : Nat) (formula : Formula σ) :
    hilbertize anchorSort (Formula.closeFreeAt target id depth formula) =
      Formula.closeFreeAt target id depth (hilbertize anchorSort formula) := by
  induction formula generalizing depth with
  | falsum =>
      simp [hilbertize, hilbert_falsum, Formula.closeFreeAt]
  | truth =>
      simp [hilbertize, Formula.closeFreeAt]
  | rel relation arguments =>
      rfl
  | equal left right =>
      rfl
  | neg body ih =>
      simp [hilbertize, Formula.closeFreeAt, ih]
  | conj left right ihLeft ihRight =>
      simp [hilbertize, hilbert_conj, Formula.closeFreeAt,
        ihLeft, ihRight]
  | disj left right ihLeft ihRight =>
      simp [hilbertize, Formula.closeFreeAt, ihLeft, ihRight]
  | imp antecedent consequent ihAntecedent ihConsequent =>
      simp [hilbertize, Formula.closeFreeAt,
        ihAntecedent, ihConsequent]
  | iff left right ihLeft ihRight =>
      simp [hilbertize, hilbert_iff, hilbert_conj,
        Formula.closeFreeAt, ihLeft, ihRight]
  | forallE sort body ih =>
      simp [hilbertize, Formula.closeFreeAt, ih]
  | existsE sort body ih =>
      simp [hilbertize, Formula.closeFreeAt, ih]
/-- Hilbert 归约与自由变量替换操作交换。 -/
theorem hilbertize_substituteFree {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (anchorSort target : σ.SortSymbol) (id : FreeVarId) (replacement : Term σ) (formula : Formula σ) :
    hilbertize anchorSort (Formula.substituteFree target id replacement formula) =
      Formula.substituteFree target id replacement (hilbertize anchorSort formula) := by
  induction formula with
  | falsum =>
      simp [hilbertize, hilbert_falsum, Formula.substituteFree]
  | truth =>
      simp [hilbertize, Formula.substituteFree]
  | rel relation arguments =>
      rfl
  | equal left right =>
      rfl
  | neg body ih =>
      simp [hilbertize, Formula.substituteFree, ih]
  | conj left right ihLeft ihRight =>
      simp [hilbertize, hilbert_conj, Formula.substituteFree,
        ihLeft, ihRight]
  | disj left right ihLeft ihRight =>
      simp [hilbertize, Formula.substituteFree, ihLeft, ihRight]
  | imp antecedent consequent ihAntecedent ihConsequent =>
      simp [hilbertize, Formula.substituteFree,
        ihAntecedent, ihConsequent]
  | iff left right ihLeft ihRight =>
      simp [hilbertize, hilbert_iff, hilbert_conj,
        Formula.substituteFree, ihLeft, ihRight]
  | forallE sort body ih =>
      simp [hilbertize, Formula.substituteFree, ih]
  | existsE sort body ih =>
      simp [hilbertize, Formula.substituteFree, ih]
/-- Hilbert 归约不改变自由变量支持的成员关系。 -/
theorem mem_freeSupport_hilbertize_iff
    {σ : Signature.{u, v, w}} (anchorSort : σ.SortSymbol) (freeVariable : FreeVariable σ) (formula : Formula σ) :
    freeVariable ∈ Formula.freeSupport (hilbertize anchorSort formula) ↔
      freeVariable ∈ Formula.freeSupport formula := by
  induction formula with
  | falsum =>
      simp [hilbertize, hilbert_falsum, Formula.freeSupport]
  | truth =>
      simp [hilbertize, Formula.freeSupport]
  | rel relation arguments =>
      rfl
  | equal left right =>
      rfl
  | neg body ih =>
      simpa [hilbertize, Formula.freeSupport] using ih
  | conj left right ihLeft ihRight =>
      simp [hilbertize, hilbert_conj, Formula.freeSupport,
        ihLeft, ihRight]
  | disj left right ihLeft ihRight =>
      simp [hilbertize, Formula.freeSupport, ihLeft, ihRight]
  | imp antecedent consequent ihAntecedent ihConsequent =>
      simp [hilbertize, Formula.freeSupport,
        ihAntecedent, ihConsequent]
  | iff left right ihLeft ihRight =>
      simp [hilbertize, hilbert_iff, hilbert_conj,
        Formula.freeSupport, ihLeft, ihRight, or_comm,
        or_left_comm]
  | forallE sort body ih =>
      simpa [hilbertize, Formula.freeSupport] using ih
  | existsE sort body ih =>
      simpa [hilbertize, Formula.freeSupport] using ih
end Formula
namespace Theory
/-- 理论逐公式执行 Hilbert 归约后的像。 -/
def hilbertize {σ : Signature.{u, v, w}} (anchorSort : σ.SortSymbol) (theory : Theory σ) : Theory σ :=
  fun encoded =>
    ∃ source, theory source ∧
      encoded = Formula.hilbertize anchorSort source
/-- 原理论成员进入其 Hilbert 归约像。 -/
theorem hilbertize_mem {σ : Signature.{u, v, w}}
    {anchorSort : σ.SortSymbol} {theory : Theory σ}
    {formula : Formula σ} (hTheory : theory formula) :
    Theory.hilbertize anchorSort theory (Formula.hilbertize anchorSort formula) :=
  ⟨formula, hTheory, rfl⟩
/-- Hilbert 化理论再次 Hilbert 化后仍包含于原像。 -/
theorem hilbertize_idempotent_subset {σ : Signature.{u, v, w}}
    {anchorSort : σ.SortSymbol} {theory : Theory σ} :
    ∀ formula,
      Theory.hilbertize anchorSort (Theory.hilbertize anchorSort theory) formula →
        Theory.hilbertize anchorSort theory formula := by
  intro formula hFormula
  rcases hFormula with ⟨middle, hMiddle, rfl⟩
  rcases hMiddle with ⟨source, hSource, rfl⟩
  simpa using Theory.hilbertize_mem (anchorSort := anchorSort) hSource
/-- Hilbert 化理论包含于其二次 Hilbert 化。 -/
theorem hilbertize_subset_idempotent {σ : Signature.{u, v, w}}
    {anchorSort : σ.SortSymbol} {theory : Theory σ} :
    ∀ formula,
      Theory.hilbertize anchorSort theory formula →
        Theory.hilbertize anchorSort (Theory.hilbertize anchorSort theory) formula := by
  intro formula hFormula
  rcases hFormula with ⟨source, hSource, rfl⟩
  exact ⟨Formula.hilbertize anchorSort source,
    ⟨source, hSource, rfl⟩, (Formula.hilbertize_idempotent anchorSort source).symm⟩
end Theory
namespace HilbertBaseAxiom
/-- 基础 Hilbert 公理模式对公式参数逐点 Hilbert 归约后仍是同类公理。 -/
theorem hilbertize {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {formula : Formula σ} (anchorSort : σ.SortSymbol) (hAxiom : HilbertBaseAxiom formula) :
    HilbertBaseAxiom (Formula.hilbertize anchorSort formula) := by
  cases hAxiom with
  | implication_distribution antecedent middle consequent =>
      simpa [Formula.hilbertize] using (HilbertBaseAxiom.implication_distribution (Formula.hilbertize anchorSort antecedent)
          (Formula.hilbertize anchorSort middle) (Formula.hilbertize anchorSort consequent))
  | self_implication formula =>
      simpa [Formula.hilbertize] using (HilbertBaseAxiom.self_implication (Formula.hilbertize anchorSort formula))
  | weakening formula extra =>
      simpa [Formula.hilbertize] using (HilbertBaseAxiom.weakening (Formula.hilbertize anchorSort formula) (Formula.hilbertize anchorSort extra))
  | contradiction formula conclusion =>
      simpa [Formula.hilbertize] using (HilbertBaseAxiom.contradiction (Formula.hilbertize anchorSort formula) (Formula.hilbertize anchorSort conclusion))
  | classical formula =>
      simpa [Formula.hilbertize] using (HilbertBaseAxiom.classical (Formula.hilbertize anchorSort formula))
  | explosion formula conclusion =>
      simpa [Formula.hilbertize] using (HilbertBaseAxiom.explosion (Formula.hilbertize anchorSort formula) (Formula.hilbertize anchorSort conclusion))
  | case_analysis formula conclusion =>
      simpa [Formula.hilbertize] using (HilbertBaseAxiom.case_analysis (Formula.hilbertize anchorSort formula) (Formula.hilbertize anchorSort conclusion))
  | forall_specialization sort body term hTerm hClosed =>
      simpa [Formula.hilbertize,
        Formula.hilbertize_openAt] using (HilbertBaseAxiom.forall_specialization sort (Formula.hilbertize anchorSort body)
          term hTerm hClosed)
  | forall_distribution sort antecedent consequent =>
      simpa [Formula.hilbertize] using (HilbertBaseAxiom.forall_distribution sort (Formula.hilbertize anchorSort antecedent)
          (Formula.hilbertize anchorSort consequent))
  | vacuous_forall sort eigen formula hFresh =>
      have hFresh' : (sort, eigen) ∉
            Formula.freeSupport (Formula.hilbertize anchorSort formula) := by
        intro hMember
        exact hFresh <| (Formula.mem_freeSupport_hilbertize_iff
            anchorSort (sort, eigen) formula).mp hMember
      simpa [Formula.hilbertize,
        Formula.hilbertize_closeFreeAt] using (HilbertBaseAxiom.vacuous_forall sort eigen (Formula.hilbertize anchorSort formula) hFresh')
  | equality_substitution sort leftId rightId body =>
      simpa [Formula.hilbertize,
        Formula.hilbertize_substituteFree] using (HilbertBaseAxiom.equality_substitution sort leftId rightId (Formula.hilbertize anchorSort body))
  | equality_reflexivity sort id =>
      exact HilbertBaseAxiom.equality_reflexivity sort id
end HilbertBaseAxiom
namespace HilbertLogicalAxiom
/-- 有限全称闭包的 Hilbert 逻辑公理对公式参数归约封闭。 -/
theorem hilbertize {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {formula : Formula σ} (anchorSort : σ.SortSymbol) (hAxiom : HilbertLogicalAxiom formula) :
    HilbertLogicalAxiom (Formula.hilbertize anchorSort formula) := by
  induction hAxiom with
  | base hBase =>
      exact HilbertLogicalAxiom.base (hBase.hilbertize anchorSort)
  | forall_closure sort eigen hAxiom ih =>
      simpa [Formula.hilbertize,
        Formula.hilbertize_closeFreeAt] using (HilbertLogicalAxiom.forall_closure sort eigen ih)
end HilbertLogicalAxiom
namespace HilbertDerives
/--
若理论对 Hilbert 归约像封闭，则其严格 Hilbert 推导也可逐行执行同一归约。
这条结构递归桥只处理已经是 Hilbert 证明的证书，不经过较宽的自然演绎编译层。
-/
theorem hilbertize {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (anchorSort : σ.SortSymbol)
    {theory : Theory σ} {formula : Formula σ} (hTheoryHilbertClosed :
      ∀ candidate,
        Theory.hilbertize anchorSort theory candidate →
          theory candidate) (hDerives : HilbertDerives theory formula) :
    HilbertDerives theory (Formula.hilbertize anchorSort formula) := by
  induction hDerives with
  | logical_axiom hAxiom hAdmissible =>
      exact HilbertDerives.logical_axiom (hAxiom.hilbertize anchorSort) (Formula.Admissible.hilbertize hAdmissible)
  | theory_axiom hTheory hAdmissible =>
      exact HilbertDerives.theory_axiom (hTheoryHilbertClosed _ (Theory.hilbertize_mem hTheory)) (Formula.Admissible.hilbertize hAdmissible)
  | modus_ponens hAntecedent hImplication
      ihAntecedent ihImplication =>
      exact HilbertDerives.modus_ponens
        ihAntecedent <| by
          simpa [Formula.hilbertize] using ihImplication
end HilbertDerives
end FirstOrder
end Logic
end YesMetaZFC
