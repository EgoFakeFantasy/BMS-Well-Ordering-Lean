import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Presentation
import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Prenex
import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Reordering

/-!
# 函数图消去的递归见证闭包

本模块先按项树直接构造图见证。续延携带编译值的后置公式；目标函数节点在子参数
闭包完成后调用图全体性，非目标函数节点只重建函数项。该树形闭包随后可统一正规化
为核心编译器输出的扁平条件列表与连续见证闭包。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace FunctionGraphElimination

universe u v w

set_option autoImplicit false

variable
  {σ : Signature.{u, v, w}}
  [DecidableEq σ.SortSymbol]
  [DecidableEq σ.FuncSymbol]

omit [DecidableEq σ.FuncSymbol] in
/-- 条件合取保持公共 admissibility。 -/
theorem condition_conjunction_admissible
    {conditions : List (Formula σ)}
    {core : Formula σ}
    (hConditions :
      ∀ condition, condition ∈ conditions →
        Formula.Admissible condition)
    (hCore : Formula.Admissible core) :
    Formula.Admissible
      (condition_conjunction conditions core) :=
  ⟨condition_conjunction_well_formed
      (fun condition hCondition =>
        (hConditions condition hCondition).1)
      hCore.1,
    condition_conjunction_scoped
      (fun condition hCondition =>
        (hConditions condition hCondition).2)
      hCore.2⟩

omit [DecidableEq σ.SortSymbol]
  [DecidableEq σ.FuncSymbol] in
/-- 条件与核心共同排除一个自由变量时，整个右结合合取同样排除它。 -/
theorem condition_conjunction_fresh
    {conditions : List (Formula σ)}
    {core : Formula σ}
    {freeVariable : FreeVariable σ}
    (hConditions :
      ∀ condition, condition ∈ conditions →
        freeVariable ∉
          Formula.freeSupport condition)
    (hCore :
      freeVariable ∉
        Formula.freeSupport core) :
    freeVariable ∉
      Formula.freeSupport
        (condition_conjunction conditions core) := by
  induction conditions with
  | nil =>
      exact hCore
  | cons condition conditions ih =>
      simp only [condition_conjunction,
        Formula.freeSupport, List.mem_append]
      intro hMember
      rcases hMember with
        hMember | hMember
      · exact hConditions condition (by simp)
          hMember
      · exact ih
          (fun candidate hCandidate =>
            hConditions candidate
              (by simp [hCandidate]))
          hMember

omit [DecidableEq σ.FuncSymbol] in
private theorem conj_right_iff_congr
    {T : Theory σ} {Γ : Context σ}
    {side left right : Formula σ}
    (hEquivalent :
      Derives T Γ (Formula.iff left right))
    (hSide : Formula.Admissible side) :
    Derives T Γ
      (Formula.iff
        (Formula.conj side left)
        (Formula.conj side right)) := by
  apply Derives.iff_intro
  · have hConjunction :
        Derives T
          (Formula.conj side left :: Γ)
          (Formula.conj side left) :=
      Derives.assumption_of_mem (by simp)
        (hFormulaCheck :=
          Formula.check_admissible_complete <|
            Formula.Admissible.conj hSide <|
              Formula.Admissible.iff_left
                hEquivalent.admissible)
    have hLeft :=
      Derives.conj_elim_right hConjunction
    have hRight :=
      Derives.iff_elim_right
        hEquivalent.context_weaken_cons hLeft
    exact Derives.conj_intro
      (Derives.conj_elim_left hConjunction)
      hRight
  · have hConjunction :
        Derives T
          (Formula.conj side right :: Γ)
          (Formula.conj side right) :=
      Derives.assumption_of_mem (by simp)
        (hFormulaCheck :=
          Formula.check_admissible_complete <|
            Formula.Admissible.conj hSide <|
              Formula.Admissible.iff_right
                hEquivalent.admissible)
    have hRight :=
      Derives.conj_elim_right hConjunction
    have hLeft :=
      Derives.iff_elim_left
        hEquivalent.context_weaken_cons hRight
    exact Derives.conj_intro
      (Derives.conj_elim_left hConjunction)
      hLeft

omit [DecidableEq σ.FuncSymbol] in
/-- 条件链保持其核心公式之间的逻辑等价。 -/
theorem condition_conjunction_iff_mono
    {conditions : List (Formula σ)}
    {left right : Formula σ}
    (hConditions :
      ∀ condition, condition ∈ conditions →
        Formula.Admissible condition)
    (hEquivalent :
      Derives (Theory.empty : Theory σ) []
        (Formula.iff left right)) :
    Derives (Theory.empty : Theory σ) []
      (Formula.iff
        (condition_conjunction conditions left)
        (condition_conjunction conditions right)) := by
  induction conditions with
  | nil =>
      simpa [condition_conjunction] using hEquivalent
  | cons condition conditions ih =>
      have hCondition :=
        hConditions condition (by simp)
      have hTail :
          ∀ candidate, candidate ∈ conditions →
            Formula.Admissible candidate := by
        intro candidate hCandidate
        exact hConditions candidate
          (by simp [hCandidate])
      simpa [condition_conjunction] using
        conj_right_iff_congr
          (ih hTail) hCondition

omit [DecidableEq σ.FuncSymbol] in
private theorem conj_rotate_iff
    {first second third : Formula σ}
    (hFirst : Formula.Admissible first)
    (hSecond : Formula.Admissible second)
    (hThird : Formula.Admissible third) :
    Derives (Theory.empty : Theory σ) []
      (Formula.iff
        (Formula.conj first
          (Formula.conj second third))
        (Formula.conj second
          (Formula.conj first third))) := by
  derive_prop

omit [DecidableEq σ.FuncSymbol] in
/--
把一个根条件从右结合条件链的核心旋到最外侧。该换序只改变合取结构，不涉及
量词或函数图的任何语义前提。
-/
theorem condition_conjunction_rotate_iff
    {conditions : List (Formula σ)}
    {pivot core : Formula σ}
    (hConditions :
      ∀ condition, condition ∈ conditions →
        Formula.Admissible condition)
    (hPivot : Formula.Admissible pivot)
    (hCore : Formula.Admissible core) :
    Derives (Theory.empty : Theory σ) []
      (Formula.iff
        (condition_conjunction conditions
          (Formula.conj pivot core))
        (Formula.conj pivot
          (condition_conjunction conditions core))) := by
  induction conditions with
  | nil =>
      simpa [condition_conjunction] using
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_refl_m
          (T := (Theory.empty : Theory σ))
          (Γ := [])
          (Formula.Admissible.conj hPivot hCore)
  | cons condition conditions ih =>
      have hCondition :=
        hConditions condition (by simp)
      have hTail :
          ∀ candidate, candidate ∈ conditions →
            Formula.Admissible candidate := by
        intro candidate hCandidate
        exact hConditions candidate
          (by simp [hCandidate])
      have hTailCore :=
        condition_conjunction_admissible
          hTail hCore
      have hCongruence :=
        conj_right_iff_congr
          (ih hTail) hCondition
      have hRotate :=
        conj_rotate_iff
          hCondition hPivot hTailCore
      simpa [condition_conjunction] using
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
          hCongruence hRotate

omit [DecidableEq σ.FuncSymbol] in
/--
存在量词可以穿过一整条对其新鲜的条件合取链。证明按条件列表归纳，量词规则只
消费每个条件各自的 admissibility 与新鲜性。
-/
theorem condition_conjunction_exists_iff
    {sort : σ.SortSymbol} {eigen : FreeVarId}
    {conditions : List (Formula σ)}
    {body : Formula σ}
    (hConditions :
      ∀ condition, condition ∈ conditions →
        Formula.Admissible condition)
    (hFresh :
      ∀ condition, condition ∈ conditions →
        (sort, eigen) ∉
          Formula.freeSupport condition)
    (hBody : Formula.Admissible body) :
    Derives (Theory.empty : Theory σ) []
      (Formula.iff
        (condition_conjunction conditions
          (Formula.existsE sort
            (Formula.closeFreeAt sort eigen 0 body)))
        (Formula.existsE sort
          (Formula.closeFreeAt sort eigen 0
            (condition_conjunction conditions body)))) := by
  induction conditions with
  | nil =>
      simpa [condition_conjunction] using
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_refl_m
          (T := (Theory.empty : Theory σ))
          (Γ := [])
          (Formula.Admissible.exists_closeFreeAt
            sort eigen hBody)
  | cons condition conditions ih =>
      have hCondition :=
        hConditions condition (by simp)
      have hTailConditions :
          ∀ candidate, candidate ∈ conditions →
            Formula.Admissible candidate := by
        intro candidate hCandidate
        exact hConditions candidate
          (by simp [hCandidate])
      have hTailFresh :
          ∀ candidate, candidate ∈ conditions →
            (sort, eigen) ∉
              Formula.freeSupport candidate := by
        intro candidate hCandidate
        exact hFresh candidate
          (by simp [hCandidate])
      have hTail := ih
        hTailConditions hTailFresh
      have hTailBody :=
        condition_conjunction_admissible
          hTailConditions hBody
      have hCongruence :
          Derives (Theory.empty : Theory σ) []
            (Formula.iff
              (Formula.conj condition
                (condition_conjunction conditions
                  (Formula.existsE sort
                    (Formula.closeFreeAt sort eigen 0
                      body))))
              (Formula.conj condition
                (Formula.existsE sort
                  (Formula.closeFreeAt sort eigen 0
                    (condition_conjunction
                      conditions body))))) := by
        exact conj_right_iff_congr
          hTail hCondition
      have hMove :=
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.exists_conj_left_iff
          (T := (Theory.empty : Theory σ))
          (Γ := [])
          hCondition hTailBody
          (hFresh condition (by simp))
      simpa [condition_conjunction] using
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
          hCongruence hMove

omit [DecidableEq σ.FuncSymbol] in
/-- 空背景中的逻辑等价可逐层提升到任意连续见证闭包。 -/
theorem close_witnesses_from_iff_mono
    (sort : σ.SortSymbol) (start count : Nat)
    {left right : Formula σ}
    (hEquivalent :
      Derives (Theory.empty : Theory σ) []
        (Formula.iff left right)) :
    Derives (Theory.empty : Theory σ) []
      (Formula.iff
        (close_witnesses_from sort start count left)
        (close_witnesses_from sort start count right)) := by
  induction count with
  | zero =>
      simpa using hEquivalent
  | succ count ih =>
      simpa [close_witnesses_from] using
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.exists_iff_mono
          (T := (Theory.empty : Theory σ))
          (Γ := [])
          (sort := sort)
          (eigen := witness_id (start + count))
          (by
            intro formula hFormula
            cases hFormula)
          (by
            intro formula hFormula
            cases hFormula)
          ih

omit [DecidableEq σ.FuncSymbol] in
/-- 连续见证闭包保持公式 admissibility。 -/
theorem close_witnesses_from_admissible
    (sort : σ.SortSymbol) (start count : Nat)
    {body : Formula σ}
    (hBody : Formula.Admissible body) :
    Formula.Admissible
      (close_witnesses_from sort start count body) := by
  induction count with
  | zero =>
      simpa using hBody
  | succ count ih =>
      simpa [close_witnesses_from] using
        Formula.Admissible.exists_closeFreeAt
          sort (witness_id (start + count)) ih

omit [DecidableEq σ.FuncSymbol] in
/-- 已导出的主体可用同一批自由见证逐层重新关闭。 -/
theorem close_witnesses_from_intro
    {T : Theory σ} {Γ : Context σ}
    (sort : σ.SortSymbol) (start count : Nat)
    {body : Formula σ}
    (hBody : Derives T Γ body) :
    Derives T Γ
      (close_witnesses_from
        sort start count body) := by
  induction count with
  | zero =>
      exact hBody
  | succ count ih =>
      simp only [close_witnesses_from]
      apply Derives.exists_intro_fvar
        sort (witness_id (start + count))
      simpa [Formula.openAt_closeFreeAt] using ih

omit [DecidableEq σ.FuncSymbol] in
/--
与连续见证区间新鲜的条件块，可以整体移入该区间的存在闭包。证明只反复消费单个
存在量词穿过合取的定理，不改变见证顺序。
-/
theorem condition_conjunction_close_iff
    (sort : σ.SortSymbol) (start count : Nat)
    {conditions : List (Formula σ)}
    {body : Formula σ}
    (hConditions :
      ∀ condition, condition ∈ conditions →
        Formula.Admissible condition)
    (hFresh :
      ∀ index,
        start ≤ index →
        index < start + count →
        ∀ condition, condition ∈ conditions →
          (sort, witness_id index) ∉
            Formula.freeSupport condition)
    (hBody : Formula.Admissible body) :
    Derives (Theory.empty : Theory σ) []
      (Formula.iff
        (condition_conjunction conditions
          (close_witnesses_from
            sort start count body))
        (close_witnesses_from sort start count
          (condition_conjunction
            conditions body))) := by
  induction count with
  | zero =>
      simpa [close_witnesses_from] using
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_refl_m
          (T := (Theory.empty : Theory σ))
          (Γ := [])
          (condition_conjunction_admissible
            hConditions hBody)
  | succ count ih =>
      let eigen :=
        witness_id (start + count)
      let inner :=
        close_witnesses_from
          sort start count body
      have hInner :
          Formula.Admissible inner :=
        close_witnesses_from_admissible
          sort start count hBody
      have hOuterFresh :
          ∀ condition, condition ∈ conditions →
            (sort, eigen) ∉
              Formula.freeSupport condition := by
        intro condition hCondition
        exact hFresh (start + count)
          (by omega) (by omega)
          condition hCondition
      have hMove :=
        condition_conjunction_exists_iff
          hConditions hOuterFresh hInner
      have hInnerEquivalent :=
        ih
          (fun index hLower hUpper
              condition hCondition =>
            hFresh index hLower
              (by omega)
              condition hCondition)
      have hLifted :=
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.exists_iff_mono
          (T := (Theory.empty : Theory σ))
          (Γ := [])
          (sort := sort) (eigen := eigen)
          (by
            intro formula hFormula
            cases hFormula)
          (by
            intro formula hFormula
            cases hFormula)
          hInnerEquivalent
      simpa [close_witnesses_from,
        eigen, inner] using
          _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
            hMove hLifted

omit [DecidableEq σ.FuncSymbol] in
/-- 一个具名存在量词可以与连续见证闭包交换顺序。 -/
theorem close_witnesses_from_exists_exchange_iff
    (sort : σ.SortSymbol) (start count : Nat)
    (eigen : FreeVarId)
    {body : Formula σ}
    (hBody : Formula.Admissible body) :
    Derives (Theory.empty : Theory σ) []
      (Formula.iff
        (close_witnesses_from sort start count
          (Formula.existsE sort
            (Formula.closeFreeAt sort eigen 0 body)))
        (Formula.existsE sort
          (Formula.closeFreeAt sort eigen 0
            (close_witnesses_from
              sort start count body)))) := by
  induction count with
  | zero =>
      simpa [close_witnesses_from] using
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_refl_m
          (T := (Theory.empty : Theory σ))
          (Γ := [])
          (Formula.Admissible.exists_closeFreeAt
            sort eigen hBody)
  | succ count ih =>
      let current :=
        witness_id (start + count)
      let inner :=
        close_witnesses_from
          sort start count body
      have hInner :
          Formula.Admissible inner :=
        close_witnesses_from_admissible
          sort start count hBody
      have hLifted :=
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.exists_iff_mono
          (T := (Theory.empty : Theory σ))
          (Γ := [])
          (sort := sort) (eigen := current)
          (by
            intro formula hFormula
            cases hFormula)
          (by
            intro formula hFormula
            cases hFormula)
          ih
      have hExchange :=
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.exists_exchange_iff
          (T := (Theory.empty : Theory σ))
          (Γ := [])
          (firstSort := sort)
          (secondSort := sort)
          (first := current)
          (second := eigen)
          hInner
      simpa [close_witnesses_from,
        current, inner] using
          _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
            hLifted hExchange

omit [DecidableEq σ.FuncSymbol] in
/-- 两个连续见证闭包块可以交换顺序。 -/
theorem close_witnesses_from_exchange_iff
    (sort : σ.SortSymbol)
    (firstStart firstCount
      secondStart secondCount : Nat)
    {body : Formula σ}
    (hBody : Formula.Admissible body) :
    Derives (Theory.empty : Theory σ) []
      (Formula.iff
        (close_witnesses_from sort
          firstStart firstCount
          (close_witnesses_from sort
            secondStart secondCount body))
        (close_witnesses_from sort
          secondStart secondCount
          (close_witnesses_from sort
            firstStart firstCount body))) := by
  induction secondCount with
  | zero =>
      simpa [close_witnesses_from] using
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_refl_m
          (T := (Theory.empty : Theory σ))
          (Γ := [])
          (close_witnesses_from_admissible
            sort firstStart firstCount hBody)
  | succ secondCount ih =>
      let current :=
        witness_id
          (secondStart + secondCount)
      let secondInner :=
        close_witnesses_from sort
          secondStart secondCount body
      have hSecondInner :
          Formula.Admissible secondInner :=
        close_witnesses_from_admissible
          sort secondStart secondCount hBody
      have hMove :=
        close_witnesses_from_exists_exchange_iff
          sort firstStart firstCount
          current hSecondInner
      have hInnerEquivalent :=
        ih
      have hLifted :=
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.exists_iff_mono
          (T := (Theory.empty : Theory σ))
          (Γ := [])
          (sort := sort) (eigen := current)
          (by
            intro formula hFormula
            cases hFormula)
          (by
            intro formula hFormula
            cases hFormula)
          hInnerEquivalent
      simpa [close_witnesses_from,
        current, secondInner] using
          _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
            hMove hLifted

mutual

/--
项的续延式图闭包。`continuation` 接收该项的编译值；目标函数节点先闭包全部参数，
再为本节点引入预留见证。
-/
def term_closure
    (D : Data σ) (start : Nat)
    (source : Term σ)
    (continuation : Term σ → Formula σ) :
    Formula σ :=
  match source with
  | .var (.bvar sort index) =>
      continuation (.var (.bvar sort index))
  | .var (.fvar sort id) =>
      continuation
        (.var (.fvar sort (source_id id)))
  | .app function arguments =>
      if function = D.symbol then
        let result :=
          Term.var
            (.fvar D.sort (witness_id start))
        terms_closure D (start + 1) arguments
          (fun values =>
            Formula.existsE D.sort <|
              Formula.closeFreeAt D.sort
                (witness_id start) 0 <|
                  Formula.conj
                    (D.graph values result)
                    (continuation result))
      else
        terms_closure D start arguments
          (fun values =>
            continuation
              (.app function values))

/-- 参数表从左到右传递状态与续延。 -/
def terms_closure
    (D : Data σ) (start : Nat)
    (sources : List (Term σ))
    (continuation :
      List (Term σ) → Formula σ) :
    Formula σ :=
  match sources with
  | [] =>
      continuation []
  | head :: tail =>
      term_closure D start head
        (fun value =>
          terms_closure D
            (term D start head).next tail
            (fun values =>
              continuation (value :: values)))

end

/--
项闭包的扁平正规形：编译器一次性给出全部图条件，再统一关闭实际分配的连续见证
区间。
-/
def term_flat_closure
    (D : Data σ) (start : Nat)
    (source : Term σ)
    (continuation : Term σ → Formula σ) :
    Formula σ :=
  let compiled := term D start source
  close_witnesses_from D.sort start
    (compiled.next - start) <|
      condition_conjunction compiled.conditions
        (continuation compiled.value)

/-- 参数表闭包的扁平正规形。 -/
def terms_flat_closure
    (D : Data σ) (start : Nat)
    (sources : List (Term σ))
    (continuation :
      List (Term σ) → Formula σ) :
    Formula σ :=
  let compiled := terms D start sources
  close_witnesses_from D.sort start
    (compiled.next - start) <|
      condition_conjunction compiled.conditions
        (continuation compiled.values)

mutual

/-- 项闭包保持续延给出的 admissibility。 -/
theorem term_closure_admissible
    (D : Data σ) (start : Nat)
    {source : Term σ} {sort : σ.SortSymbol}
    (hSource : Term.Admissible source sort)
    (continuation : Term σ → Formula σ)
    (hContinuation :
      ∀ {value},
        Term.Admissible value sort →
          Formula.Admissible
            (continuation value)) :
    Formula.Admissible
      (term_closure D start source
        continuation) := by
  cases source with
  | var value =>
      cases value <;>
        simpa [term_closure, source_term] using
          hContinuation
            (source_term_admissible hSource)
  | app function arguments =>
      have hArguments :=
        app_arguments_admissible
          function arguments hSource
      by_cases hFunction : function = D.symbol
      · subst function
        have hSort : sort = D.sort := by
          apply TermWellSorted.sort_unique
            hSource.1
          rw [← D.codomain_eq]
          exact TermWellSorted.app
            D.symbol hArguments.1
        subst sort
        let result :=
          Term.var
            (.fvar D.sort (witness_id start))
        have hResult :
            Term.Admissible result D.sort :=
          ⟨TermWellSorted.fvar
              D.sort (witness_id start),
            TermScoped.fvar
              D.sort (witness_id start)⟩
        have hClosed :=
          terms_closure_admissible
            D (start + 1) hArguments
            (fun values =>
              Formula.existsE D.sort <|
                Formula.closeFreeAt D.sort
                  (witness_id start) 0 <|
                    Formula.conj
                      (D.graph values result)
                      (continuation result))
            (by
              intro values hValues
              exact Formula.Admissible.exists_closeFreeAt
                D.sort (witness_id start) <|
                  Formula.Admissible.conj
                    (graph_admissible
                      D hValues hResult)
                    (hContinuation hResult))
        simpa [term_closure, result] using hClosed
      · have hClosed :=
          terms_closure_admissible
            D start hArguments
            (fun values =>
              continuation
                (.app function values))
            (by
              intro values hValues
              have hValue :
                  Term.Admissible
                    (.app function values) sort := by
                constructor
                · cases hSource.1 with
                  | app _ _ =>
                      exact TermWellSorted.app
                        function hValues.1
                · exact TermScoped.app
                    function values hValues.2
              exact hContinuation hValue)
        simpa [term_closure, hFunction] using
          hClosed

/-- 参数表闭包保持续延给出的 admissibility。 -/
theorem terms_closure_admissible
    (D : Data σ) (start : Nat)
    {sources : List (Term σ)}
    {sorts : List σ.SortSymbol}
    (hSources :
      ArgsAdmissible sources sorts)
    (continuation :
      List (Term σ) → Formula σ)
    (hContinuation :
      ∀ {values},
        ArgsAdmissible values sorts →
          Formula.Admissible
            (continuation values)) :
    Formula.Admissible
      (terms_closure D start sources
        continuation) := by
  cases sources with
  | nil =>
      cases hSources.1
      simpa [terms_closure] using
        hContinuation
          (ArgsAdmissible.nil)
  | cons head tail =>
      rcases ArgsAdmissible.exists_cons hSources with
        ⟨headSort, tailSorts, hSorts,
          hHead, hTail⟩
      subst sorts
      apply term_closure_admissible
        D start hHead
      intro value hValue
      apply terms_closure_admissible
        D (term D start head).next hTail
      intro values hValues
      exact hContinuation
        (ArgsAdmissible.cons
          hValue hValues)

end

/-- 单项编译产生的每个图条件都 admissible。 -/
theorem term_conditions_admissible
    (D : Data σ) (start : Nat)
    {source : Term σ} {sort : σ.SortSymbol}
    (hSource : Term.Admissible source sort) :
    ∀ condition,
      condition ∈ (term D start source).conditions →
        Formula.Admissible condition := by
  intro condition hCondition
  exact
    ⟨(term_well_formed D start hSource.1).2
        condition hCondition,
      (term_scoped D start hSource.2).2
        condition hCondition⟩

/-- 参数表编译产生的每个图条件都 admissible。 -/
theorem terms_conditions_admissible
    (D : Data σ) (start : Nat)
    {sources : List (Term σ)}
    {sorts : List σ.SortSymbol}
    (hSources : ArgsAdmissible sources sorts) :
    ∀ condition,
      condition ∈ (terms D start sources).conditions →
        Formula.Admissible condition := by
  intro condition hCondition
  exact
    ⟨(terms_well_formed D start hSources.1).2
        condition hCondition,
      (terms_scoped D start hSources.2).2
        condition hCondition⟩

/-- 扁平项闭包保持续延给出的 admissibility。 -/
theorem term_flat_closure_admissible
    (D : Data σ) (start : Nat)
    {source : Term σ} {sort : σ.SortSymbol}
    (hSource : Term.Admissible source sort)
    (continuation : Term σ → Formula σ)
    (hContinuation :
      ∀ {value},
        Term.Admissible value sort →
          Formula.Admissible
            (continuation value)) :
    Formula.Admissible
      (term_flat_closure D start source
        continuation) := by
  let compiled := term D start source
  apply close_witnesses_from_admissible
  apply condition_conjunction_admissible
  · simpa [compiled] using
      term_conditions_admissible
        D start hSource
  · apply hContinuation
    exact
      ⟨(term_well_formed
          D start hSource.1).1,
        (term_scoped
          D start hSource.2).1⟩

/-- 扁平参数闭包同样保持续延给出的 admissibility。 -/
theorem terms_flat_closure_admissible
    (D : Data σ) (start : Nat)
    {sources : List (Term σ)}
    {sorts : List σ.SortSymbol}
    (hSources : ArgsAdmissible sources sorts)
    (continuation :
      List (Term σ) → Formula σ)
    (hContinuation :
      ∀ {values},
        ArgsAdmissible values sorts →
          Formula.Admissible
            (continuation values)) :
    Formula.Admissible
      (terms_flat_closure D start sources
        continuation) := by
  let compiled := terms D start sources
  apply close_witnesses_from_admissible
  apply condition_conjunction_admissible
  · simpa [compiled] using
      terms_conditions_admissible
        D start hSources
  · apply hContinuation
    simpa [compiled] using
      terms_admissible D start hSources

mutual

/--
项树闭包与编译器扁平闭包逻辑等价。证明只依赖函数图的语法侧条件；图的全体性
留给后续 `GraphPresentation` 层消费。
-/
theorem term_closure_iff_flat
    (D : Data σ) (start : Nat)
    {source : Term σ} {sort : σ.SortSymbol}
    (hSource : Term.Admissible source sort)
    (continuation : Term σ → Formula σ)
    (hContinuation :
      ∀ {value},
        Term.Admissible value sort →
          Formula.Admissible
            (continuation value)) :
    Derives (Theory.empty : Theory σ) []
      (Formula.iff
        (term_closure D start source continuation)
        (term_flat_closure D start source
          continuation)) := by
  cases source with
  | var value =>
      have hValue :=
        source_term_admissible hSource
      have hRefl :=
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_refl_m
          (T := (Theory.empty : Theory σ))
          (Γ := [])
          (hContinuation hValue)
      cases value <;>
        simpa [term_closure, term_flat_closure,
          term, source_term] using hRefl
  | app function arguments =>
      have hArguments :=
        app_arguments_admissible
          function arguments hSource
      by_cases hFunction : function = D.symbol
      · subst function
        have hSort : sort = D.sort := by
          apply TermWellSorted.sort_unique
            hSource.1
          rw [← D.codomain_eq]
          exact TermWellSorted.app
            D.symbol hArguments.1
        subst sort
        let compiled :=
          terms D (start + 1) arguments
        let result :=
          Term.var
            (.fvar D.sort (witness_id start))
        let core :=
          continuation result
        have hResult :
            Term.Admissible result D.sort :=
          ⟨TermWellSorted.fvar
              D.sort (witness_id start),
            TermScoped.fvar
              D.sort (witness_id start)⟩
        have hCompiledArguments :
            ArgsAdmissible compiled.values
              (σ.funcDomain D.symbol) := by
          simpa [compiled] using
            terms_admissible D (start + 1)
              hArguments
        have hCore :
            Formula.Admissible core := by
          exact hContinuation hResult
        have hConditions :
            ∀ condition,
              condition ∈ compiled.conditions →
                Formula.Admissible condition := by
          simpa [compiled] using
            terms_conditions_admissible
              D (start + 1) hArguments
        have hChild :=
          terms_closure_iff_flat
            D (start + 1) hArguments
            (fun values =>
              Formula.existsE D.sort <|
                Formula.closeFreeAt D.sort
                  (witness_id start) 0 <|
                    Formula.conj
                      (D.graph values result)
                      core)
            (by
              intro values hValues
              exact
                Formula.Admissible.exists_closeFreeAt
                  D.sort (witness_id start) <|
                    Formula.Admissible.conj
                      (graph_admissible
                        D hValues hResult)
                      hCore)
        have hFresh :
            ∀ condition,
              condition ∈ compiled.conditions →
                (D.sort, witness_id start) ∉
                  Formula.freeSupport condition := by
          intro condition hCondition
          exact
            terms_conditions_witness_fresh_below
              D (start + 1) arguments
                (by omega)
                condition
                (by simpa [compiled] using hCondition)
        have hMove :=
          condition_conjunction_exists_iff
            hConditions hFresh
            (Formula.Admissible.conj
              (graph_admissible
                D hCompiledArguments hResult)
              hCore)
        have hRotate :=
          condition_conjunction_rotate_iff
            hConditions
            (graph_admissible
              D hCompiledArguments hResult)
            hCore
        have hRotateExists :=
          _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.exists_iff_mono
            (T := (Theory.empty : Theory σ))
            (Γ := [])
            (sort := D.sort)
            (eigen := witness_id start)
            (by
              intro formula hFormula
              cases hFormula)
            (by
              intro formula hFormula
              cases hFormula)
            hRotate
        have hInner :=
          _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
            hMove hRotateExists
        let childCount :=
          compiled.next - (start + 1)
        have hLifted :=
          close_witnesses_from_iff_mono
            D.sort (start + 1)
              childCount hInner
        have hTree :=
          _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
            hChild hLifted
        have hCompiledNext :
            start + 1 ≤ compiled.next := by
          simpa [compiled] using
            terms_next_ge D
              (start + 1) arguments
        have hCount :
            compiled.next - start =
              1 + childCount := by
          simp only [childCount]
          omega
        simpa [term_closure, term_flat_closure,
          terms_flat_closure, term, compiled,
          result, core, childCount, hCount,
          close_witnesses_from_add,
          condition_conjunction] using hTree
      · have hClosed :=
          terms_closure_iff_flat
            D start hArguments
            (fun values =>
              continuation
                (.app function values))
            (by
              intro values hValues
              have hValue :
                  Term.Admissible
                    (.app function values) sort := by
                constructor
                · cases hSource.1 with
                  | app _ _ =>
                      exact TermWellSorted.app
                        function hValues.1
                · exact TermScoped.app
                    function values hValues.2
              exact hContinuation hValue)
        simpa [term_closure, term_flat_closure,
          terms_flat_closure, term,
          hFunction] using hClosed

/--
参数表树闭包与扁平闭包逻辑等价。`cons` 分支显式交换首项与尾项的见证块，随后
用条件列表拼接定理恢复编译器的线性布局。
-/
theorem terms_closure_iff_flat
    (D : Data σ) (start : Nat)
    {sources : List (Term σ)}
    {sorts : List σ.SortSymbol}
    (hSources : ArgsAdmissible sources sorts)
    (continuation :
      List (Term σ) → Formula σ)
    (hContinuation :
      ∀ {values},
        ArgsAdmissible values sorts →
          Formula.Admissible
            (continuation values)) :
    Derives (Theory.empty : Theory σ) []
      (Formula.iff
        (terms_closure D start sources
          continuation)
        (terms_flat_closure D start sources
          continuation)) := by
  cases sources with
  | nil =>
      cases hSources.1
      have hRefl :=
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_refl_m
          (T := (Theory.empty : Theory σ))
          (Γ := [])
          (hContinuation ArgsAdmissible.nil)
      simpa [terms_closure, terms_flat_closure,
        terms] using hRefl
  | cons head tail =>
      rcases ArgsAdmissible.exists_cons hSources with
        ⟨headSort, tailSorts, hSorts,
          hHead, hTail⟩
      subst sorts
      let compiledHead :=
        term D start head
      let compiledTail :=
        terms D compiledHead.next tail
      let headCount :=
        compiledHead.next - start
      let tailCount :=
        compiledTail.next - compiledHead.next
      have hCompiledHead :
          Term.Admissible
            compiledHead.value headSort := by
        exact
          ⟨(term_well_formed
              D start hHead.1).1,
            (term_scoped
              D start hHead.2).1⟩
      have hCompiledTail :
          ArgsAdmissible
            compiledTail.values tailSorts := by
        simpa [compiledHead, compiledTail] using
          terms_admissible D
            (term D start head).next hTail
      have hHeadConditions :
          ∀ condition,
            condition ∈ compiledHead.conditions →
              Formula.Admissible condition := by
        simpa [compiledHead] using
          term_conditions_admissible
            D start hHead
      have hTailConditions :
          ∀ condition,
            condition ∈ compiledTail.conditions →
              Formula.Admissible condition := by
        simpa [compiledHead, compiledTail] using
          terms_conditions_admissible
            D (term D start head).next hTail
      have hTailEquivalent :=
        terms_closure_iff_flat
          D compiledHead.next hTail
          (fun values =>
            continuation
              (compiledHead.value :: values))
          (by
            intro values hValues
            exact hContinuation
              (ArgsAdmissible.cons
                hCompiledHead hValues))
      have hHeadTree :=
        term_closure_iff_flat
          D start hHead
          (fun value =>
            terms_closure D compiledHead.next tail
              (fun values =>
                continuation (value :: values)))
          (by
            intro value hValue
            apply terms_closure_admissible
              D compiledHead.next hTail
            intro values hValues
            exact hContinuation
              (ArgsAdmissible.cons
                hValue hValues))
      have hTailCongruence :=
        condition_conjunction_iff_mono
          hHeadConditions hTailEquivalent
      have hTailLifted :=
        close_witnesses_from_iff_mono
          D.sort start headCount
            hTailCongruence
      have hAfterTail :=
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
          hHeadTree hTailLifted
      have hTailCore :
          Formula.Admissible
            (condition_conjunction
              compiledTail.conditions
              (continuation
                (compiledHead.value ::
                  compiledTail.values))) :=
        condition_conjunction_admissible
          hTailConditions <|
            hContinuation <|
              ArgsAdmissible.cons
                hCompiledHead hCompiledTail
      have hHeadFresh :
          ∀ index,
            compiledHead.next ≤ index →
            index <
              compiledHead.next + tailCount →
            ∀ condition,
              condition ∈ compiledHead.conditions →
                (D.sort, witness_id index) ∉
                  Formula.freeSupport condition := by
        intro index hLower hUpper
        exact term_conditions_witness_fresh_above
          D start head hLower
      have hMove :=
        condition_conjunction_close_iff
          D.sort compiledHead.next tailCount
          hHeadConditions hHeadFresh hTailCore
      have hMoveLifted :=
        close_witnesses_from_iff_mono
          D.sort start headCount hMove
      have hAfterMove :=
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
          hAfterTail hMoveLifted
      have hCombinedCore :
          Formula.Admissible
            (condition_conjunction
              compiledHead.conditions
              (condition_conjunction
                compiledTail.conditions
                (continuation
                  (compiledHead.value ::
                    compiledTail.values)))) :=
        condition_conjunction_admissible
          hHeadConditions hTailCore
      have hExchange :=
        close_witnesses_from_exchange_iff
          D.sort start headCount
            compiledHead.next tailCount
            hCombinedCore
      have hNormalized :=
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
          hAfterMove hExchange
      have hHeadNext :
          start ≤ compiledHead.next := by
        simpa [compiledHead] using
          term_next_ge D start head
      have hTailNext :
          compiledHead.next ≤
            compiledTail.next := by
        simpa [compiledHead, compiledTail] using
          terms_next_ge D
            (term D start head).next tail
      have hHeadStart :
          start + headCount =
            compiledHead.next := by
        simp only [headCount]
        omega
      have hTotalCount :
          compiledTail.next - start =
            headCount + tailCount := by
        simp only [headCount, tailCount]
        omega
      simpa [terms_closure, terms_flat_closure,
        terms, compiledHead, compiledTail,
        headCount, tailCount, hHeadStart,
        hTotalCount, close_witnesses_from_add,
        condition_conjunction_append] using
          hNormalized

end

namespace GraphPresentation

variable {D : Data σ}

mutual

/--
若续延对当前编译值可导，则基础理论可构造整棵项图闭包。新鲜性只覆盖该项实际
分配的见证区间。
-/
theorem term_closure_derives
    (P : GraphPresentation D) (start : Nat)
    {source : Term σ} {sort : σ.SortSymbol}
    (hSource : Term.Admissible source sort)
    {Γ : Context σ}
    (hFresh :
      ∀ index,
        start ≤ index →
        index < (term D start source).next →
        ∀ formula, formula ∈ Γ →
          (D.sort, witness_id index) ∉
            Formula.freeSupport formula)
    (continuation : Term σ → Formula σ)
    (hContinuation :
      Derives P.theory Γ
        (continuation
          (term D start source).value)) :
    Derives P.theory Γ
      (term_closure D start source
        continuation) := by
  cases source with
  | var value =>
      cases value <;>
        simpa [term, term_closure] using
          hContinuation
  | app function arguments =>
      have hArguments :=
        app_arguments_admissible
          function arguments hSource
      by_cases hFunction : function = D.symbol
      · subst function
        let compiled :=
          terms D (start + 1) arguments
        let result :=
          Term.var
            (.fvar D.sort (witness_id start))
        have hStartLt :
            start <
              (term D start
                (.app D.symbol arguments)).next := by
          have hCompiled :
              start + 1 ≤ compiled.next := by
            simpa [compiled] using
              terms_next_ge D
                (start + 1) arguments
          simpa [term, compiled] using
            Nat.lt_of_lt_of_le
              (Nat.lt_succ_self start)
              hCompiled
        have hExists :
            Derives P.theory Γ
              (Formula.existsE D.sort
                (Formula.closeFreeAt D.sort
                  (witness_id start) 0
                  (D.graph compiled.values
                    result))) :=
          (P.selected_total start hArguments).context_weaken
            (by simp)
        have hRoot :
            Derives P.theory Γ
              (Formula.existsE D.sort
                (Formula.closeFreeAt D.sort
                  (witness_id start) 0
                  (Formula.conj
                    (D.graph compiled.values result)
                    (continuation result)))) := by
          apply P.exists_conj_of_exists
          · intro formula hFormula
            exact hFresh start
              (Nat.le_refl start) hStartLt
              formula hFormula
          · exact hExists
          · simpa [term, result, compiled] using
              hContinuation
        have hClosed :=
          terms_closure_derives
            P (start + 1) hArguments
            (Γ := Γ)
            (fun index hLower hUpper formula hFormula => by
              apply hFresh index
              · omega
              · simpa [term, compiled] using hUpper
              · exact hFormula)
            (fun values =>
              Formula.existsE D.sort <|
                Formula.closeFreeAt D.sort
                  (witness_id start) 0 <|
                    Formula.conj
                      (D.graph values result)
                      (continuation result))
            (by simpa [compiled] using hRoot)
        simpa [term_closure, result,
          compiled] using hClosed
      · have hClosed :=
          terms_closure_derives
            P start hArguments
            (Γ := Γ)
            (fun index hLower hUpper formula hFormula => by
              apply hFresh index hLower
              · simpa [term, hFunction] using hUpper
              · exact hFormula)
            (fun values =>
              continuation
                (.app function values))
            (by
              simpa [term, hFunction] using
                hContinuation)
        simpa [term_closure, hFunction] using
          hClosed

/-- 参数表闭包逐项复用项闭包，并保持线性状态区间。 -/
theorem terms_closure_derives
    (P : GraphPresentation D) (start : Nat)
    {sources : List (Term σ)}
    {sorts : List σ.SortSymbol}
    (hSources :
      ArgsAdmissible sources sorts)
    {Γ : Context σ}
    (hFresh :
      ∀ index,
        start ≤ index →
        index < (terms D start sources).next →
        ∀ formula, formula ∈ Γ →
          (D.sort, witness_id index) ∉
            Formula.freeSupport formula)
    (continuation :
      List (Term σ) → Formula σ)
    (hContinuation :
      Derives P.theory Γ
        (continuation
          (terms D start sources).values)) :
    Derives P.theory Γ
      (terms_closure D start sources
        continuation) := by
  cases sources with
  | nil =>
      simpa [terms, terms_closure] using
        hContinuation
  | cons head tail =>
      rcases ArgsAdmissible.exists_cons hSources with
        ⟨headSort, tailSorts, hSorts,
          hHead, hTail⟩
      subst sorts
      let compiledHead :=
        term D start head
      let compiledTail :=
        terms D compiledHead.next tail
      have hHeadNext :
          compiledHead.next ≤
            compiledTail.next := by
        simpa [compiledHead, compiledTail] using
          terms_next_ge D
            (term D start head).next tail
      apply term_closure_derives
        P start hHead
      · intro index hLower hUpper formula hFormula
        apply hFresh index hLower
        · apply Nat.lt_of_lt_of_le hUpper
          exact hHeadNext
        · exact hFormula
      · apply terms_closure_derives
          P compiledHead.next hTail
        · intro index hLower hUpper formula hFormula
          apply hFresh index
          · exact Nat.le_trans
              (term_next_ge D start head)
              hLower
          · simpa [terms, compiledHead,
              compiledTail] using hUpper
          · exact hFormula
        · simpa [terms, compiledHead,
            compiledTail] using hContinuation

end

mutual

/--
项闭包的依赖版构造：续延允许使用该项全部编译条件作为局部假设。
-/
theorem term_closure_derives_from_conditions
    (P : GraphPresentation D) (start : Nat)
    {source : Term σ} {sort : σ.SortSymbol}
    (hSource : Term.Admissible source sort)
    {Γ : Context σ}
    (hFresh :
      ∀ index,
        start ≤ index →
        index < (term D start source).next →
        ∀ formula, formula ∈ Γ →
          (D.sort, witness_id index) ∉
            Formula.freeSupport formula)
    (continuation : Term σ → Formula σ)
    (hContinuation :
      Derives P.theory
        ((term D start source).conditions ++ Γ)
        (continuation
          (term D start source).value)) :
    Derives P.theory Γ
      (term_closure D start source
        continuation) := by
  cases source with
  | var value =>
      cases value <;>
        simpa [term, term_closure] using
          hContinuation
  | app function arguments =>
      have hArguments :=
        app_arguments_admissible
          function arguments hSource
      by_cases hFunction : function = D.symbol
      · subst function
        let compiled :=
          terms D (start + 1) arguments
        let result :=
          Term.var
            (.fvar D.sort (witness_id start))
        have hSort : sort = D.sort := by
          apply TermWellSorted.sort_unique
            hSource.1
          rw [← D.codomain_eq]
          exact TermWellSorted.app
            D.symbol hArguments.1
        subst sort
        have hCompiled :
            ArgsAdmissible compiled.values
              (σ.funcDomain D.symbol) := by
          simpa [compiled] using
            terms_admissible D
              (start + 1) hArguments
        have hResult :
            Term.Admissible result D.sort :=
          ⟨TermWellSorted.fvar D.sort
              (witness_id start),
            TermScoped.fvar D.sort
              (witness_id start)⟩
        have hExists :
            Derives P.theory
              (compiled.conditions ++ Γ)
              (Formula.existsE D.sort
                (Formula.closeFreeAt D.sort
                  (witness_id start) 0
                  (D.graph compiled.values
                    result))) :=
          (P.selected_total start hArguments).context_weaken
            (by simp)
        have hSide :
            Derives P.theory
              (D.graph compiled.values result ::
                compiled.conditions ++ Γ)
              (continuation result) := by
          simpa [term, compiled, result] using
            hContinuation
        have hRoot :
            Derives P.theory
              (compiled.conditions ++ Γ)
              (Formula.existsE D.sort
                (Formula.closeFreeAt D.sort
                  (witness_id start) 0
                  (Formula.conj
                    (D.graph compiled.values result)
                    (continuation result)))) := by
          apply P.exists_conj_of_case
          · intro formula hFormula
            rcases List.mem_append.mp hFormula with
              hCondition | hFormula
            · exact
                terms_conditions_witness_fresh_below
                  D (start + 1) arguments
                    (by omega) formula <| by
                      simpa [compiled] using hCondition
            · exact hFresh start
                (Nat.le_refl start)
                (by
                  have hNext :
                      start + 1 ≤ compiled.next := by
                    simpa [compiled] using
                      terms_next_ge D
                        (start + 1) arguments
                  simpa [term, compiled] using
                    Nat.lt_of_lt_of_le
                      (Nat.lt_succ_self start)
                      hNext)
                formula hFormula
          · exact hExists
          · exact hSide
        have hClosed :=
          terms_closure_derives_from_conditions
            P (start + 1) hArguments
            (Γ := Γ)
            (fun index hLower hUpper formula hFormula => by
              apply hFresh index
              · omega
              · simpa [term, compiled] using hUpper
              · exact hFormula)
            (fun values =>
              Formula.existsE D.sort <|
                Formula.closeFreeAt D.sort
                  (witness_id start) 0 <|
                    Formula.conj
                      (D.graph values result)
                      (continuation result))
            (by simpa [compiled] using hRoot)
        simpa [term_closure, compiled,
          result] using hClosed
      · have hClosed :=
          terms_closure_derives_from_conditions
            P start hArguments
            (Γ := Γ)
            (fun index hLower hUpper formula hFormula => by
              apply hFresh index hLower
              · simpa [term, hFunction] using hUpper
              · exact hFormula)
            (fun values =>
              continuation
                (.app function values))
            (by
              simpa [term, hFunction] using
                hContinuation)
        simpa [term_closure, hFunction] using
          hClosed

/-- 参数表闭包的依赖版构造，逐项消去线性条件块。 -/
theorem terms_closure_derives_from_conditions
    (P : GraphPresentation D) (start : Nat)
    {sources : List (Term σ)}
    {sorts : List σ.SortSymbol}
    (hSources :
      ArgsAdmissible sources sorts)
    {Γ : Context σ}
    (hFresh :
      ∀ index,
        start ≤ index →
        index < (terms D start sources).next →
        ∀ formula, formula ∈ Γ →
          (D.sort, witness_id index) ∉
            Formula.freeSupport formula)
    (continuation :
      List (Term σ) → Formula σ)
    (hContinuation :
      Derives P.theory
        ((terms D start sources).conditions ++ Γ)
        (continuation
          (terms D start sources).values)) :
    Derives P.theory Γ
      (terms_closure D start sources
        continuation) := by
  cases sources with
  | nil =>
      simpa [terms, terms_closure] using
        hContinuation
  | cons head tail =>
      rcases ArgsAdmissible.exists_cons hSources with
        ⟨headSort, tailSorts, hSorts,
          hHead, hTail⟩
      subst sorts
      let compiledHead := term D start head
      let compiledTail :=
        terms D compiledHead.next tail
      apply term_closure_derives_from_conditions
        P start hHead
      · intro index hLower hUpper formula hFormula
        apply hFresh index hLower
        · exact Nat.lt_of_lt_of_le hUpper <| by
            simpa [compiledHead, compiledTail] using
              terms_next_ge D
                (term D start head).next tail
        · exact hFormula
      · apply terms_closure_derives_from_conditions
          P compiledHead.next hTail
        · intro index hLower hUpper formula hFormula
          rcases List.mem_append.mp hFormula with
            hCondition | hFormula
          · exact term_conditions_witness_fresh_above
              D start head hLower
                formula <| by
                  simpa [compiledHead] using
                    hCondition
          · apply hFresh index
            · exact Nat.le_trans
                (term_next_ge D start head)
                hLower
            · simpa [terms, compiledHead,
                compiledTail] using hUpper
            · exact hFormula
        · apply hContinuation.context_weaken
          intro formula hFormula
          have hFormula' :
              formula ∈
                (compiledHead.conditions ++
                    compiledTail.conditions) ++ Γ := by
            simpa [terms, compiledHead,
              compiledTail] using hFormula
          rcases List.mem_append.mp hFormula' with
            hConditions | hFormula
          · rcases List.mem_append.mp hConditions with
              hHeadCondition | hTailCondition
            · exact List.mem_append.mpr <|
                Or.inr <| List.mem_append.mpr <|
                  Or.inl hHeadCondition
            · exact List.mem_append.mpr
                (Or.inl hTailCondition)
          · exact List.mem_append.mpr <|
              Or.inr <| List.mem_append.mpr <|
                Or.inr hFormula

end

/--
树闭包的构造性推导经正规化后，直接给出编译器扁平项闭包。续延的 admissibility
只用于逻辑等价证明，图见证仍完全由 `GraphPresentation` 构造。
-/
theorem term_flat_derives
    (P : GraphPresentation D) (start : Nat)
    {source : Term σ} {sort : σ.SortSymbol}
    (hSource : Term.Admissible source sort)
    {Γ : Context σ}
    (hFresh :
      ∀ index,
        start ≤ index →
        index < (term D start source).next →
        ∀ formula, formula ∈ Γ →
          (D.sort, witness_id index) ∉
            Formula.freeSupport formula)
    (continuation : Term σ → Formula σ)
    (hContinuationAdmissible :
      ∀ {value},
        Term.Admissible value sort →
          Formula.Admissible
            (continuation value))
    (hContinuation :
      Derives P.theory Γ
        (continuation
          (term D start source).value)) :
    Derives P.theory Γ
      (term_flat_closure D start source
        continuation) := by
  have hTree :=
    P.term_closure_derives start hSource
      hFresh continuation hContinuation
  have hEquivalent :=
    Derives.of_empty
      (T := P.theory) (Γ := Γ) <|
        term_closure_iff_flat
          D start hSource continuation
            hContinuationAdmissible
  exact Derives.iff_elim_right
    hEquivalent hTree

/-- 参数表树闭包的构造性推导经正规化后，直接给出扁平参数闭包。 -/
theorem terms_flat_derives
    (P : GraphPresentation D) (start : Nat)
    {sources : List (Term σ)}
    {sorts : List σ.SortSymbol}
    (hSources : ArgsAdmissible sources sorts)
    {Γ : Context σ}
    (hFresh :
      ∀ index,
        start ≤ index →
        index < (terms D start sources).next →
        ∀ formula, formula ∈ Γ →
          (D.sort, witness_id index) ∉
            Formula.freeSupport formula)
    (continuation :
      List (Term σ) → Formula σ)
    (hContinuationAdmissible :
      ∀ {values},
        ArgsAdmissible values sorts →
          Formula.Admissible
            (continuation values))
    (hContinuation :
      Derives P.theory Γ
        (continuation
          (terms D start sources).values)) :
    Derives P.theory Γ
      (terms_flat_closure D start sources
        continuation) := by
  have hTree :=
    P.terms_closure_derives start hSources
      hFresh continuation hContinuation
  have hEquivalent :=
    Derives.of_empty
      (T := P.theory) (Γ := Γ) <|
        terms_closure_iff_flat
          D start hSources continuation
            hContinuationAdmissible
  exact Derives.iff_elim_right
    hEquivalent hTree

/--
依赖图条件的树闭包经正规化后，得到同一扁平编译布局。
-/
theorem term_flat_derives_from_conditions
    (P : GraphPresentation D) (start : Nat)
    {source : Term σ} {sort : σ.SortSymbol}
    (hSource : Term.Admissible source sort)
    {Γ : Context σ}
    (hFresh :
      ∀ index,
        start ≤ index →
        index < (term D start source).next →
        ∀ formula, formula ∈ Γ →
          (D.sort, witness_id index) ∉
            Formula.freeSupport formula)
    (continuation : Term σ → Formula σ)
    (hContinuationAdmissible :
      ∀ {value},
        Term.Admissible value sort →
          Formula.Admissible
            (continuation value))
    (hContinuation :
      Derives P.theory
        ((term D start source).conditions ++ Γ)
        (continuation
          (term D start source).value)) :
    Derives P.theory Γ
      (term_flat_closure D start source
        continuation) := by
  have hTree :=
    P.term_closure_derives_from_conditions
      start hSource hFresh
      continuation hContinuation
  have hEquivalent :=
    Derives.of_empty
      (T := P.theory) (Γ := Γ) <|
        term_closure_iff_flat
          D start hSource continuation
            hContinuationAdmissible
  exact Derives.iff_elim_right
    hEquivalent hTree

/-- 参数表的依赖图条件闭包同样可正规化为扁平布局。 -/
theorem terms_flat_derives_from_conditions
    (P : GraphPresentation D) (start : Nat)
    {sources : List (Term σ)}
    {sorts : List σ.SortSymbol}
    (hSources : ArgsAdmissible sources sorts)
    {Γ : Context σ}
    (hFresh :
      ∀ index,
        start ≤ index →
        index < (terms D start sources).next →
        ∀ formula, formula ∈ Γ →
          (D.sort, witness_id index) ∉
            Formula.freeSupport formula)
    (continuation :
      List (Term σ) → Formula σ)
    (hContinuationAdmissible :
      ∀ {values},
        ArgsAdmissible values sorts →
          Formula.Admissible
            (continuation values))
    (hContinuation :
      Derives P.theory
        ((terms D start sources).conditions ++ Γ)
        (continuation
          (terms D start sources).values)) :
    Derives P.theory Γ
      (terms_flat_closure D start sources
        continuation) := by
  have hTree :=
    P.terms_closure_derives_from_conditions
      start hSources hFresh
      continuation hContinuation
  have hEquivalent :=
    Derives.of_empty
      (T := P.theory) (Γ := Γ) <|
        terms_closure_iff_flat
          D start hSources continuation
            hContinuationAdmissible
  exact Derives.iff_elim_right
    hEquivalent hTree

/-- 空上下文中，每个 admissible 项都具有完整的递归图见证树。 -/
theorem term_closure_truth
    (P : GraphPresentation D) (start : Nat)
    {source : Term σ} {sort : σ.SortSymbol}
    (hSource : Term.Admissible source sort) :
    Derives P.theory []
      (term_closure D start source
        (fun _ => Formula.truth)) := by
  apply P.term_closure_derives
    start hSource
  · intro index hLower hUpper formula hFormula
    cases hFormula
  · exact Derives.truth_intro

/-- 空上下文中，每个 admissible 参数表都具有完整的递归图见证树。 -/
theorem terms_closure_truth
    (P : GraphPresentation D) (start : Nat)
    {sources : List (Term σ)}
    {sorts : List σ.SortSymbol}
    (hSources :
      ArgsAdmissible sources sorts) :
    Derives P.theory []
      (terms_closure D start sources
        (fun _ => Formula.truth)) := by
  apply P.terms_closure_derives
    start hSources
  · intro index hLower hUpper formula hFormula
    cases hFormula
  · exact Derives.truth_intro

/-- 空上下文中，每个 admissible 项都具有编译器布局的扁平图见证。 -/
theorem term_flat_truth
    (P : GraphPresentation D) (start : Nat)
    {source : Term σ} {sort : σ.SortSymbol}
    (hSource : Term.Admissible source sort) :
    Derives P.theory []
      (term_flat_closure D start source
        (fun _ => Formula.truth)) := by
  apply P.term_flat_derives
    start hSource
  · intro index hLower hUpper formula hFormula
    cases hFormula
  · intro value hValue
    exact Formula.Admissible.truth
  · exact Derives.truth_intro

/-- 空上下文中，每个 admissible 参数表都具有编译器布局的扁平图见证。 -/
theorem terms_flat_truth
    (P : GraphPresentation D) (start : Nat)
    {sources : List (Term σ)}
    {sorts : List σ.SortSymbol}
    (hSources : ArgsAdmissible sources sorts) :
    Derives P.theory []
      (terms_flat_closure D start sources
        (fun _ => Formula.truth)) := by
  apply P.terms_flat_derives
    start hSources
  · intro index hLower hUpper formula hFormula
    cases hFormula
  · intro values hValues
    exact Formula.Admissible.truth
  · exact Derives.truth_intro

/-- 参数编译器生成的全部条件在其连续见证闭包下可同时满足。 -/
theorem terms_conditions_truth
    (P : GraphPresentation D) (start : Nat)
    {sources : List (Term σ)}
    {sorts : List σ.SortSymbol}
    (hSources : ArgsAdmissible sources sorts) :
    Derives P.theory []
      (close_witnesses_from D.sort start
        ((terms D start sources).next - start)
        (condition_conjunction
          (terms D start sources).conditions
          Formula.truth)) := by
  simpa [terms_flat_closure] using
    P.terms_flat_truth start hSources

/--
从零开始编译时，扁平参数见证退化为公共原子编译器使用的 `close_witnesses` 表示。
-/
theorem terms_conditions_closed
    (P : GraphPresentation D)
    {sources : List (Term σ)}
    {sorts : List σ.SortSymbol}
    (hSources : ArgsAdmissible sources sorts) :
    Derives P.theory []
      (close_witnesses D.sort
        (terms D 0 sources).next
        (condition_conjunction
          (terms D 0 sources).conditions
          Formula.truth)) := by
  simpa [close_witnesses_from_zero_start] using
    P.terms_conditions_truth 0 hSources

end GraphPresentation

end FunctionGraphElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
