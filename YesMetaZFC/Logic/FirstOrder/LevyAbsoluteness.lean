import YesMetaZFC.Logic.FirstOrder.LevyHierarchy
import YesMetaZFC.Logic.Semantics
/-!
# 相对 Lévy 层级的结构间绝对性
本模块给出一阶结构嵌入下的通用传递定理：
* 相对 `Delta0` 公式双向绝对；
* 相对 `Sigma1` 公式向上绝对；
* 相对 `Pi1` 公式向下绝对。
与纯句法的 `LevyHierarchy` 分层不同，这里显式记录函数、关系、sort 与有界关系
初段的保持性。扩展集合论语言后续只需为自己的标准对象嵌入实现这一份合同，
不需要针对证明码公式重新展开量词归纳。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
universe u v w x y
namespace Formula
/--
保持相对 Lévy 语义的结构嵌入。
`bounded_preimage` 是传递性条件的抽象形式：目标结构中属于某个源对象像的有界
元素，仍来自源结构。它正好是有界量词双向绝对所需、而普通一阶嵌入不提供的字段。
-/
structure LevyEmbedding
    {σ : Signature.{u, v, w}} (bound : LevyBound σ) (source : Structure.{u, v, w, x} σ) (target : Structure.{u, v, w, y} σ) where
  map : source.Domain → target.Domain
  map_injective : Function.Injective map
  sort_iff :
    ∀ sort value,
      source.sortInterp sort value ↔
        target.sortInterp sort (map value)
  function_eq :
    ∀ function arguments,
      map (source.funcInterp function arguments) =
        target.funcInterp function (arguments.map map)
  relation_iff :
    ∀ relation arguments,
      source.relInterp relation arguments ↔
        target.relInterp relation (arguments.map map)
  bounded_preimage :
    ∀ boundValue targetValue,
      target.sortInterp bound.sort targetValue →
      target.relInterp bound.relation
        [targetValue, map boundValue] →
      ∃ sourceValue,
        source.sortInterp bound.sort sourceValue ∧
          map sourceValue = targetValue
namespace LevyEmbedding
/-- 沿 Lévy 嵌入逐点提升变量环境。 -/
def map_env
    {σ : Signature.{u, v, w}}
    {bound : LevyBound σ}
    {source : Structure.{u, v, w, x} σ}
    {target : Structure.{u, v, w, y} σ} (embedding : LevyEmbedding bound source target) (env : Env source) :
    Env target where
  boundVal sort index :=
    embedding.map (env.boundVal sort index)
  freeVal sort id :=
    embedding.map (env.freeVal sort id)
  boundSort sort index := (embedding.sort_iff sort (env.boundVal sort index)).mp (env.boundSort sort index)
  freeSort sort id := (embedding.sort_iff sort (env.freeVal sort id)).mp (env.freeSort sort id)
/-- 环境提升与压入一个源对象交换。 -/
theorem map_env_pushBound
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {bound : LevyBound σ}
    {source : Structure.{u, v, w, x} σ}
    {target : Structure.{u, v, w, y} σ} (embedding : LevyEmbedding bound source target) (env : Env source) (sort : σ.SortSymbol) (value : source.Domain)
    (hValue : source.sortInterp sort value) :
    embedding.map_env (env.pushBound sort value hValue) = (embedding.map_env env).pushBound
        sort (embedding.map value) ((embedding.sort_iff sort value).mp hValue) := by
  rw [Env.mk.injEq]
  constructor
  · funext targetSort index
    by_cases hSort : targetSort = sort
    · subst targetSort
      cases index <;> simp [map_env, Env.pushBound]
    · simp [map_env, Env.pushBound, hSort]
  · rfl
/-- 项解释与 Lévy 嵌入交换。 -/
theorem term_eval_eq
    {σ : Signature.{u, v, w}}
    {bound : LevyBound σ}
    {source : Structure.{u, v, w, x} σ}
    {target : Structure.{u, v, w, y} σ} (embedding : LevyEmbedding bound source target) (env : Env source) :
    ∀ term : Term σ,
      embedding.map (Term.eval env term) =
        Term.eval (embedding.map_env env) term := by
  intro term
  refine Term.rec (motive_1 := fun term =>
      embedding.map (Term.eval env term) =
        Term.eval (embedding.map_env env) term) (motive_2 := fun arguments =>
      (arguments.map (Term.eval env)).map embedding.map =
        arguments.map (Term.eval (embedding.map_env env)))
    ?_ ?_ ?_ ?_ term
  · intro freeOrBound
    cases freeOrBound <;> simp [Term.eval, map_env]
  · intro function arguments hArguments
    simpa [Term.eval] using (embedding.function_eq function (arguments.map (Term.eval env))).trans (congrArg (target.funcInterp function) hArguments)
  · rfl
  · intro head tail hHead hTail
    simp only [List.map_cons]
    rw [hHead, hTail]
/-- 参数列表解释与 Lévy 嵌入交换。 -/
theorem term_list_eval_eq
    {σ : Signature.{u, v, w}}
    {bound : LevyBound σ}
    {source : Structure.{u, v, w, x} σ}
    {target : Structure.{u, v, w, y} σ} (embedding : LevyEmbedding bound source target) (env : Env source) :
    ∀ arguments : List (Term σ), (arguments.map (Term.eval env)).map embedding.map =
        arguments.map (Term.eval (embedding.map_env env)) := by
  intro arguments
  induction arguments with
  | nil =>
      rfl
  | cons head tail ih =>
      simp only [List.map_cons]
      rw [embedding.term_eval_eq env head, ih]
/-- 压栈环境中的同 sort 零号 bound 变量求值为刚压入的对象。 -/
@[simp]
theorem term_eval_pushBound_bvar_zero
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {model : Structure.{u, v, w, x} σ} (env : Env model) (sort : σ.SortSymbol) (value : model.Domain) (hValue : model.sortInterp sort value) :
    Term.eval (env.pushBound sort value hValue) (.var (.bvar sort 0) : Term σ) =
      value := by
  simp [Term.eval, Env.pushBound]
mutual
  /--
  不使用新 binder 顶层变量的项，其解释不依赖压入的具体值。
  -/
  theorem _root_.YesMetaZFC.Logic.FirstOrder.Term.BoundFreeAt.eval_pushBound_eq
      {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
      {model : Structure.{u, v, w, x} σ}
      {sort : σ.SortSymbol} {term : Term σ} (hTerm : Term.BoundFreeAt sort 0 term) (env : Env model) (left right : model.Domain)
      (hLeft : model.sortInterp sort left) (hRight : model.sortInterp sort right) :
      Term.eval (env.pushBound sort left hLeft) term =
        Term.eval (env.pushBound sort right hRight) term := by
    cases hTerm with
    | bvar variableSort index hDifferent =>
        rcases hDifferent with hSort | hIndex
        · simp [Term.eval, Env.pushBound, hSort]
        · cases index with
          | zero =>
              exact (hIndex rfl).elim
          | succ previous =>
              simp [Term.eval, Env.pushBound]
    | fvar =>
        simp [Term.eval, Env.pushBound]
    | app function hArguments =>
        simpa only [Term.eval] using
          congrArg (model.funcInterp function) (hArguments.eval_pushBound_eq
              env left right hLeft hRight)
  /-- `eval_pushBound_eq` 的参数列表版本。 -/
  theorem _root_.YesMetaZFC.Logic.FirstOrder.Term.ArgsBoundFreeAt.eval_pushBound_eq
      {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
      {model : Structure.{u, v, w, x} σ}
      {sort : σ.SortSymbol} {arguments : List (Term σ)} (hArguments : Term.ArgsBoundFreeAt sort 0 arguments) (env : Env model) (left right : model.Domain)
      (hLeft : model.sortInterp sort left) (hRight : model.sortInterp sort right) :
      arguments.map (Term.eval (env.pushBound sort left hLeft)) =
        arguments.map (Term.eval (env.pushBound sort right hRight)) := by
    cases hArguments with
    | nil =>
        rfl
    | cons hHead hTail =>
        simp only [List.map_cons]
        rw [hHead.eval_pushBound_eq
          env left right hLeft hRight]
        rw [hTail.eval_pushBound_eq
          env left right hLeft hRight]
end
/-- 映入目标结构后，源环境中的有界集合项取得对应的目标值。 -/
private theorem bounded_term_eval_eq
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {bound : LevyBound σ}
    {source : Structure.{u, v, w, x} σ}
    {target : Structure.{u, v, w, y} σ} (embedding : LevyEmbedding bound source target) (env : Env source) (setTerm : Term σ)
    (hSet : Term.BoundFreeAt bound.sort 0 setTerm) (sourceValue : source.Domain) (hSourceValue :
      source.sortInterp bound.sort sourceValue) (targetValue : target.Domain) (hTargetValue :
      target.sortInterp bound.sort targetValue) :
    Term.eval ((embedding.map_env env).pushBound
          bound.sort targetValue hTargetValue)
        setTerm =
      embedding.map (Term.eval (env.pushBound bound.sort sourceValue hSourceValue)
          setTerm) := by
  let mappedSourceProof :
      target.sortInterp bound.sort (embedding.map sourceValue) := (embedding.sort_iff bound.sort sourceValue).mp
      hSourceValue
  calc
    Term.eval ((embedding.map_env env).pushBound
          bound.sort targetValue hTargetValue)
        setTerm =
      Term.eval ((embedding.map_env env).pushBound
          bound.sort (embedding.map sourceValue)
          mappedSourceProof)
        setTerm :=
      hSet.eval_pushBound_eq (embedding.map_env env)
        targetValue (embedding.map sourceValue)
        hTargetValue mappedSourceProof
    _ =
      Term.eval (embedding.map_env (env.pushBound
            bound.sort sourceValue hSourceValue))
        setTerm := by
      rw [embedding.map_env_pushBound]
    _ =
      embedding.map (Term.eval (env.pushBound bound.sort sourceValue hSourceValue)
          setTerm) := (embedding.term_eval_eq (env.pushBound bound.sort sourceValue hSourceValue)
        setTerm).symm

/--
正位置成员 guard 从公式体的满足性中恢复见证的显式集合界。
-/
theorem MembershipGuard.mem_of_satisfies
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {bound : LevyBound σ}
    {model : Structure.{u, v, w, x} σ}
    {setTerm : Term σ} {formula : Formula σ}
    (hGuard : MembershipGuard bound setTerm formula)
    (env : Env model)
    (hFormula : Formula.satisfies env formula) :
    model.relInterp bound.relation
      [Term.eval env (.var (.bvar bound.sort 0)),
        Term.eval env setTerm] := by
  induction hGuard generalizing env with
  | membership =>
      simpa only [Formula.satisfies, List.map_cons,
        List.map_nil] using hFormula
  | conj_left hLeft ih =>
      exact ih env hFormula.1
  | conj_right hRight ih =>
      exact ih env hFormula.2

/-- 相对 `Delta0` 公式在 Lévy 嵌入两侧绝对。 -/
theorem delta0_absolute
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {bound : LevyBound σ}
    {source : Structure.{u, v, w, x} σ}
    {target : Structure.{u, v, w, y} σ} (embedding : LevyEmbedding bound source target)
    {formula : Formula σ} (hFormula : IsDelta0 bound formula) :
    ∀ env : Env source,
      Formula.satisfies env formula ↔
        Formula.satisfies (embedding.map_env env) formula := by
  induction hFormula with
  | falsum =>
      intro env
      rfl
  | truth =>
      intro env
      rfl
  | rel relation arguments =>
      intro env
      simp only [Formula.satisfies]
      rw [← embedding.term_list_eval_eq env arguments]
      exact embedding.relation_iff relation (arguments.map (Term.eval env))
  | equal left right =>
      intro env
      simp only [Formula.satisfies]
      constructor
      · intro hEquality
        rw [← embedding.term_eval_eq env left,
          ← embedding.term_eval_eq env right]
        exact congrArg embedding.map hEquality
      · intro hEquality
        apply embedding.map_injective
        simpa only [embedding.term_eval_eq] using hEquality
  | neg hBody ih =>
      intro env
      simpa only [Formula.satisfies] using not_congr (ih env)
  | conj hLeft hRight ihLeft ihRight =>
      intro env
      simp only [Formula.satisfies, ihLeft env, ihRight env]
  | disj hLeft hRight ihLeft ihRight =>
      intro env
      simp only [Formula.satisfies, ihLeft env, ihRight env]
  | imp hLeft hRight ihLeft ihRight =>
      intro env
      simp only [Formula.satisfies, ihLeft env, ihRight env]
  | iff hLeft hRight ihLeft ihRight =>
      intro env
      simp only [Formula.satisfies, ihLeft env, ihRight env]
  | bounded_forall setTerm body hSet hBody ih =>
      intro env
      simp only [Formula.satisfies, List.map_cons, List.map_nil,
        term_eval_pushBound_bvar_zero]
      constructor
      · intro hSource targetValue hTargetSort hTargetMember
        rcases source.sortNonempty bound.sort with
          ⟨anchor, hAnchor⟩
        let sourceBound :=
          Term.eval (env.pushBound bound.sort anchor hAnchor)
            setTerm
        have hTargetBound :
            Term.eval ((embedding.map_env env).pushBound
                  bound.sort targetValue hTargetSort)
                setTerm =
              embedding.map sourceBound := by
          simpa [sourceBound] using
            bounded_term_eval_eq embedding env setTerm hSet
              anchor hAnchor targetValue hTargetSort
        have hTargetMember' :
            target.relInterp bound.relation
              [targetValue, embedding.map sourceBound] := by
          simpa [hTargetBound] using hTargetMember
        rcases embedding.bounded_preimage
            sourceBound targetValue hTargetSort hTargetMember' with
          ⟨sourceValue, hSourceSort, hMap⟩
        have hSourceBound :
            Term.eval (env.pushBound
                  bound.sort sourceValue hSourceSort)
                setTerm =
              sourceBound := by
          simpa [sourceBound] using
            hSet.eval_pushBound_eq env
              sourceValue anchor hSourceSort hAnchor
        have hSourceMember :
            source.relInterp bound.relation
              [sourceValue,
                Term.eval (env.pushBound
                    bound.sort sourceValue hSourceSort)
                  setTerm] := by
          rw [hSourceBound]
          exact (embedding.relation_iff bound.relation
              [sourceValue, sourceBound]).mpr (by simpa [hMap] using hTargetMember')
        have hSourceBody :=
          hSource sourceValue hSourceSort hSourceMember
        have hTargetBody := (ih (env.pushBound
              bound.sort sourceValue hSourceSort)).mp
            hSourceBody
        simpa [embedding.map_env_pushBound, hMap] using hTargetBody
      · intro hTarget sourceValue hSourceSort hSourceMember
        let hMappedSort := (embedding.sort_iff bound.sort sourceValue).mp
            hSourceSort
        have hTargetMember :
            target.relInterp bound.relation
              [embedding.map sourceValue,
                Term.eval ((embedding.map_env env).pushBound
                    bound.sort (embedding.map sourceValue)
                    hMappedSort)
                  setTerm] := by
          have hSourceTarget := (embedding.relation_iff bound.relation
              [sourceValue,
                Term.eval (env.pushBound
                    bound.sort sourceValue hSourceSort)
                  setTerm]).mp hSourceMember
          simpa [embedding.map_env_pushBound,
            embedding.term_eval_eq] using hSourceTarget
        have hTargetBody :=
          hTarget (embedding.map sourceValue)
            hMappedSort hTargetMember
        have hSourceBody := (ih (env.pushBound
              bound.sort sourceValue hSourceSort)).mpr (by
              simpa [embedding.map_env_pushBound] using
                hTargetBody)
        exact hSourceBody
  | bounded_exists setTerm body hSet hBody ih =>
      intro env
      simp only [Formula.satisfies, List.map_cons, List.map_nil,
        term_eval_pushBound_bvar_zero]
      constructor
      · rintro ⟨sourceValue, hSourceSort,
          hSourceMember, hSourceBody⟩
        let hMappedSort := (embedding.sort_iff bound.sort sourceValue).mp
            hSourceSort
        refine
          ⟨embedding.map sourceValue, hMappedSort, ?_, ?_⟩
        · have hSourceTarget := (embedding.relation_iff bound.relation
              [sourceValue,
                Term.eval (env.pushBound
                    bound.sort sourceValue hSourceSort)
                  setTerm]).mp hSourceMember
          simpa [embedding.map_env_pushBound,
            embedding.term_eval_eq] using hSourceTarget
        · have hTargetBody := (ih (env.pushBound
                bound.sort sourceValue hSourceSort)).mp
              hSourceBody
          simpa [embedding.map_env_pushBound] using hTargetBody
      · rintro ⟨targetValue, hTargetSort,
          hTargetMember, hTargetBody⟩
        rcases source.sortNonempty bound.sort with
          ⟨anchor, hAnchor⟩
        let sourceBound :=
          Term.eval (env.pushBound bound.sort anchor hAnchor)
            setTerm
        have hTargetBound :
            Term.eval ((embedding.map_env env).pushBound
                  bound.sort targetValue hTargetSort)
                setTerm =
              embedding.map sourceBound := by
          simpa [sourceBound] using
            bounded_term_eval_eq embedding env setTerm hSet
              anchor hAnchor targetValue hTargetSort
        have hTargetMember' :
            target.relInterp bound.relation
              [targetValue, embedding.map sourceBound] := by
          simpa [hTargetBound] using hTargetMember
        rcases embedding.bounded_preimage
            sourceBound targetValue hTargetSort hTargetMember' with
          ⟨sourceValue, hSourceSort, hMap⟩
        have hSourceBound :
            Term.eval (env.pushBound
                  bound.sort sourceValue hSourceSort)
                setTerm =
              sourceBound := by
          simpa [sourceBound] using
            hSet.eval_pushBound_eq env
              sourceValue anchor hSourceSort hAnchor
        refine ⟨sourceValue, hSourceSort, ?_, ?_⟩
        · rw [hSourceBound]
          exact (embedding.relation_iff bound.relation
              [sourceValue, sourceBound]).mpr (by simpa [hMap] using hTargetMember')
        · apply (ih (env.pushBound
                bound.sort sourceValue hSourceSort)).mpr
          simpa [embedding.map_env_pushBound, hMap] using
            hTargetBody
  | guarded_exists setTerm body hSet hBody hGuard ih =>
      intro env
      simp only [Formula.satisfies]
      constructor
      · rintro ⟨sourceValue, hSourceSort, hSourceBody⟩
        let hTargetSort :=
          (embedding.sort_iff bound.sort sourceValue).mp
            hSourceSort
        refine
          ⟨embedding.map sourceValue, hTargetSort, ?_⟩
        have hTargetBody :=
          (ih (env.pushBound
              bound.sort sourceValue hSourceSort)).mp
            hSourceBody
        simpa [embedding.map_env_pushBound] using
          hTargetBody
      · rintro ⟨targetValue, hTargetSort, hTargetBody⟩
        rcases source.sortNonempty bound.sort with
          ⟨anchor, hAnchor⟩
        let sourceBound :=
          Term.eval
            (env.pushBound bound.sort anchor hAnchor)
            setTerm
        have hTargetBound :
            Term.eval
                ((embedding.map_env env).pushBound
                  bound.sort targetValue hTargetSort)
                setTerm =
              embedding.map sourceBound := by
          simpa [sourceBound] using
            bounded_term_eval_eq embedding env setTerm hSet
              anchor hAnchor targetValue hTargetSort
        have hTargetMember :
            target.relInterp bound.relation
              [targetValue, embedding.map sourceBound] := by
          have hGuarded :=
            MembershipGuard.mem_of_satisfies hGuard
              ((embedding.map_env env).pushBound
                bound.sort targetValue hTargetSort)
              hTargetBody
          simpa [hTargetBound,
            term_eval_pushBound_bvar_zero] using hGuarded
        rcases embedding.bounded_preimage
            sourceBound targetValue hTargetSort hTargetMember with
          ⟨sourceValue, hSourceSort, hMap⟩
        refine ⟨sourceValue, hSourceSort, ?_⟩
        apply (ih (env.pushBound
            bound.sort sourceValue hSourceSort)).mpr
        simpa [embedding.map_env_pushBound, hMap] using
          hTargetBody
mutual
  /-- 相对 `Sigma1` 公式沿 Lévy 嵌入向上绝对。 -/
  theorem sigma1_upward_absolute
      {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
      {bound : LevyBound σ}
      {source : Structure.{u, v, w, x} σ}
      {target : Structure.{u, v, w, y} σ} (embedding : LevyEmbedding bound source target)
      {formula : Formula σ} (hFormula : IsSigma1 bound formula) :
      ∀ env : Env source,
        Formula.satisfies env formula →
          Formula.satisfies (embedding.map_env env) formula := by
    cases hFormula with
    | delta0 hDelta =>
        intro env hSource
        exact (delta0_absolute embedding hDelta env).mp hSource
    | neg hBody =>
        intro env hSource hTarget
        exact hSource (pi1_downward_absolute embedding hBody env hTarget)
    | conj hLeft hRight =>
        intro env hSource
        exact
          ⟨sigma1_upward_absolute embedding hLeft env hSource.1,
            sigma1_upward_absolute embedding hRight env hSource.2⟩
    | disj hLeft hRight =>
        intro env hSource
        rcases hSource with hSource | hSource
        · exact Or.inl (sigma1_upward_absolute embedding hLeft env hSource)
        · exact Or.inr (sigma1_upward_absolute embedding hRight env hSource)
    | imp hLeft hRight =>
        intro env hSource hTargetLeft
        exact
          sigma1_upward_absolute embedding hRight env (hSource (pi1_downward_absolute embedding hLeft env
                hTargetLeft))
    | existsE sort hBody =>
        intro env hSource
        simp only [Formula.satisfies] at hSource ⊢
        rcases hSource with ⟨sourceValue, hSourceSort, hSourceBody⟩
        let hTargetSort := (embedding.sort_iff sort sourceValue).mp hSourceSort
        refine ⟨embedding.map sourceValue, hTargetSort, ?_⟩
        simpa [embedding.map_env_pushBound] using
          sigma1_upward_absolute embedding hBody (env.pushBound sort sourceValue hSourceSort)
            hSourceBody
    | bounded_forall setTerm body hSet hBody =>
        intro env
        simp only [Formula.satisfies, List.map_cons, List.map_nil,
          term_eval_pushBound_bvar_zero]
        intro hSource targetValue hTargetSort hTargetMember
        rcases source.sortNonempty bound.sort with
          ⟨anchor, hAnchor⟩
        let sourceBound :=
          Term.eval (env.pushBound bound.sort anchor hAnchor)
            setTerm
        have hTargetBound :
            Term.eval ((embedding.map_env env).pushBound
                  bound.sort targetValue hTargetSort)
                setTerm =
              embedding.map sourceBound := by
          simpa [sourceBound] using
            bounded_term_eval_eq embedding env setTerm hSet
              anchor hAnchor targetValue hTargetSort
        have hTargetMember' :
            target.relInterp bound.relation
              [targetValue, embedding.map sourceBound] := by
          simpa [hTargetBound] using hTargetMember
        rcases embedding.bounded_preimage
            sourceBound targetValue hTargetSort hTargetMember' with
          ⟨sourceValue, hSourceSort, hMap⟩
        have hSourceBound :
            Term.eval (env.pushBound
                  bound.sort sourceValue hSourceSort)
                setTerm =
              sourceBound := by
          simpa [sourceBound] using
            hSet.eval_pushBound_eq env
              sourceValue anchor hSourceSort hAnchor
        have hSourceMember :
            source.relInterp bound.relation
              [sourceValue,
                Term.eval (env.pushBound
                    bound.sort sourceValue hSourceSort)
                  setTerm] := by
          rw [hSourceBound]
          exact (embedding.relation_iff bound.relation
              [sourceValue, sourceBound]).mpr (by simpa [hMap] using hTargetMember')
        have hSourceBody :=
          hSource sourceValue hSourceSort hSourceMember
        have hTargetBody :=
          sigma1_upward_absolute embedding hBody (env.pushBound
              bound.sort sourceValue hSourceSort)
            hSourceBody
        simpa [embedding.map_env_pushBound, hMap] using hTargetBody
    | bounded_exists setTerm body hSet hBody =>
        intro env
        simp only [Formula.satisfies, List.map_cons, List.map_nil,
          term_eval_pushBound_bvar_zero]
        intro hSource
        rcases hSource with
          ⟨sourceValue, hSourceSort, hSourceMember, hSourceBody⟩
        let hTargetSort := (embedding.sort_iff bound.sort sourceValue).mp
            hSourceSort
        refine
          ⟨embedding.map sourceValue, hTargetSort, ?_, ?_⟩
        · have hSourceTarget := (embedding.relation_iff bound.relation
              [sourceValue,
                Term.eval (env.pushBound
                    bound.sort sourceValue hSourceSort)
                  setTerm]).mp hSourceMember
          simpa [embedding.map_env_pushBound,
            embedding.term_eval_eq] using hSourceTarget
        · have hTargetBody :=
            sigma1_upward_absolute embedding hBody (env.pushBound
                bound.sort sourceValue hSourceSort)
              hSourceBody
          simpa [embedding.map_env_pushBound] using hTargetBody
  /-- 相对 `Pi1` 公式沿 Lévy 嵌入向下绝对。 -/
  theorem pi1_downward_absolute
      {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
      {bound : LevyBound σ}
      {source : Structure.{u, v, w, x} σ}
      {target : Structure.{u, v, w, y} σ} (embedding : LevyEmbedding bound source target)
      {formula : Formula σ} (hFormula : IsPi1 bound formula) :
      ∀ env : Env source,
        Formula.satisfies (embedding.map_env env) formula →
          Formula.satisfies env formula := by
    cases hFormula with
    | delta0 hDelta =>
        intro env hTarget
        exact (delta0_absolute embedding hDelta env).mpr hTarget
    | neg hBody =>
        intro env hTarget hSource
        exact hTarget (sigma1_upward_absolute embedding hBody env hSource)
    | conj hLeft hRight =>
        intro env hTarget
        exact
          ⟨pi1_downward_absolute embedding hLeft env hTarget.1,
            pi1_downward_absolute embedding hRight env hTarget.2⟩
    | disj hLeft hRight =>
        intro env hTarget
        rcases hTarget with hTarget | hTarget
        · exact Or.inl (pi1_downward_absolute embedding hLeft env hTarget)
        · exact Or.inr (pi1_downward_absolute embedding hRight env hTarget)
    | imp hLeft hRight =>
        intro env hTarget hSourceLeft
        exact
          pi1_downward_absolute embedding hRight env (hTarget (sigma1_upward_absolute embedding hLeft env
                hSourceLeft))
    | forallE sort hBody =>
        intro env hTarget sourceValue hSourceSort
        simp only [Formula.satisfies] at hTarget ⊢
        let hTargetSort := (embedding.sort_iff sort sourceValue).mp hSourceSort
        apply pi1_downward_absolute embedding hBody (env.pushBound sort sourceValue hSourceSort)
        simpa [embedding.map_env_pushBound] using
          hTarget (embedding.map sourceValue) hTargetSort
    | bounded_forall setTerm body hSet hBody =>
        intro env
        simp only [Formula.satisfies, List.map_cons, List.map_nil,
          term_eval_pushBound_bvar_zero]
        intro hTarget sourceValue hSourceSort hSourceMember
        let hTargetSort := (embedding.sort_iff bound.sort sourceValue).mp
            hSourceSort
        have hTargetMember :
            target.relInterp bound.relation
              [embedding.map sourceValue,
                Term.eval ((embedding.map_env env).pushBound
                    bound.sort (embedding.map sourceValue)
                    hTargetSort)
                  setTerm] := by
          have hSourceTarget := (embedding.relation_iff bound.relation
              [sourceValue,
                Term.eval (env.pushBound
                    bound.sort sourceValue hSourceSort)
                  setTerm]).mp hSourceMember
          simpa [embedding.map_env_pushBound,
            embedding.term_eval_eq] using hSourceTarget
        have hTargetBody :=
          hTarget (embedding.map sourceValue)
            hTargetSort hTargetMember
        apply pi1_downward_absolute embedding hBody (env.pushBound bound.sort sourceValue hSourceSort)
        simpa [embedding.map_env_pushBound] using hTargetBody
    | bounded_exists setTerm body hSet hBody =>
        intro env
        simp only [Formula.satisfies, List.map_cons, List.map_nil,
          term_eval_pushBound_bvar_zero]
        intro hTarget
        rcases hTarget with
          ⟨targetValue, hTargetSort, hTargetMember, hTargetBody⟩
        rcases source.sortNonempty bound.sort with
          ⟨anchor, hAnchor⟩
        let sourceBound :=
          Term.eval (env.pushBound bound.sort anchor hAnchor)
            setTerm
        have hTargetBound :
            Term.eval ((embedding.map_env env).pushBound
                  bound.sort targetValue hTargetSort)
                setTerm =
              embedding.map sourceBound := by
          simpa [sourceBound] using
            bounded_term_eval_eq embedding env setTerm hSet
              anchor hAnchor targetValue hTargetSort
        have hTargetMember' :
            target.relInterp bound.relation
              [targetValue, embedding.map sourceBound] := by
          simpa [hTargetBound] using hTargetMember
        rcases embedding.bounded_preimage
            sourceBound targetValue hTargetSort hTargetMember' with
          ⟨sourceValue, hSourceSort, hMap⟩
        have hSourceBound :
            Term.eval (env.pushBound
                  bound.sort sourceValue hSourceSort)
                setTerm =
              sourceBound := by
          simpa [sourceBound] using
            hSet.eval_pushBound_eq env
              sourceValue anchor hSourceSort hAnchor
        refine ⟨sourceValue, hSourceSort, ?_, ?_⟩
        · rw [hSourceBound]
          exact (embedding.relation_iff bound.relation
              [sourceValue, sourceBound]).mpr (by simpa [hMap] using hTargetMember')
        · apply pi1_downward_absolute embedding hBody (env.pushBound bound.sort sourceValue hSourceSort)
          simpa [embedding.map_env_pushBound, hMap] using
            hTargetBody
end
end LevyEmbedding
end Formula
end FirstOrder
end Logic
end YesMetaZFC
