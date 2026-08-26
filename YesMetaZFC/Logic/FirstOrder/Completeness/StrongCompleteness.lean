import YesMetaZFC.Logic.FirstOrder.Completeness.TruthLemma
import YesMetaZFC.Logic.FirstOrder.Completeness.Schedule
/-!
# 一阶 Henkin 强完备性
本模块把 seeded Henkin 完成、典范项模型和 truth lemma 收束为最终语义接口。
公平调度仍然显式传入；泛型签名并未被伪设为可数。
典范项域位于 `Type (max u v)`，因此泛型强完备性定理对应
`Theory.SemanticallyEntails.{u, v, w, max u v}`。对于集合论等 `Type 0`
签名，这正好退化为项目常用的 universe-0 语义蕴涵。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Completeness
namespace Henkin
universe u v w
namespace CanonicalModel
/-- 任意 Henkin 完成结果的典范环境都满足原背景理论。 -/
theorem models_background {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {background : Background T} (result : Result background) :
    Theory.Models T (canonical_env result) := by
  intro formula hFormula
  exact (truth_lemma result formula (background.admissible formula hFormula)).mpr (result.contains_background hFormula)
end CanonicalModel
namespace Construction
noncomputable section
/-- 从空候选开始完成背景理论。 -/
def background_result {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} (background : Background T) (schedule : Schedule σ) :
    Result background :=
  result (Stage.initial background) schedule
/-- 从单公式反例种子开始完成背景理论。 -/
def refutation_result {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} (background : Background T) (schedule : Schedule σ) (formula : Formula σ) (hFormula : Formula.Admissible formula)
    (hNotDerives : ¬ Derives T [] formula) :
    Result background :=
  result (Stage.refutation_seed background formula hFormula hNotDerives)
    schedule
/-- 反例完成结果保留种子中的目标否定。 -/
theorem refutation_result_contains_neg {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} (background : Background T) (schedule : Schedule σ) (formula : Formula σ) (hFormula : Formula.Admissible formula)
    (hNotDerives : ¬ Derives T [] formula) : (refutation_result background schedule formula hFormula hNotDerives).candidate (Formula.neg formula) := by
  change
    candidate (Stage.refutation_seed background formula hFormula hNotDerives)
      schedule (Formula.neg formula)
  exact candidate_of_initial (by
    simp [Stage.refutation_seed, Stage.seed])
end
end Construction
/-- 一致句子理论在公平调度下具有典范项模型。 -/
theorem exists_model_of_background {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} (background : Background T) (schedule : Schedule σ) :
    ∃ (M : Structure.{u, v, w, max u v} σ), ∃ env : Env M,
      Theory.Models T env := by
  let result := Construction.background_result background schedule
  exact
    ⟨CanonicalModel.model result,
      CanonicalModel.canonical_env result,
      CanonicalModel.models_background result⟩
/--
若 admissible 公式不可由背景理论推出，则 seeded 典范模型给出一个真实反模型。
-/
theorem exists_countermodel_of_not_derives {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} (background : Background T) (schedule : Schedule σ) (formula : Formula σ) (hFormula : Formula.Admissible formula)
    (hNotDerives : ¬ Derives T [] formula) :
    ∃ (M : Structure.{u, v, w, max u v} σ), ∃ env : Env M,
      Theory.Models T env ∧ ¬ Formula.satisfies env formula := by
  let result :=
    Construction.refutation_result
      background schedule formula hFormula hNotDerives
  have hModels :
      Theory.Models T (CanonicalModel.canonical_env result) :=
    CanonicalModel.models_background result
  have hNegCandidate :
      result.candidate (Formula.neg formula) := by
    exact
      Construction.refutation_result_contains_neg
        background schedule formula hFormula hNotDerives
  have hNegSatisfies :
      Formula.satisfies (CanonicalModel.canonical_env result) (Formula.neg formula) :=
    (CanonicalModel.truth_lemma result (Formula.neg formula) hFormula.neg).mpr
      hNegCandidate
  exact
    ⟨CanonicalModel.model result,
      CanonicalModel.canonical_env result,
      hModels,
      by simpa [Formula.satisfies] using hNegSatisfies⟩
/--
当前 LN 语法核的强完备性。
背景理论成员必须是 admissible 句子；目标只需 admissible，因而也覆盖带自由变量
的语义蕴涵。公平公式调度作为泛型签名上的显式可枚举性边界保留。
-/
theorem strong_completeness {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} (schedule : Schedule σ) (hAdmissible : Theory.Admissible T)
    (hSentence : ∀ formula, T formula → Formula.Sentence formula)
    {formula : Formula σ} (hFormula : Formula.Admissible formula) (hEntails :
      Theory.SemanticallyEntails.{u, v, w, max u v} T formula) :
    Derives T [] formula := by
  apply Classical.byContradiction
  intro hNotDerives
  have hConsistent : Derives.Consistent T [] := by
    intro hFalse
    exact hNotDerives (.falsumElim hFalse)
  let background : Background T := {
    admissible := hAdmissible
    sentence := hSentence
    consistent := hConsistent
  }
  rcases
      exists_countermodel_of_not_derives
        background schedule formula hFormula hNotDerives with
    ⟨M, env, hModels, hRefutes⟩
  exact hRefutes (hEntails env hModels)
/-- 空上下文推导给出对应 universe 上的语义蕴涵。 -/
theorem semantically_entails_of_derives {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {formula : Formula σ} (hDerives : Derives T [] formula) :
    Theory.SemanticallyEntails.{u, v, w, max u v} T formula := by
  intro M env hModels
  exact hDerives.sound env hModels (by
    intro assumption hAssumption
    cases hAssumption)
/-- 显式公平调度下，句子理论的语义蕴涵与空上下文推导等价。 -/
theorem semantically_entails_iff_derives {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} (schedule : Schedule σ) (hAdmissible : Theory.Admissible T)
    (hSentence : ∀ formula, T formula → Formula.Sentence formula)
    {formula : Formula σ} (hFormula : Formula.Admissible formula) :
    Theory.SemanticallyEntails.{u, v, w, max u v} T formula ↔
      Derives T [] formula := by
  constructor
  · exact strong_completeness schedule hAdmissible hSentence hFormula
  · exact semantically_entails_of_derives
/-- 显式公平调度下，句子理论一致当且仅当它具有典范 universe 中的模型。 -/
theorem consistent_iff_exists_model {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} (schedule : Schedule σ) (hAdmissible : Theory.Admissible T)
    (hSentence : ∀ formula, T formula → Formula.Sentence formula) :
    Derives.Consistent T [] ↔
      ∃ (M : Structure.{u, v, w, max u v} σ), ∃ env : Env M,
        Theory.Models T env := by
  constructor
  · intro hConsistent
    exact
      exists_model_of_background
        {
          admissible := hAdmissible
          sentence := hSentence
          consistent := hConsistent
        }
        schedule
  · rintro ⟨M, env, hModels⟩ hFalse
    have hSatisfiesFalse :=
      hFalse.sound env hModels (by
        intro formula hFormula
        cases hFormula)
    simp [Formula.satisfies] at hSatisfiesFalse
end Henkin
end Completeness
end FirstOrder
end Logic
end YesMetaZFC
