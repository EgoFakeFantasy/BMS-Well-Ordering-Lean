import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FixedAxiomTable

/-!
# `ProofT` 的 schema verifier 插件

schema 插件只描述一个对象层证书分支及其句法可用性。插件列表统一负责有限析取、
成员注入、逐分支拒绝和闭项替换；理论 presentation 因而不再把 separation、
collection 或 replacement 的分支树写死在总 verifier 中。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-- 一个带自然数标签的外部 schema 生成器插件。 -/
structure SchemaGeneratorPlugin (Sentence : Type) where
  tag : Nat
  generate : Nat → Option Sentence

namespace SchemaGeneratorPlugin

/-- 按 schema 标签调度第一个匹配的外部生成器插件。 -/
def generate_list
    {Sentence : Type}
    (plugins : List (SchemaGeneratorPlugin Sentence))
    (tag payload : Nat) : Option Sentence :=
  match plugins with
  | [] => none
  | plugin :: rest =>
      if tag = plugin.tag then
        plugin.generate payload
      else
        generate_list rest tag payload

/-- 插件列表中任一成功生成都归约到某个实际启用的插件。 -/
theorem generate_list_sound
    {Sentence : Type}
    {P : Sentence → Prop}
    (plugins : List (SchemaGeneratorPlugin Sentence))
    (tag payload : Nat)
    {sentence : Sentence}
    (hPlugin :
      ∀ plugin, plugin ∈ plugins →
        plugin.generate payload = some sentence →
          P sentence)
    (hGenerate :
      generate_list plugins tag payload =
        some sentence) :
    P sentence := by
  induction plugins with
  | nil =>
      simp [generate_list] at hGenerate
  | cons plugin rest ih =>
      simp only [generate_list] at hGenerate
      split at hGenerate
      · exact hPlugin plugin (by simp) hGenerate
      · exact ih
          (fun member hMember =>
            hPlugin member (by simp [hMember]))
          hGenerate

/-- 成功分派可反演出实际命中的插件、标签等式与该插件的生成等式。 -/
theorem generate_list_some
    {Sentence : Type}
    (plugins : List (SchemaGeneratorPlugin Sentence))
    (tag payload : Nat)
    {sentence : Sentence}
    (hGenerate :
      generate_list plugins tag payload =
        some sentence) :
    ∃ plugin,
      plugin ∈ plugins ∧
      tag = plugin.tag ∧
      plugin.generate payload = some sentence := by
  induction plugins with
  | nil =>
      simp [generate_list] at hGenerate
  | cons plugin rest ih =>
      simp only [generate_list] at hGenerate
      split at hGenerate
      next hTag =>
        exact ⟨plugin, by simp, hTag, hGenerate⟩
      next hTag =>
        rcases ih hGenerate with
          ⟨member, hMember, hMemberTag, hMemberGenerate⟩
        exact
          ⟨member, (by simp [hMember]),
            hMemberTag, hMemberGenerate⟩

end SchemaGeneratorPlugin

/-- 一个可组合的对象层 schema verifier 分支。 -/
structure SchemaPlugin where
  tag : Nat
  condition_with_base :
    SetTerm → SetTerm → FreeVarId → SetFormula
  condition_admissible :
    ∀ formula certificate base,
      Term.Admissible formula SetSort.set →
      Term.Admissible certificate SetSort.set →
      Formula.Admissible
        (condition_with_base formula certificate base)

namespace SchemaPlugin

/-- schema 条件的有限见证闭包。列表顺序就是从外到内的存在量词顺序。 -/
def witness_closure
    (ids : List FreeVarId)
    (body : SetFormula) : SetFormula :=
  match ids with
  | [] => body
  | id :: rest =>
      ∃ₘ[SetSort.set, id], witness_closure rest body

/-- 带显式成员界的有限 witness 闭包。 -/
def bounded_witness_closure
    (bindings : List (FreeVarId × SetTerm))
    (body : SetFormula) : SetFormula :=
  match bindings with
  | [] => body
  | (id, bound) :: rest =>
      ∃ₘ[SetSort.set, id],
        (x#id ∈ₘ bound) ∧ₘ
          bounded_witness_closure rest body

/-- 每个 witness 的界项新鲜时，有界闭包保持 `Delta0`。 -/
theorem bounded_witness_closure_delta0
    (bindings : List (FreeVarId × SetTerm))
    (body : SetFormula)
    (hBoundFresh :
      ∀ binding, binding ∈ bindings →
        (SetSort.set, binding.1) ∉
          Term.freeSupport binding.2)
    (hBody : Formula.IsDelta0 set_levy_bound body) :
    Formula.IsDelta0 set_levy_bound
      (bounded_witness_closure bindings body) := by
  induction bindings with
  | nil =>
      simpa [bounded_witness_closure] using hBody
  | cons binding rest ih =>
      have hRest :
          Formula.IsDelta0 set_levy_bound
            (bounded_witness_closure rest body) :=
        ih (fun item hItem =>
          hBoundFresh item (by simp [hItem]))
      have hConj :
          Formula.IsDelta0 set_levy_bound
            ((x#binding.1 ∈ₘ binding.2) ∧ₘ
              bounded_witness_closure rest body) :=
        Formula.IsDelta0.conj
          (Formula.IsDelta0.rel
            RelationSymbol.membership
            [x#binding.1, binding.2])
          hRest
      simpa [bounded_witness_closure] using
        Formula.IsDelta0.guarded_exists_closeFreeAt
          binding.1 binding.2
          (hBoundFresh binding (by simp))
          hConj
          (Formula.FreeMembershipGuard.conj_left
            Formula.FreeMembershipGuard.membership)

/-- 有限见证闭包恰好删除列表中各 binder 的自由出现。 -/
theorem mem_freeSupport_witness_closure_iff
    (freeVariable : FreeVariable signature)
    (ids : List FreeVarId)
    (body : SetFormula) :
    freeVariable ∈
        Formula.freeSupport (witness_closure ids body) ↔
      freeVariable ∈ Formula.freeSupport body ∧
        ∀ id, id ∈ ids →
          freeVariable ≠ (SetSort.set, id) := by
  induction ids with
  | nil =>
      simp [witness_closure]
  | cons id rest ih =>
      simp only [witness_closure, Formula.freeSupport,
        Formula.mem_freeSupport_closeFreeAt_iff, ih,
        List.mem_cons]
      constructor
      · rintro ⟨⟨hBody, hRest⟩, hId⟩
        refine ⟨hBody, ?_⟩
        intro target hTarget
        rcases hTarget with rfl | hTarget
        · exact hId
        · exact hRest target hTarget
      · rintro ⟨hBody, hAll⟩
        exact
          ⟨⟨hBody, fun target hTarget =>
              hAll target (Or.inr hTarget)⟩,
            hAll id (Or.inl rfl)⟩

theorem witness_closure_admissible
    (ids : List FreeVarId)
    {body : SetFormula}
    (hBody : Formula.Admissible body) :
    Formula.Admissible (witness_closure ids body) := by
  induction ids with
  | nil =>
      simpa [witness_closure] using hBody
  | cons id rest ih =>
      simpa [witness_closure] using
        Formula.Admissible.exists_closeFreeAt
          SetSort.set id ih

/-- 有限见证闭包的合法性可反演回开放 body。 -/
theorem witness_closure_body_admissible
    (ids : List FreeVarId)
    {body : SetFormula}
    (hClosure :
      Formula.Admissible (witness_closure ids body)) :
    Formula.Admissible body := by
  induction ids with
  | nil =>
      simpa [witness_closure] using hClosure
  | cons id rest ih =>
      have hOpened :=
        Formula.Admissible.exists_openAt
          (term := (x#id : SetTerm))
          SetSort.set hClosure
          (set_variable_admissible id)
      apply ih
      simpa [witness_closure, Formula.openAt_closeFreeAt] using
        hOpened

/--
每个 witness 取其同名对象变量时，开放 body 的证明可直接封装为有限存在闭包。
该接口只处理 binder 样板；各 schema 的实质性组件仍须在 `hBody` 中给出。
-/
theorem witness_closure_intro_self
    {T : SetTheory}
    (ids : List FreeVarId)
    {body : SetFormula}
    (hBody : Derives T [] body) :
    Derives T [] (witness_closure ids body) := by
  induction ids with
  | nil =>
      simpa [witness_closure] using hBody
  | cons id rest ih =>
      nd_apply FirstOrder.Derives.exists_intro
        (term := (x#id : SetTerm))
      simpa [witness_closure,
        Formula.openAt_closeFreeAt_eq_substituteFree,
        Formula.substituteFree_self] using ih

/--
以一列闭项实例化 schema 的全部见证，并统一封装为有限存在闭包。

`assignments` 的顺序同时确定从外到内的存在量词顺序和逐次代入顺序；因此调用方只需
证明最终开放 body 的代入实例，不再逐层维护 `closeFreeAt` 与 substitution 的交换。
-/
theorem witness_closure_intro_assignments
    {T : SetTheory}
    (assignments : List (FreeVarId × SetTerm))
    (body : SetFormula)
    (hIds :
      (assignments.map (fun assignment => assignment.1)).Nodup)
    (hWitnessCheck :
      ∀ assignment, assignment ∈ assignments →
        Term.CheckCertificate assignment.2 SetSort.set)
    (hWitnessFree :
      ∀ assignment, assignment ∈ assignments →
        Term.freeSupport assignment.2 = [])
    (hInstance :
      Derives T []
        (Formula.substituteFreeAssignments
          SetSort.set assignments body)) :
    Derives T []
      (witness_closure
        (assignments.map (fun assignment => assignment.1))
        body) := by
  have hExists :=
    FirstOrder.Derives.exists_intro_substituted_assignments
      (T := T) (Γ := [])
      (sort := SetSort.set) assignments body
      hIds hWitnessCheck hWitnessFree hInstance
  have hShape :
      ∀ assignments : List (FreeVarId × SetTerm),
        Formula.existsFreeAssignments
            SetSort.set assignments body =
          witness_closure
            (assignments.map (fun assignment => assignment.1))
            body := by
    intro assignments'
    induction assignments' with
    | nil =>
        rfl
    | cons assignment assignments' ih =>
        simp only [Formula.existsFreeAssignments,
          List.map_cons, witness_closure]
        rw [ih]
  rw [← hShape assignments]
  exact hExists

/--
若宿主理论的公理都是句子，则开放 body 的统一否定可穿过一个 canonical
存在闭包。闭包自身消除了 eigenvariable，故无需额外的外部新鲜编号假设。
-/
theorem exists_closeFreeAt_neg_of_neg
    {T : SetTheory}
    (hTheorySentence :
      ∀ {formula}, T formula →
        Formula.freeSupport formula = [])
    (id : FreeVarId)
    (body : SetFormula)
    (hBody : Formula.Admissible body)
    (hNeg : Derives T [] (¬ₘ body)) :
    Derives T [] (
      ¬ₘ (∃ₘ[SetSort.set, id], body)) := by
  let condition : SetFormula :=
    ∃ₘ[SetSort.set, id], body
  have hCondition :
      Formula.Admissible condition := by
    simpa [condition] using
      Formula.Admissible.exists_closeFreeAt
        SetSort.set id hBody
  nd_apply FirstOrder.Derives.negIntro
    (T := T)
    (Γ := ([] : Context signature))
    (body := condition)
    (hBodyCheck :=
      Formula.check_admissible_complete hCondition)
  let Γ : Context signature := [condition]
  have hConditionAt :
      Γ ⊢ₘ[T] condition :=
    FirstOrder.Derives.assumption (by simp [Γ])
  nd_apply FirstOrder.Derives.exists_elim
    (T := T)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := id)
    (body := body)
    (conclusion := Formula.falsum)
    (hBodyCheck :=
      Formula.check_admissible_complete hBody)
  · intro formula hFormula
    rw [hTheorySentence hFormula]
    exact List.not_mem_nil
  · intro formula hFormula
    simp only [Γ, List.mem_singleton] at hFormula
    subst formula
    simpa [condition] using
      Formula.not_mem_freeSupport_closeFreeAt
        SetSort.set id 0 body
  · exact List.not_mem_nil
  · simpa [condition] using hConditionAt
  · exact FirstOrder.Derives.negElim
      (FirstOrder.Derives.assumption
        (Γ := body :: Γ) (by simp))
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := body :: Γ)
        (by simp) hNeg)

/-- 开放 body 的统一否定逐层提升为任意有限见证闭包的否定。 -/
theorem witness_closure_neg
    {T : SetTheory}
    (hTheorySentence :
      ∀ {formula}, T formula →
        Formula.freeSupport formula = [])
    (ids : List FreeVarId)
    {body : SetFormula}
    (hBody : Formula.Admissible body)
    (hNeg : Derives T [] (¬ₘ body)) :
    Derives T [] (¬ₘ witness_closure ids body) := by
  induction ids with
  | nil =>
      simpa [witness_closure] using hNeg
  | cons id rest ih =>
      have hRest :
          Formula.Admissible
            (witness_closure rest body) :=
        witness_closure_admissible rest hBody
      simpa [witness_closure] using
        exists_closeFreeAt_neg_of_neg
          hTheorySentence id
          (witness_closure rest body)
          hRest ih

/--
插件列表的右结合有限析取。

单元素列表不追加伪分支，因此 `[separation, collection]` 约化为仓库原先使用的
`separation ∨ collection` 形状。
-/
def condition_list
    (plugins : List SchemaPlugin)
    (formula certificate : SetTerm)
    (base : FreeVarId) : SetFormula :=
  match plugins with
  | [] => Formula.falsum
  | [plugin] =>
      plugin.condition_with_base formula certificate base
  | plugin :: rest =>
      plugin.condition_with_base formula certificate base ∨ₘ
        condition_list rest formula certificate base

theorem condition_list_admissible
    (plugins : List SchemaPlugin)
    (formula certificate : SetTerm)
    (base : FreeVarId)
    (hFormula : Term.Admissible formula SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set) :
    Formula.Admissible
      (condition_list plugins formula certificate base) := by
  induction plugins with
  | nil =>
      simpa [condition_list] using
        (Formula.Admissible.falsum :
          Formula.Admissible (Formula.falsum : SetFormula))
  | cons plugin rest ih =>
      cases rest with
      | nil =>
          simpa [condition_list] using
            plugin.condition_admissible
              formula certificate base hFormula hCertificate
      | cons next tail =>
          simpa [condition_list] using
            Formula.Admissible.disj
              (plugin.condition_admissible
                formula certificate base hFormula hCertificate)
              ih

/-- 全部启用插件为 `Delta0` 时，有限插件析取仍为 `Delta0`。 -/
theorem condition_list_delta0
    (plugins : List SchemaPlugin)
    (formula certificate : SetTerm)
    (base : FreeVarId)
    (hPlugins :
      ∀ plugin, plugin ∈ plugins →
        Formula.IsDelta0 set_levy_bound
          (plugin.condition_with_base
            formula certificate base)) :
    Formula.IsDelta0 set_levy_bound
      (condition_list plugins formula certificate base) := by
  induction plugins with
  | nil =>
      simpa [condition_list] using
        (Formula.IsDelta0.falsum :
          Formula.IsDelta0 set_levy_bound
            (Formula.falsum : SetFormula))
  | cons plugin rest ih =>
      cases rest with
      | nil =>
          simpa [condition_list] using
            hPlugins plugin (by simp)
      | cons next tail =>
          simpa [condition_list] using
            Formula.IsDelta0.disj
              (hPlugins plugin (by simp))
              (ih (fun member hMember =>
                hPlugins member (by simp [hMember])))

/-! `Delta0` 不是插件组合的唯一可用层级；schema 的外层 witness 通常落在 `Sigma1`。 -/

theorem condition_list_sigma1
    (plugins : List SchemaPlugin)
    (formula certificate : SetTerm)
    (base : FreeVarId)
    (hPlugins :
      ∀ plugin, plugin ∈ plugins →
        Formula.IsSigma1 set_levy_bound
          (plugin.condition_with_base
            formula certificate base)) :
    Formula.IsSigma1 set_levy_bound
      (condition_list plugins formula certificate base) := by
  induction plugins with
  | nil =>
      simpa [condition_list] using
        (Formula.IsSigma1.delta0
          (Formula.IsDelta0.falsum :
            Formula.IsDelta0 set_levy_bound
              (Formula.falsum : SetFormula)))
  | cons plugin rest ih =>
      cases rest with
      | nil =>
          simpa [condition_list] using
            hPlugins plugin (by simp)
      | cons next tail =>
          simpa [condition_list] using
            Formula.IsSigma1.disj
              (hPlugins plugin (by simp))
              (ih (fun member hMember =>
                hPlugins member (by simp [hMember])))

@[formula_check]
theorem condition_list_check
    (plugins : List SchemaPlugin)
    (formula certificate : SetTerm)
    (base : FreeVarId)
    (hFormula : Term.CheckCertificate formula SetSort.set)
    (hCertificate : Term.CheckCertificate certificate SetSort.set) :
    Formula.CheckCertificate
      (condition_list plugins formula certificate base) :=
  Formula.check_certificate_of_admissible
    (condition_list_admissible
      plugins formula certificate base
      hFormula.admissible hCertificate.admissible)

/-- 任意已启用插件的成功分支都可注入总 schema 条件。 -/
theorem condition_list_of_mem
    {T : SetTheory}
    {plugins : List SchemaPlugin}
    {plugin : SchemaPlugin}
    (hPlugin : plugin ∈ plugins)
    {formula certificate : SetTerm}
    {base : FreeVarId}
    (hFormula : Term.Admissible formula SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set)
    (hCondition :
      Derives T [] (
        plugin.condition_with_base
          formula certificate base)) :
    Derives T [] (
      condition_list plugins formula certificate base) := by
  induction plugins with
  | nil =>
      simp at hPlugin
  | cons head rest ih =>
      simp only [List.mem_cons] at hPlugin
      cases rest with
      | nil =>
          rcases hPlugin with rfl | hPlugin
          · simpa [condition_list] using hCondition
          · simp at hPlugin
      | cons next tail =>
          rcases hPlugin with rfl | hPlugin
          · simpa [condition_list] using
              FirstOrder.Derives.disjIntroLeft
                (hRightCheck :=
                  Formula.check_admissible_complete
                    (condition_list_admissible
                      (next :: tail) formula certificate base
                      hFormula hCertificate))
                hCondition
          · simpa [condition_list] using
              FirstOrder.Derives.disjIntroRight
                (hLeftCheck :=
                  Formula.check_admissible_complete
                    (head.condition_admissible
                      formula certificate base
                      hFormula hCertificate))
                (ih hPlugin)

/-- 全部启用插件均被拒绝时，总 schema 条件被拒绝。 -/
theorem condition_list_neg
    {T : SetTheory}
    (plugins : List SchemaPlugin)
    (formula certificate : SetTerm)
    (base : FreeVarId)
    (hFormula : Term.Admissible formula SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set)
    (hReject :
      ∀ plugin, plugin ∈ plugins →
        Derives T [] (
          ¬ₘ plugin.condition_with_base
            formula certificate base)) :
    Derives T [] (
      ¬ₘ condition_list plugins formula certificate base) := by
  induction plugins with
  | nil =>
      nd_apply FirstOrder.Derives.negIntro
        (T := T) (Γ := ([] : Context signature))
        (body :=
          condition_list [] formula certificate base)
      exact FirstOrder.Derives.assumption (by
        simp [condition_list])
  | cons plugin rest ih =>
      cases rest with
      | nil =>
          simpa [condition_list] using
            hReject plugin (by simp)
      | cons next tail =>
          let head : SetFormula :=
            plugin.condition_with_base
              formula certificate base
          let restCondition : SetFormula :=
            condition_list (next :: tail)
              formula certificate base
          let body : SetFormula := head ∨ₘ restCondition
          have hHeadNeg : Derives T [] (¬ₘ head) := by
            simpa [head] using
              hReject plugin (by simp)
          have hRestNeg :
              Derives T [] (¬ₘ restCondition) := by
            simpa [restCondition] using
              ih (fun member hMember =>
                hReject member (by simp [hMember]))
          have hBody : Formula.Admissible body := by
            simpa [body, head, restCondition,
              condition_list] using
              condition_list_admissible
                (plugin :: next :: tail)
                formula certificate base
                hFormula hCertificate
          nd_apply FirstOrder.Derives.negIntro
            (T := T) (Γ := ([] : Context signature))
            (body := body)
            (hBodyCheck :=
              Formula.check_admissible_complete hBody)
          let Γ : Context signature := [body]
          have hBodyAt : Γ ⊢ₘ[T] body :=
            FirstOrder.Derives.assumption (by simp [Γ])
          apply FirstOrder.Derives.disjElim hBodyAt
          · exact FirstOrder.Derives.negElim
              (FirstOrder.Derives.assumption
                (Γ := head :: Γ) (by simp))
              (FirstOrder.Derives.context_weaken
                (Γ := []) (Δ := head :: Γ)
                (by simp) hHeadNeg)
          · exact FirstOrder.Derives.negElim
              (FirstOrder.Derives.assumption
                (Γ := restCondition :: Γ) (by simp))
              (FirstOrder.Derives.context_weaken
                (Γ := []) (Δ := restCondition :: Γ)
                (by simp) hRestNeg)

/--
若每个插件分支都保持同一项替换，则插件列表的总析取也保持该替换。
-/
theorem condition_list_substitute
    (plugins : List SchemaPlugin)
    (formula certificate replacement
      formulaResult certificateResult : SetTerm)
    (sourceId : FreeVarId)
    (base : FreeVarId)
    (hPlugin :
      ∀ plugin, plugin ∈ plugins →
        Formula.substituteFree SetSort.set sourceId replacement
            (plugin.condition_with_base
              formula certificate base) =
          plugin.condition_with_base
            formulaResult certificateResult base) :
    Formula.substituteFree SetSort.set sourceId replacement
        (condition_list plugins formula certificate base) =
      condition_list plugins
        formulaResult certificateResult base := by
  induction plugins with
  | nil =>
      rfl
  | cons plugin rest ih =>
      cases rest with
      | nil =>
          simpa [condition_list] using
            hPlugin plugin (by simp)
      | cons next tail =>
          have hHead := hPlugin plugin (by simp)
          have hTail :=
            ih (fun member hMember =>
              hPlugin member (by simp [hMember]))
          simp [condition_list, Formula.substituteFree,
            hHead, hTail]

end SchemaPlugin
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
