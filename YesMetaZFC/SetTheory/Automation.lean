import YesMetaZFC.SetTheory.Extension
import YesMetaZFC.Automation.HostFirstOrder.ReplaySemantics

/-!
# 纯集合论公理切片到内禀一阶自动化

项目句子先进入 `HostFirstOrder.Formula` 的深度索引语法，再由公共前端同时生成
preprocessing core、原始搜索问题和内禀问题。自由闭合、bound scope 与 arity 不再形成
独立证明层；旧扁平 `searchFormula`、`FormulaScoped` 与 source/deep 反模型桥已删除。
-/

namespace YesMetaZFC
namespace SetTheory
namespace Automation

open _root_.YesMetaZFC.Automation

abbrev ProjectTerm (depth : Nat) :=
  Definitional.Project.Term depth

abbrev ProjectFormula (depth : Nat) :=
  Definitional.Project.Formula 1 depth

abbrev ProjectSentence :=
  Definitional.Project.Sentence

namespace Translate

/-- 搜索签名中保留给纯隶属关系的稳定编号。 -/
def membership_symbol : Nat := 1

/-- 自由闭合的项目项直接进入深度索引宿主一阶项。 -/
def term {depth : Nat} (source : ProjectTerm depth)
    (hClosed : source.freeSupport = []) :
    HostFirstOrder.Term depth :=
  match source with
  | .bound entry => .bvar entry
  | .free id => by
      change [id] = [] at hClosed
      cases hClosed

/-- 深度索引宿主语法中的纯隶属原子。 -/
def mem {depth : Nat} (left right : HostFirstOrder.Term depth) :
    HostFirstOrder.Formula depth :=
  .atom membership_symbol [left, right]

/--
自由闭合的项目公式直接进入深度索引宿主一阶公式。
外延等同落到内建等号，子集原子落到其一阶定义；因此搜索签名只保留真正原始的隶属关系。
-/
def formula :
    {depth : Nat} → (source : ProjectFormula depth) →
      source.FreeClosed → HostFirstOrder.Formula depth
  | _, .falsum, _ =>
      .falsum
  | _, .truth, _ =>
      .truth
  | _, .mem left right, hClosed => by
      simp only [Definitional.Formula.FreeClosed] at hClosed
      exact mem (term left hClosed.1) (term right hClosed.2)
  | _, .atom .extensionalEq _ arguments, hClosed => by
      simp only [Definitional.Formula.FreeClosed] at hClosed
      exact .equal
        (term (arguments 0) (hClosed 0))
        (term (arguments 1) (hClosed 1))
  | _, .atom .subset _ arguments, hClosed => by
      simp only [Definitional.Formula.FreeClosed] at hClosed
      exact .forallE <| .imp
        (mem (.bvar 0)
          (term (arguments 0).weaken (by simpa using hClosed 0)))
        (mem (.bvar 0)
          (term (arguments 1).weaken (by simpa using hClosed 1)))
  | _, .neg body, hClosed => by
      simp only [Definitional.Formula.FreeClosed] at hClosed
      exact .neg (formula body hClosed)
  | _, .conj left right, hClosed => by
      simp only [Definitional.Formula.FreeClosed] at hClosed
      exact .conj
        (formula left hClosed.1)
        (formula right hClosed.2)
  | _, .disj left right, hClosed => by
      simp only [Definitional.Formula.FreeClosed] at hClosed
      exact .disj
        (formula left hClosed.1)
        (formula right hClosed.2)
  | _, .imp left right, hClosed => by
      simp only [Definitional.Formula.FreeClosed] at hClosed
      exact .imp
        (formula left hClosed.1)
        (formula right hClosed.2)
  | _, .iff left right, hClosed => by
      simp only [Definitional.Formula.FreeClosed] at hClosed
      exact .iff
        (formula left hClosed.1)
        (formula right hClosed.2)
  | _, .forallE body, hClosed => by
      simp only [Definitional.Formula.FreeClosed] at hClosed
      exact .forallE (formula body hClosed)
  | _, .existsE body, hClosed => by
      simp only [Definitional.Formula.FreeClosed] at hClosed
      exact .existsE (formula body hClosed)

/-- 项目句子的唯一自动化像。 -/
def sentence (source : ProjectSentence) : HostFirstOrder.ClosedFormula :=
  formula source.formula source.freeClosed

/-- 集合结构对自动化宿主语法的标准解释。 -/
noncomputable def interpretation (ℳ : SetTheory.Structure.{u}) :
    HostFirstOrder.Interpretation ℳ.Domain where
  default := Classical.choice ℳ.nonempty
  function := fun _ _ => Classical.choice ℳ.nonempty
  predicate := fun symbol arguments =>
    match symbol, arguments with
    | 1, [left, right] => ℳ.mem left right
    | _, _ => False

/-- 标准解释只把稳定编号 `1` 解释为二元隶属。 -/
@[simp] theorem interpretation_membership
    {ℳ : SetTheory.Structure.{u}} (left right : ℳ.Domain) :
    (interpretation ℳ).predicate membership_symbol [left, right] ↔
      ℳ.mem left right := by
  rfl

/-- 宿主量词压栈与集合环境压栈逐字一致。 -/
theorem push_bound_eq {ℳ : SetTheory.Structure.{u}} {depth : Nat}
    (env : SetTheory.Env ℳ depth) (value : ℳ.Domain) :
    HostFirstOrder.Formula.pushBound value env.bound =
      (env.push value).bound := by
  funext entry
  refine Fin.cases ?_ (fun previous => ?_) entry <;> rfl

/-- 项目闭项与其宿主一阶像取值相同。 -/
@[simp] theorem eval_term {ℳ : SetTheory.Structure.{u}} {depth : Nat}
    (env : SetTheory.Env ℳ depth) (source : ProjectTerm depth)
    (hClosed : source.freeSupport = []) :
    HostFirstOrder.Term.eval (interpretation ℳ) env.bound
        (term source hClosed) =
      Definitional.Term.eval env source := by
  cases source with
  | bound entry =>
      simp [term, HostFirstOrder.Term.eval,
        Definitional.Term.eval]
  | free id =>
      change [id] = [] at hClosed
      cases hClosed

/-- 新 binder 下提升的项目项仍按原环境取值。 -/
@[simp] theorem eval_term_weaken {ℳ : SetTheory.Structure.{u}}
    {depth : Nat} (env : SetTheory.Env ℳ depth) (value : ℳ.Domain)
    (source : ProjectTerm depth)
    (hClosed : source.weaken.freeSupport = []) :
    HostFirstOrder.Term.eval (interpretation ℳ)
        (HostFirstOrder.Formula.pushBound value env.bound)
        (term source.weaken hClosed) =
      Definitional.Term.eval env source := by
  rw [push_bound_eq]
  rw [eval_term (env.push value)]
  exact Definitional.Term.eval_weaken env value source

/-- 宿主语法最新绑定变量取栈顶值。 -/
@[simp] theorem eval_newest {ℳ : SetTheory.Structure.{u}}
    {depth : Nat} (env : SetTheory.Env ℳ depth) (value : ℳ.Domain) :
    HostFirstOrder.Term.eval (interpretation ℳ)
        (HostFirstOrder.Formula.pushBound value env.bound)
        (.bvar 0 : HostFirstOrder.Term (depth + 1)) = value := by
  rw [HostFirstOrder.Term.eval]
  rw [push_bound_eq]
  rfl

/-- 项目公式与唯一自动化像在外延集合结构中语义一致。 -/
theorem eval_formula {ℳ : SetTheory.Structure.{u}}
    (hExt : Extensional ℳ) {depth : Nat} (env : SetTheory.Env ℳ depth) :
    ∀ (source : ProjectFormula depth) (hClosed : source.FreeClosed),
      HostFirstOrder.Formula.eval (interpretation ℳ) env.bound
          (formula source hClosed) ↔
        Definitional.Project.Formula.satisfies env source
  | .falsum, _ => by
      simp [formula, HostFirstOrder.Formula.eval,
        Definitional.Project.Formula.satisfies_falsum_iff]
  | .truth, _ => by
      simp [formula, HostFirstOrder.Formula.eval,
        Definitional.Project.Formula.satisfies_truth_iff]
  | .mem left right, hClosed => by
      simp only [Definitional.Formula.FreeClosed] at hClosed
      rw [Definitional.Project.Formula.satisfies_mem_iff]
      simp only [formula, mem, HostFirstOrder.Formula.eval,
        HostFirstOrder.Term.evalList, interpretation_membership]
      rw [eval_term env left, eval_term env right]
  | .atom .extensionalEq hStage arguments, hClosed => by
      simp only [Definitional.Formula.FreeClosed] at hClosed
      rw [Definitional.Project.Formula.satisfies_atom_extensionalEq_iff]
      simp only [formula, HostFirstOrder.Formula.eval,
        eval_term env (arguments 0) (hClosed 0),
        eval_term env (arguments 1) (hClosed 1)]
      constructor
      · intro hEqual value
        simp [hEqual]
      · exact hExt.eq_of_same_members _ _
  | .atom .subset hStage arguments, hClosed => by
      simp only [Definitional.Formula.FreeClosed] at hClosed
      rw [Definitional.Project.Formula.satisfies_atom_subset_iff]
      simp only [formula, HostFirstOrder.Formula.eval, mem,
        HostFirstOrder.Term.evalList, interpretation_membership]
      simp only [eval_newest, eval_term_weaken]
  | .neg body, hClosed => by
      simp only [Definitional.Formula.FreeClosed] at hClosed
      simpa [formula, HostFirstOrder.Formula.eval,
        Definitional.Project.Formula.satisfies_neg_iff] using
        not_congr (eval_formula hExt env body hClosed)
  | .conj left right, hClosed => by
      simp only [Definitional.Formula.FreeClosed] at hClosed
      simpa [formula, HostFirstOrder.Formula.eval,
        Definitional.Project.Formula.satisfies_conj_iff] using
        and_congr
          (eval_formula hExt env left hClosed.1)
          (eval_formula hExt env right hClosed.2)
  | .disj left right, hClosed => by
      simp only [Definitional.Formula.FreeClosed] at hClosed
      simpa [formula, HostFirstOrder.Formula.eval,
        Definitional.Project.Formula.satisfies_disj_iff] using
        or_congr
          (eval_formula hExt env left hClosed.1)
          (eval_formula hExt env right hClosed.2)
  | .imp left right, hClosed => by
      simp only [Definitional.Formula.FreeClosed] at hClosed
      simpa [formula, HostFirstOrder.Formula.eval,
        Definitional.Project.Formula.satisfies_imp_iff] using
        imp_congr
          (eval_formula hExt env left hClosed.1)
          (eval_formula hExt env right hClosed.2)
  | .iff left right, hClosed => by
      simp only [Definitional.Formula.FreeClosed] at hClosed
      simpa [formula, HostFirstOrder.Formula.eval,
        Definitional.Project.Formula.satisfies_iff_iff] using
        iff_congr
          (eval_formula hExt env left hClosed.1)
          (eval_formula hExt env right hClosed.2)
  | .forallE body, hClosed => by
      simp only [Definitional.Formula.FreeClosed] at hClosed
      rw [Definitional.Project.Formula.satisfies_forall_iff]
      simp only [formula, HostFirstOrder.Formula.eval]
      constructor <;> intro h value
      · exact (eval_formula hExt (env.push value) body hClosed).mp <| by
          simpa [push_bound_eq] using h value
      · simpa [push_bound_eq] using
          (eval_formula hExt (env.push value) body hClosed).mpr (h value)
  | .existsE body, hClosed => by
      simp only [Definitional.Formula.FreeClosed] at hClosed
      rw [Definitional.Project.Formula.satisfies_exists_iff]
      simp only [formula, HostFirstOrder.Formula.eval]
      constructor
      · rintro ⟨value, hBody⟩
        refine ⟨value, ?_⟩
        exact (eval_formula hExt (env.push value) body hClosed).mp <| by
          simpa [push_bound_eq] using hBody
      · rintro ⟨value, hBody⟩
        refine ⟨value, ?_⟩
        simpa [push_bound_eq] using
          (eval_formula hExt (env.push value) body hClosed).mpr hBody

/-- 项目句子满足关系与闭宿主公式求值一致。 -/
theorem eval_sentence {ℳ : SetTheory.Structure.{u}}
    (hExt : Extensional ℳ) (free : FreeVarId → ℳ.Domain)
    (source : ProjectSentence) :
    HostFirstOrder.Semantics.closedEval (interpretation ℳ)
        (sentence source) ↔
      Definitional.Project.Formula.satisfies
        ({ bound := Fin.elim0, free := free } : SetTheory.Env ℳ 0)
        source.formula := by
  simpa [HostFirstOrder.Semantics.closedEval, sentence] using!
    eval_formula hExt
      ({ bound := Fin.elim0, free := free } : SetTheory.Env ℳ 0)
      source.formula source.freeClosed

end Translate

/-! ## 有限理论切片 -/

/-- 无限集合论理论的显式有限搜索切片。 -/
structure TheorySlice (theory : Theory) where
  axioms : List ProjectSentence
  member : ∀ sentence, sentence ∈ axioms → theory sentence

namespace TheorySlice

/-- 空切片。 -/
def empty (theory : Theory) : TheorySlice theory where
  axioms := []
  member := by simp

/-- 单公理切片。 -/
def singleton {theory : Theory} (sentence : ProjectSentence)
    (hSentence : theory sentence) : TheorySlice theory where
  axioms := [sentence]
  member := by
    intro candidate hCandidate
    simp only [List.mem_singleton] at hCandidate
    subst candidate
    exact hSentence

/-- 向切片前端加入一条来源已证明的公理。 -/
def push {theory : Theory} (slice : TheorySlice theory)
    (sentence : ProjectSentence) (hSentence : theory sentence) :
    TheorySlice theory where
  axioms := sentence :: slice.axioms
  member := by
    intro candidate hCandidate
    rcases List.mem_cons.mp hCandidate with rfl | hTail
    · exact hSentence
    · exact slice.member candidate hTail

/-- 沿理论包含映射提升切片。 -/
def mapTheory {weak strong : Theory} (slice : TheorySlice weak)
    (hMap : ∀ sentence, weak sentence → strong sentence) :
    TheorySlice strong where
  axioms := slice.axioms
  member := fun sentence hSentence =>
    hMap sentence (slice.member sentence hSentence)

/-- 切片自身形成的有限理论。 -/
def asTheory {theory : Theory} (slice : TheorySlice theory) : Theory :=
  fun sentence => sentence ∈ slice.axioms

/-- 切片公理逐字包含于原理论。 -/
theorem subtheory {theory : Theory} (slice : TheorySlice theory) :
    Theory.Subtheory slice.asTheory theory :=
  slice.member

/-- 切片的唯一宿主闭公式表。 -/
def hostPremises {theory : Theory} (slice : TheorySlice theory) :
    List HostFirstOrder.ClosedFormula :=
  slice.axioms.map Translate.sentence

/-- 切片进入 preprocessing core。 -/
def sourceProblem {theory : Theory} (slice : TheorySlice theory)
    (target : ProjectSentence) : SourcePreprocessing.Problem :=
  HostFirstOrder.sourceProblemOfSyntax slice.hostPremises
    (Translate.sentence target)

/-- 切片进入可计算 DAG 搜索语法。 -/
def searchProblem {theory : Theory} (slice : TheorySlice theory)
    (target : ProjectSentence) : SourcePreprocessing.DeepProblem :=
  HostFirstOrder.searchProblemOfSyntax slice.hostPremises
    (Translate.sentence target)

/-- 切片进入内禀一阶语义问题。 -/
def intrinsicProblem {theory : Theory} (slice : TheorySlice theory)
    (target : ProjectSentence) :
    LogicSoundness.SetLevel.DeepProblem
      SearchMaterialization.SearchSignature :=
  HostFirstOrder.intrinsicProblemOfSyntax slice.hostPremises
    (Translate.sentence target)

/-- 内禀搜索定理提升为原集合论理论的语义定理。 -/
theorem soundOfSearch {theory : Theory} (slice : TheorySlice theory)
    (target : ProjectSentence)
    (hSearch : LogicSoundness.SetLevel.SemanticallyEntails
      (slice.intrinsicProblem target).theory
      (slice.intrinsicProblem target).target) :
    SemanticallyEntails.{0} theory target := by
  intro ℳ hModels
  rw [Structure.satisfiesSentence_iff]
  intro free
  let interpretation := Translate.interpretation ℳ
  have hTarget := hSearch (HostFirstOrder.Semantics.model interpretation) (by
    intro formula hFormula
    rcases List.mem_map.mp hFormula with
      ⟨hostSentence, hHostSentence, rfl⟩
    rcases List.mem_map.mp hHostSentence with
      ⟨sentence, hSentence, rfl⟩
    rw [HostFirstOrder.Semantics.trueIn_iff]
    exact (Translate.eval_sentence hModels.1 free sentence).mpr
      ((Structure.satisfiesSentence_iff ℳ sentence).mp
        (hModels.2 sentence (slice.member sentence hSentence)) free))
  exact (Translate.eval_sentence hModels.1 free target).mp
    ((HostFirstOrder.Semantics.trueIn_iff interpretation
      (Translate.sentence target)).mp hTarget)

end TheorySlice
end Automation

namespace KP

/-- KP 的固定有限公理切片；模式实例按证明需要继续 `push`。 -/
def automationCoreSlice : Automation.TheorySlice SetTheory.KP :=
  Automation.TheorySlice.empty SetTheory.KP
    |>.push Axioms.extensionality Axiom.extensionality
    |>.push Axioms.emptySet Axiom.emptySet
    |>.push Axioms.pairing Axiom.pairing
    |>.push Axioms.union Axiom.union
    |>.push Axioms.infinity Axiom.infinity
    |>.push Axioms.foundation Axiom.foundation

end KP

namespace ZF

/-- ZF 的固定有限公理切片；分离/收集实例按证明需要继续 `push`。 -/
def automationCoreSlice : Automation.TheorySlice SetTheory.ZF :=
  Automation.TheorySlice.empty SetTheory.ZF
    |>.push Axioms.extensionality Axiom.extensionality
    |>.push Axioms.emptySet Axiom.emptySet
    |>.push Axioms.pairing Axiom.pairing
    |>.push Axioms.union Axiom.union
    |>.push Axioms.powerSet Axiom.powerSet
    |>.push Axioms.infinity Axiom.infinity
    |>.push Axioms.foundation Axiom.foundation

end ZF

namespace ZFC

/-- ZFC 的固定有限公理切片；模式实例按证明需要继续 `push`。 -/
def automationCoreSlice : Automation.TheorySlice SetTheory.ZFC :=
  ZF.automationCoreSlice
    |>.mapTheory (fun _ hSentence => Axiom.zf hSentence)
    |>.push Axioms.choice Axiom.choice

end ZFC
end SetTheory
end YesMetaZFC
