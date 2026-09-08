import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Basic

/-!
# 类型化分离公理

分离谓词的待筛选元素占据唯一的 bound 槽，外部参数由 free 上下文精确记录。
公理先以规范 free 槽引入母集，再统一关闭全部参数；实例化只经过公共全称闭包接口，
不再生成变量编号、新鲜性、作用域、admissibility 或检查证书义务。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

/-- 单个集合元素 binder 下的类型化分离谓词。 -/
structure SetPredicate (free : SetContext) where
  body : SetFormula [SetSort.set] free

namespace SetPredicate

/-- 谓词参数整体进入一个新的 free 槽。 -/
def weakenFree {free : SetContext}
    (predicate : SetPredicate free) :
    SetPredicate (SetSort.set :: free) where
  body := predicate.body.weakenFree SetSort.set

/-- 对谓词的全部外部参数执行一次类型化替换。 -/
def substituteFree {sourceFree targetFree : SetContext}
    (substitution :
      VariableSubstitution signature sourceFree [] targetFree)
    (predicate : SetPredicate sourceFree) :
    SetPredicate targetFree where
  body := predicate.body.substituteFree
    (VariableSubstitution.embedBoundClosed [SetSort.set] substitution)

/-- 在规范新元素处打开谓词的元素 binder。 -/
def atNewest {free : SetContext}
  (predicate : SetPredicate free) :
    SetOpenFormula (SetSort.set :: free) :=
  (predicate.body.weakenFree SetSort.set).instantiateTop
    (FreshVariable.newest
      (σ := signature) (free := free) SetSort.set)

/-- 母集成员条件与分离谓词的合取。 -/
def separation_condition {free : SetContext}
    (predicate : SetPredicate free) (source : SetOpenTerm free) :
    SetOpenFormula (SetSort.set :: free) :=
  let element := FreshVariable.newest
    (σ := signature) (free := free) SetSort.set
  (element ∈ₘ source.weakenFree SetSort.set) ∧ₘ predicate.atNewest

/-- `target` 恰由 `source` 中满足谓词的元素组成。 -/
def separation_spec {free : SetContext}
    (predicate : SetPredicate free)
    (source target : SetOpenTerm free) : SetOpenFormula free :=
  membership_specification target
    (predicate.separation_condition source)

/-- 对固定母集断言一个分离结果存在。 -/
def separation_exists {free : SetContext}
    (predicate : SetPredicate free)
    (source : SetOpenTerm free) : SetOpenFormula free :=
  let target := FreshVariable.newest
    (σ := signature) (free := free) SetSort.set
  ((predicate.weakenFree).separation_spec
      (source.weakenFree SetSort.set) target).existsFreeTop SetSort.set

/-- 分离 schema 在关闭母集前的开放实例。 -/
def separation_open_axiom {free : SetContext}
    (predicate : SetPredicate free) : SetOpenFormula free :=
  let source := FreshVariable.newest
    (σ := signature) (free := free) SetSort.set
  ((predicate.weakenFree).separation_exists source).forallFreeTop SetSort.set

/-- 关闭母集及谓词全部参数后的分离公理实例。 -/
def separation_axiom {free : SetContext}
    (predicate : SetPredicate free) : SetSentence :=
  Metatheory.Formula.forall_close predicate.separation_open_axiom

/-- 在外延理论上加入一个类型化分离公理实例。 -/
def separation_theory {free : SetContext}
    (predicate : SetPredicate free) : SetTheory :=
  Theory.insert predicate.separation_axiom extensionality_theory

/-- 已打开母集量词的分离公理可在任意母集项处实例化。 -/
theorem separation_exists_of_open_axiom
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (predicate : SetPredicate free) (source : SetOpenTerm free)
    (hAxiom : Γ ⊢ₘ[T] predicate.separation_open_axiom) :
    Γ ⊢ₘ[T] predicate.separation_exists source := by
  have hInstance := FirstOrder.Derives.forall_elim source hAxiom
  simpa [separation_open_axiom, separation_exists, weakenFree,
    separation_spec, separation_condition, atNewest,
    membership_specification, FreshVariable.newest,
    Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteFree, Term.substitute,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.liftFree,
    VariableSubstitution.instantiateFreeTop,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId] using hInstance

/-- 分离理论在任意局部上下文中给出指定母集的分离结果。 -/
theorem separation_exists_derives
    {free : SetContext} {Γ : Context signature free}
    (predicate : SetPredicate free) (source : SetOpenTerm free) :
    Γ ⊢ₘ[predicate.separation_theory]
      predicate.separation_exists source := by
  have hClosed :
      ([] : Context signature []) ⊢ₘ[predicate.separation_theory]
        Formula.fromSentence predicate.separation_axiom :=
    FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)
  have hOpen : Γ ⊢ₘ[predicate.separation_theory]
      predicate.separation_open_axiom.substituteFree
        (VariableSubstitution.freeId :
          VariableSubstitution signature free [] free) :=
    Metatheory.Derives.forall_close_elim
      predicate.separation_open_axiom
      VariableSubstitution.freeId
      hClosed
  apply predicate.separation_exists_of_open_axiom source
  simpa [Formula.substituteFree, Substitution.free_map,
    Formula.substitute] using hOpen

/-- 同一谓词从同一母集分离出的两个结果相等。 -/
theorem separation_unique
    {free : SetContext} {Γ : Context signature free}
    (predicate : SetPredicate free)
    (source left right : SetOpenTerm free) :
    Γ ⊢ₘ[extensionality_theory]
      predicate.separation_spec source left ⟶ₘ
        predicate.separation_spec source right ⟶ₘ (left ≐ₘ right) := by
  simpa [separation_spec] using
    (membership_specification_unique
      (Γ := Γ) left right (predicate.separation_condition source))

end SetPredicate
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
