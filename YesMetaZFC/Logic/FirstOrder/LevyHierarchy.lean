import YesMetaZFC.Logic.FirstOrder.Derivation.Substitution

/-!
# 内在类型的一阶 Lévy 层级

界项直接处于量词外层的 bound/free 上下文；有界量词构造器只负责把它弱化到量词
体内。因此界项不可能依赖刚引入的变量，不再需要 `BoundFreeAt`、自然数深度或关闭
自由变量后的捕获证明。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Formula

universe u v w

/-- 相对 Lévy 层级所使用的二元有界关系。 -/
structure LevyBound (σ : Signature.{u, v, w}) where
  sort : σ.SortSymbol
  relation : σ.RelSymbol
  domains : σ.relDomain relation = [sort, sort]

namespace LevyBound

/-- 构造类型正确的有界关系原子式。 -/
def membership {σ : Signature.{u, v, w}} (ℬ : LevyBound σ)
    {bound free : SortContext σ}
    (element set : Term σ bound free ℬ.sort) : Formula σ bound free :=
  .rel ℬ.relation
    (ℬ.domains.symm ▸ (.cons element (.cons set .nil)))

theorem pair_arguments_substituteMapped
    {σ : Signature.{u, v, w}}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    {domain : List σ.SortSymbol} {sort : σ.SortSymbol}
    (hDomain : domain = [sort, sort])
    (boundSubstitution : VariableSubstitution σ sourceBound
      targetBound targetFree)
    (freeSubstitution : VariableSubstitution σ sourceFree
      targetBound targetFree)
    (element set : Term σ sourceBound sourceFree sort) :
    (hDomain.symm ▸
      (Arguments.cons element (Arguments.cons set Arguments.nil) :
        Arguments σ sourceBound sourceFree [sort, sort])).substituteMapped
        boundSubstitution freeSubstitution =
      hDomain.symm ▸
        (Arguments.cons
          (element.substituteMapped boundSubstitution freeSubstitution)
          (Arguments.cons
            (set.substituteMapped boundSubstitution freeSubstitution)
            Arguments.nil) :
          Arguments σ targetBound targetFree [sort, sort]) := by
  cases hDomain
  rfl

@[simp] theorem membership_substituteMapped
    {σ : Signature.{u, v, w}} (ℬ : LevyBound σ)
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (boundSubstitution : VariableSubstitution σ sourceBound
      targetBound targetFree)
    (freeSubstitution : VariableSubstitution σ sourceFree
      targetBound targetFree)
    (element set : Term σ sourceBound sourceFree ℬ.sort) :
    (ℬ.membership element set).substituteMapped
        boundSubstitution freeSubstitution =
      ℬ.membership
        (element.substituteMapped boundSubstitution freeSubstitution)
        (set.substituteMapped boundSubstitution freeSubstitution) := by
  change
    Formula.rel ℬ.relation
        ((ℬ.domains.symm ▸
          (Arguments.cons element (Arguments.cons set Arguments.nil) :
            Arguments σ sourceBound sourceFree [ℬ.sort, ℬ.sort])).substituteMapped
          boundSubstitution freeSubstitution) =
      Formula.rel ℬ.relation
        (ℬ.domains.symm ▸
          (Arguments.cons
            (element.substituteMapped boundSubstitution freeSubstitution)
            (Arguments.cons
              (set.substituteMapped boundSubstitution freeSubstitution)
              Arguments.nil) :
            Arguments σ targetBound targetFree [ℬ.sort, ℬ.sort]))
  exact congrArg (Formula.rel ℬ.relation)
    (pair_arguments_substituteMapped ℬ.domains
      boundSubstitution freeSubstitution element set)

/-- 有界关系原子沿 free 上下文弱化逐项作用。 -/
@[simp] theorem membership_weakenFree
    {σ : Signature.{u, v, w}} (ℬ : LevyBound σ)
    {bound free : SortContext σ}
    (introduced : σ.SortSymbol)
    (element set : Term σ bound free ℬ.sort) :
    (ℬ.membership element set).weakenFree introduced =
      ℬ.membership (element.weakenFree introduced)
        (set.weakenFree introduced) := by
  rw [Formula.weakenFree_eq_renameMapped]
  rw [← Formula.substituteMapped_of_renaming]
  rw [membership_substituteMapped]
  congr 1
  · exact Term.substituteMapped_of_renaming
      (VariableRenaming.weaken introduced) element
  · exact Term.substituteMapped_of_renaming
      (VariableRenaming.weaken introduced) set

/-- 标准有界全称量词 `∀ x ∈ set, body`。 -/
def boundedForall {σ : Signature.{u, v, w}} (ℬ : LevyBound σ)
    {bound free : SortContext σ}
    (set : Term σ bound free ℬ.sort)
    (body : Formula σ (ℬ.sort :: bound) free) :
    Formula σ bound free :=
  .forallE ℬ.sort
    (.imp
      (ℬ.membership (.bvar .here) (set.weakenBound ℬ.sort))
      body)

/--
界项由外层最新 bound 变量承载时，顶部实例化直接恢复普通有界全称。
该等式把定义域运输压缩为一次根节点归约，避免下游展开量词体。
-/
@[simp] theorem boundedForall_instantiateTop_bvar
    {σ : Signature.{u, v, w}} (ℬ : LevyBound σ)
    {bound free : SortContext σ}
    (replacement : Term σ bound free ℬ.sort)
    (body : Formula σ (ℬ.sort :: bound) free) :
    (ℬ.boundedForall
        ((.bvar .here) : Term σ (ℬ.sort :: bound) free ℬ.sort)
        (body.weakenBoundUnderTop ℬ.sort)).instantiateTop replacement =
      ℬ.boundedForall replacement body := by
  simp only [boundedForall, Formula.instantiateTop,
    Substitution.instantiateTop, Formula.substitute,
    Formula.substituteMapped, membership_substituteMapped,
    VariableSubstitution.weakenBound_freeId,
    Formula.substituteMapped_liftBound_instantiateTop_weakenBoundUnderTop,
    Term.substituteMapped, VariableSubstitution.liftBound,
    VariableSubstitution.instantiateTop,
    Term.weakenBound, Term.rename, Renaming.weakenBound,
    Renaming.bound, Term.renameMapped, VariableRenaming.weaken]

/-- 标准有界存在量词 `∃ x ∈ set, body`。 -/
def boundedExists {σ : Signature.{u, v, w}} (ℬ : LevyBound σ)
    {bound free : SortContext σ}
    (set : Term σ bound free ℬ.sort)
    (body : Formula σ (ℬ.sort :: bound) free) :
    Formula σ bound free :=
  .existsE ℬ.sort
    (.conj
      (ℬ.membership (.bvar .here) (set.weakenBound ℬ.sort))
      body)

end LevyBound

/--
量词体在正位置携带当前变量的成员界。该证书只沿合取传播，用于允许已经把成员
原子合并进较大合取的有界存在式。
-/
inductive MembershipGuard {σ : Signature.{u, v, w}} (ℬ : LevyBound σ)
    {bound free : SortContext σ}
    (set : Term σ bound free ℬ.sort) :
    Formula σ (ℬ.sort :: bound) free → Prop where
  | membership :
      MembershipGuard ℬ set
        (ℬ.membership (.bvar .here) (set.weakenBound ℬ.sort))
  | conj_left {left right : Formula σ (ℬ.sort :: bound) free} :
      MembershipGuard ℬ set left →
        MembershipGuard ℬ set (.conj left right)
  | conj_right {left right : Formula σ (ℬ.sort :: bound) free} :
      MembershipGuard ℬ set right →
        MembershipGuard ℬ set (.conj left right)

/-- 相对 `Delta0` 公式：只含布尔联结词和内在有界量词。 -/
inductive IsDelta0 {σ : Signature.{u, v, w}} (ℬ : LevyBound σ) :
    {bound free : SortContext σ} → Formula σ bound free → Prop where
  | falsum {bound free} :
      IsDelta0 ℬ (.falsum : Formula σ bound free)
  | truth {bound free} :
      IsDelta0 ℬ (.truth : Formula σ bound free)
  | rel {bound free} (relation : σ.RelSymbol)
      (arguments : Arguments σ bound free (σ.relDomain relation)) :
      IsDelta0 ℬ (.rel relation arguments)
  | equal {bound free} {sort : σ.SortSymbol}
      (left right : Term σ bound free sort) :
      IsDelta0 ℬ (.equal left right)
  | neg {bound free} {body : Formula σ bound free} :
      IsDelta0 ℬ body → IsDelta0 ℬ (.neg body)
  | conj {bound free} {left right : Formula σ bound free} :
      IsDelta0 ℬ left → IsDelta0 ℬ right → IsDelta0 ℬ (.conj left right)
  | disj {bound free} {left right : Formula σ bound free} :
      IsDelta0 ℬ left → IsDelta0 ℬ right → IsDelta0 ℬ (.disj left right)
  | imp {bound free} {left right : Formula σ bound free} :
      IsDelta0 ℬ left → IsDelta0 ℬ right → IsDelta0 ℬ (.imp left right)
  | iff {bound free} {left right : Formula σ bound free} :
      IsDelta0 ℬ left → IsDelta0 ℬ right → IsDelta0 ℬ (.iff left right)
  | bounded_forall {bound free}
      (set : Term σ bound free ℬ.sort)
      {body : Formula σ (ℬ.sort :: bound) free} :
      IsDelta0 ℬ body → IsDelta0 ℬ (ℬ.boundedForall set body)
  | bounded_exists {bound free}
      (set : Term σ bound free ℬ.sort)
      {body : Formula σ (ℬ.sort :: bound) free} :
      IsDelta0 ℬ body → IsDelta0 ℬ (ℬ.boundedExists set body)
  | guarded_exists {bound free}
      (set : Term σ bound free ℬ.sort)
      {body : Formula σ (ℬ.sort :: bound) free} :
      IsDelta0 ℬ body → MembershipGuard ℬ set body →
        IsDelta0 ℬ (.existsE ℬ.sort body)

namespace MembershipGuard

/-- 类型化替换保持正位置成员 guard。 -/
theorem substituteMapped
    {σ : Signature.{u, v, w}} {ℬ : LevyBound σ}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    {set : Term σ sourceBound sourceFree ℬ.sort}
    {body : Formula σ (ℬ.sort :: sourceBound) sourceFree}
    (boundSubstitution : VariableSubstitution σ sourceBound
      targetBound targetFree)
    (freeSubstitution : VariableSubstitution σ sourceFree
      targetBound targetFree)
    (hGuard : MembershipGuard ℬ set body) :
    MembershipGuard ℬ
      (set.substituteMapped boundSubstitution freeSubstitution)
      (body.substituteMapped
        (VariableSubstitution.liftBound ℬ.sort boundSubstitution)
        (VariableSubstitution.weakenBound ℬ.sort freeSubstitution)) := by
  induction hGuard with
  | membership =>
      rw [LevyBound.membership_substituteMapped]
      simpa [Term.substituteMapped_weakenBound,
        VariableSubstitution.liftBound,
        VariableSubstitution.weakenBound] using!
        (MembershipGuard.membership (ℬ := ℬ)
          (set := set.substituteMapped boundSubstitution freeSubstitution))
  | conj_left hLeft ih =>
      simpa [Formula.substituteMapped] using
        (MembershipGuard.conj_left (ℬ := ℬ)
          (set := set.substituteMapped boundSubstitution freeSubstitution)
          ih)
  | conj_right hRight ih =>
      simpa [Formula.substituteMapped] using
        (MembershipGuard.conj_right (ℬ := ℬ)
          (set := set.substituteMapped boundSubstitution freeSubstitution)
          ih)

end MembershipGuard

namespace IsDelta0

/-- 类型化替换保持 `Delta0`，包括成员 guard 形式的有界存在式。 -/
theorem substituteMapped
    {σ : Signature.{u, v, w}} {ℬ : LevyBound σ}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    {formula : Formula σ sourceBound sourceFree}
    (boundSubstitution : VariableSubstitution σ sourceBound
      targetBound targetFree)
    (freeSubstitution : VariableSubstitution σ sourceFree
      targetBound targetFree)
    (hFormula : IsDelta0 ℬ formula) :
    IsDelta0 ℬ
      (formula.substituteMapped boundSubstitution freeSubstitution) := by
  induction hFormula generalizing targetBound targetFree with
  | falsum =>
      exact IsDelta0.falsum
  | truth =>
      exact IsDelta0.truth
  | rel relation arguments =>
      exact IsDelta0.rel relation
        (arguments.substituteMapped boundSubstitution freeSubstitution)
  | equal left right =>
      exact IsDelta0.equal
        (left.substituteMapped boundSubstitution freeSubstitution)
        (right.substituteMapped boundSubstitution freeSubstitution)
  | neg hBody ih =>
      exact IsDelta0.neg (ih boundSubstitution freeSubstitution)
  | conj hLeft hRight ihLeft ihRight =>
      exact IsDelta0.conj
        (ihLeft boundSubstitution freeSubstitution)
        (ihRight boundSubstitution freeSubstitution)
  | disj hLeft hRight ihLeft ihRight =>
      exact IsDelta0.disj
        (ihLeft boundSubstitution freeSubstitution)
        (ihRight boundSubstitution freeSubstitution)
  | imp hLeft hRight ihLeft ihRight =>
      exact IsDelta0.imp
        (ihLeft boundSubstitution freeSubstitution)
        (ihRight boundSubstitution freeSubstitution)
  | iff hLeft hRight ihLeft ihRight =>
      exact IsDelta0.iff
        (ihLeft boundSubstitution freeSubstitution)
        (ihRight boundSubstitution freeSubstitution)
  | bounded_forall set hBody ih =>
      simpa [LevyBound.boundedForall, Formula.substituteMapped,
        LevyBound.membership_substituteMapped,
        Term.substituteMapped_weakenBound, Term.substituteMapped,
        VariableSubstitution.liftBound] using
        (IsDelta0.bounded_forall
          (set.substituteMapped boundSubstitution freeSubstitution)
          (ih
            (VariableSubstitution.liftBound ℬ.sort boundSubstitution)
            (VariableSubstitution.weakenBound ℬ.sort freeSubstitution)))
  | bounded_exists set hBody ih =>
      simpa [LevyBound.boundedExists, Formula.substituteMapped,
        LevyBound.membership_substituteMapped,
        Term.substituteMapped_weakenBound, Term.substituteMapped,
        VariableSubstitution.liftBound] using
        (IsDelta0.bounded_exists
          (set.substituteMapped boundSubstitution freeSubstitution)
          (ih
            (VariableSubstitution.liftBound ℬ.sort boundSubstitution)
            (VariableSubstitution.weakenBound ℬ.sort freeSubstitution)))
  | guarded_exists set hBody hGuard ihBody =>
      simpa [Formula.substituteMapped] using
        (IsDelta0.guarded_exists
          (set.substituteMapped boundSubstitution freeSubstitution)
          (ihBody
            (VariableSubstitution.liftBound ℬ.sort boundSubstitution)
            (VariableSubstitution.weakenBound ℬ.sort freeSubstitution))
          (MembershipGuard.substituteMapped
            boundSubstitution freeSubstitution hGuard))

end IsDelta0

/-- 一阶 Lévy 层级的极性。 -/
inductive LevyPolarity where
  | sigma
  | pi
  deriving DecidableEq, Repr

namespace LevyPolarity

def flip : LevyPolarity → LevyPolarity
  | .sigma => .pi
  | .pi => .sigma

@[simp] theorem flip_sigma : flip .sigma = .pi := rfl
@[simp] theorem flip_pi : flip .pi = .sigma := rfl

end LevyPolarity

/-- `Sigma1` 与 `Pi1` 的统一极性索引定义。 -/
inductive IsLevel1 {σ : Signature.{u, v, w}} (ℬ : LevyBound σ) :
    LevyPolarity → {bound free : SortContext σ} →
      Formula σ bound free → Prop where
  | delta0 {polarity bound free} {formula : Formula σ bound free} :
      IsDelta0 ℬ formula → IsLevel1 ℬ polarity formula
  | neg {polarity bound free} {body : Formula σ bound free} :
      IsLevel1 ℬ polarity body →
        IsLevel1 ℬ polarity.flip (.neg body)
  | conj {polarity bound free} {left right : Formula σ bound free} :
      IsLevel1 ℬ polarity left → IsLevel1 ℬ polarity right →
        IsLevel1 ℬ polarity (.conj left right)
  | disj {polarity bound free} {left right : Formula σ bound free} :
      IsLevel1 ℬ polarity left → IsLevel1 ℬ polarity right →
        IsLevel1 ℬ polarity (.disj left right)
  | imp {polarity bound free} {left right : Formula σ bound free} :
      IsLevel1 ℬ polarity.flip left → IsLevel1 ℬ polarity right →
        IsLevel1 ℬ polarity (.imp left right)
  | existsE {bound free} (sort : σ.SortSymbol)
      {body : Formula σ (sort :: bound) free} :
      IsLevel1 ℬ .sigma body → IsLevel1 ℬ .sigma (.existsE sort body)
  | forallE {bound free} (sort : σ.SortSymbol)
      {body : Formula σ (sort :: bound) free} :
      IsLevel1 ℬ .pi body → IsLevel1 ℬ .pi (.forallE sort body)
  | bounded_forall {polarity bound free}
      (set : Term σ bound free ℬ.sort)
      {body : Formula σ (ℬ.sort :: bound) free} :
      IsLevel1 ℬ polarity body →
        IsLevel1 ℬ polarity (ℬ.boundedForall set body)
  | bounded_exists {polarity bound free}
      (set : Term σ bound free ℬ.sort)
      {body : Formula σ (ℬ.sort :: bound) free} :
      IsLevel1 ℬ polarity body →
        IsLevel1 ℬ polarity (ℬ.boundedExists set body)

/-- 相对 `Sigma1` 公式。 -/
abbrev IsSigma1 {σ : Signature.{u, v, w}} (ℬ : LevyBound σ)
    {bound free : SortContext σ} (formula : Formula σ bound free) :=
  IsLevel1 ℬ .sigma formula

/-- 相对 `Pi1` 公式。 -/
abbrev IsPi1 {σ : Signature.{u, v, w}} (ℬ : LevyBound σ)
    {bound free : SortContext σ} (formula : Formula σ bound free) :=
  IsLevel1 ℬ .pi formula

namespace IsDelta0

/-- `Delta0` 公式可直接提升为 `Sigma1`。 -/
theorem to_sigma1 {σ : Signature.{u, v, w}} {ℬ : LevyBound σ}
    {bound free : SortContext σ} {formula : Formula σ bound free}
    (hFormula : IsDelta0 ℬ formula) : IsSigma1 ℬ formula :=
  IsLevel1.delta0 hFormula

/-- `Delta0` 公式可直接提升为 `Pi1`。 -/
theorem to_pi1 {σ : Signature.{u, v, w}} {ℬ : LevyBound σ}
    {bound free : SortContext σ} {formula : Formula σ bound free}
    (hFormula : IsDelta0 ℬ formula) : IsPi1 ℬ formula :=
  IsLevel1.delta0 hFormula

end IsDelta0
end Formula
end FirstOrder
end Logic
end YesMetaZFC
