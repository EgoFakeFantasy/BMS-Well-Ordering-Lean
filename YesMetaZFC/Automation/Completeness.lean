import YesMetaZFC.Automation.SearchMaterialization
import YesMetaZFC.Logic.FirstOrder.Completeness

/-!
# 自动化后端的完备性接口

本模块直接为 ATP 使用的内在 Henkin 闭句建立自然数单射编码，并据此生成固定公平调度。
旧实现对扁平搜索项、扁平公式、`Admissible` 与 free-closed 证明的重复编码已经删除；
checked 后端本身持有闭句语义证书，最终只需经原签名强完备性回收到 `Derives`。
-/

namespace YesMetaZFC
namespace Automation
namespace SearchCompleteness

open _root_.YesMetaZFC.Logic
open _root_.YesMetaZFC.Logic.FirstOrder
open _root_.YesMetaZFC.Logic.FirstOrder.HenkinSignature
open _root_.YesMetaZFC.Logic.FirstOrder.Completeness.Henkin

abbrev SearchSignature := SearchMaterialization.SearchSignature
private abbrev pair := NatPairing.pair

/-! ## 搜索签名符号编码 -/

def core_sort_encode : CoreSyntax.CoreSort → Nat
  | .object => pair 0 0
  | .bool => pair 1 0
  | .prop => pair 2 0
  | .named id => pair 3 id
  | .arrow domain codomain =>
      pair 4 (pair (core_sort_encode domain) (core_sort_encode codomain))

theorem core_sort_encode_injective :
    Function.Injective core_sort_encode := by
  intro left
  induction left with
  | object =>
      intro right hCode
      cases right <;>
        simp [core_sort_encode, NatPairing.pair_eq_pair_iff] at hCode ⊢
  | bool =>
      intro right hCode
      cases right <;>
        simp [core_sort_encode, NatPairing.pair_eq_pair_iff] at hCode ⊢
  | prop =>
      intro right hCode
      cases right <;>
        simp [core_sort_encode, NatPairing.pair_eq_pair_iff] at hCode ⊢
  | named id =>
      intro right hCode
      cases right <;>
        simp [core_sort_encode, NatPairing.pair_eq_pair_iff] at hCode ⊢
      exact hCode
  | arrow domain codomain ihDomain ihCodomain =>
      intro right hCode
      cases right with
      | object =>
          simp [core_sort_encode, NatPairing.pair_eq_pair_iff] at hCode
      | bool =>
          simp [core_sort_encode, NatPairing.pair_eq_pair_iff] at hCode
      | prop =>
          simp [core_sort_encode, NatPairing.pair_eq_pair_iff] at hCode
      | named id =>
          simp [core_sort_encode, NatPairing.pair_eq_pair_iff] at hCode
      | arrow domain' codomain' =>
          simp only [core_sort_encode] at hCode
          rcases NatPairing.pair_eq_pair_iff.mp hCode with
            ⟨_, hPayload⟩
          rcases NatPairing.pair_eq_pair_iff.mp hPayload with
            ⟨hDomain, hCodomain⟩
          rw [ihDomain hDomain, ihCodomain hCodomain]

def core_sort_coding : NatCoding CoreSyntax.CoreSort where
  encode := core_sort_encode
  injective := core_sort_encode_injective

def symbol_kind_encode : CoreSyntax.Search.SymbolKind → Nat
  | .parameter => 0
  | .skolem => 1
  | .definition => 2
  | .choice => 3
  | .builtin => 4
  | .extensionalWitness => 5
  | .tuple => 6

theorem symbol_kind_encode_injective :
    Function.Injective symbol_kind_encode := by
  intro left right hCode
  cases left <;> cases right <;> simp [symbol_kind_encode] at hCode ⊢

def function_symbol_encode
    (symbol : CoreSyntax.Search.FunctionSymbol) : Nat :=
  pair symbol.id <|
    pair symbol.arity <|
      pair (symbol_kind_encode symbol.kind) <|
        pair ((NatCoding.list core_sort_coding).encode symbol.inputSorts)
          (core_sort_encode symbol.outputSort)

theorem function_symbol_encode_injective :
    Function.Injective function_symbol_encode := by
  rintro ⟨id, arity, kind, inputSorts, outputSort⟩
    ⟨id', arity', kind', inputSorts', outputSort'⟩ hCode
  unfold function_symbol_encode at hCode
  rcases NatPairing.pair_eq_pair_iff.mp hCode with ⟨hId, hCode⟩
  rcases NatPairing.pair_eq_pair_iff.mp hCode with ⟨hArity, hCode⟩
  rcases NatPairing.pair_eq_pair_iff.mp hCode with ⟨hKind, hCode⟩
  rcases NatPairing.pair_eq_pair_iff.mp hCode with
    ⟨hInputs, hOutput⟩
  cases hId
  cases hArity
  cases symbol_kind_encode_injective hKind
  cases (NatCoding.list core_sort_coding).injective hInputs
  cases core_sort_encode_injective hOutput
  rfl

def predicate_role_encode : CoreSyntax.PredicateRole → Nat
  | .relation => 0
  | .equalityProxy => 1
  | .membership => 2
  | .definition => 3
  | .builtin => 4

theorem predicate_role_encode_injective :
    Function.Injective predicate_role_encode := by
  intro left right hCode
  cases left <;> cases right <;> simp [predicate_role_encode] at hCode ⊢

def predicate_symbol_encode (symbol : CoreSyntax.PredicateSymbol) : Nat :=
  pair symbol.id <|
    pair symbol.arity <|
      pair (predicate_role_encode symbol.role)
        ((NatCoding.list core_sort_coding).encode symbol.inputSorts)

theorem predicate_symbol_encode_injective :
    Function.Injective predicate_symbol_encode := by
  rintro ⟨id, arity, role, inputSorts⟩
    ⟨id', arity', role', inputSorts'⟩ hCode
  unfold predicate_symbol_encode at hCode
  rcases NatPairing.pair_eq_pair_iff.mp hCode with ⟨hId, hCode⟩
  rcases NatPairing.pair_eq_pair_iff.mp hCode with ⟨hArity, hCode⟩
  rcases NatPairing.pair_eq_pair_iff.mp hCode with ⟨hRole, hInputs⟩
  cases hId
  cases hArity
  cases predicate_role_encode_injective hRole
  cases (NatCoding.list core_sort_coding).injective hInputs
  rfl

def relation_symbol_encode : SearchMaterialization.RelSymbol → Nat
  | .member => pair 0 0
  | .boolHolds => pair 1 0
  | .definition id arity => pair 2 (pair id arity)
  | .predicate symbol => pair 3 (predicate_symbol_encode symbol)

theorem relation_symbol_encode_injective :
    Function.Injective relation_symbol_encode := by
  intro left right hCode
  cases left <;> cases right <;>
    simp [relation_symbol_encode, NatPairing.pair_eq_pair_iff,
      predicate_symbol_encode_injective.eq_iff] at hCode ⊢
  all_goals exact hCode

/-! ## 内在 Henkin 项与公式编码 -/

def henkin_function_encode : HenkinFunc SearchSignature → Nat
  | .base function => pair 0 (function_symbol_encode function)
  | .witness sort index =>
      pair 1 (pair (core_sort_encode sort) index)

theorem henkin_function_encode_injective :
    Function.Injective henkin_function_encode := by
  intro left right hCode
  cases left <;> cases right
  · simp [henkin_function_encode, NatPairing.pair_eq_pair_iff,
      function_symbol_encode_injective.eq_iff] at hCode ⊢
    exact hCode
  · simp [henkin_function_encode, NatPairing.pair_eq_pair_iff] at hCode
  · simp [henkin_function_encode, NatPairing.pair_eq_pair_iff] at hCode
  · simp [henkin_function_encode, NatPairing.pair_eq_pair_iff,
      core_sort_encode_injective.eq_iff] at hCode ⊢
    exact hCode

private theorem variable_index_injective {S : Type}
    {context : List S} {sort : S} :
    Function.Injective (@Variable.index S context sort) := by
  intro left right hIndex
  induction left with
  | here =>
      cases right with
      | here => rfl
      | there previous => cases hIndex
  | there previous ih =>
      cases right with
      | here => cases hIndex
      | there previous' =>
          apply congrArg Variable.there
          apply ih
          simp [Variable.index] at hIndex
          omega

mutual

def term_encode
    {bound free : SortContext (HSignature SearchSignature)}
    {sort : SearchSignature.SortSymbol}
    (term : Term (HSignature SearchSignature) bound free sort) : Nat :=
  match term with
  | .bvar entry =>
      pair (core_sort_encode sort) (pair 0 entry.index)
  | .fvar entry =>
      pair (core_sort_encode sort) (pair 1 entry.index)
  | .app function arguments =>
      pair (core_sort_encode sort)
        (pair 2
          (pair (henkin_function_encode function)
            (arguments_encode arguments)))

def arguments_encode
    {bound free : SortContext (HSignature SearchSignature)}
    {sorts : List SearchSignature.SortSymbol}
    (arguments : Arguments (HSignature SearchSignature) bound free sorts) : Nat :=
  match arguments with
  | .nil => 0
  | .cons head tail =>
      pair (term_encode head) (arguments_encode tail) + 1

end

mutual

private theorem term_encode_eq_core
    {bound free : SortContext (HSignature SearchSignature)} :
    {leftSort rightSort : SearchSignature.SortSymbol} →
      (left : Term (HSignature SearchSignature) bound free leftSort) →
      (right : Term (HSignature SearchSignature) bound free rightSort) →
      term_encode left = term_encode right →
      (⟨leftSort, left⟩ :
        Σ sort, Term (HSignature SearchSignature) bound free sort) =
      ⟨rightSort, right⟩
  | _, _, .bvar leftEntry, .bvar rightEntry, hCode => by
      simp only [term_encode] at hCode
      rcases NatPairing.pair_eq_pair_iff.mp hCode with
        ⟨hSort, hNode⟩
      cases core_sort_encode_injective hSort
      have hIndex := (NatPairing.pair_eq_pair_iff.mp hNode).2
      cases variable_index_injective hIndex
      rfl
  | _, _, .bvar leftEntry, .fvar rightEntry, hCode => by
      simp only [term_encode] at hCode
      have hNode := (NatPairing.pair_eq_pair_iff.mp hCode).2
      have hTag := (NatPairing.pair_eq_pair_iff.mp hNode).1
      omega
  | _, _, .bvar leftEntry, .app rightFunction rightArguments, hCode => by
      simp only [term_encode] at hCode
      have hNode := (NatPairing.pair_eq_pair_iff.mp hCode).2
      have hTag := (NatPairing.pair_eq_pair_iff.mp hNode).1
      omega
  | _, _, .fvar leftEntry, .bvar rightEntry, hCode => by
      simp only [term_encode] at hCode
      have hNode := (NatPairing.pair_eq_pair_iff.mp hCode).2
      have hTag := (NatPairing.pair_eq_pair_iff.mp hNode).1
      omega
  | _, _, .fvar leftEntry, .fvar rightEntry, hCode => by
      simp only [term_encode] at hCode
      rcases NatPairing.pair_eq_pair_iff.mp hCode with
        ⟨hSort, hNode⟩
      cases core_sort_encode_injective hSort
      have hIndex := (NatPairing.pair_eq_pair_iff.mp hNode).2
      cases variable_index_injective hIndex
      rfl
  | _, _, .fvar leftEntry, .app rightFunction rightArguments, hCode => by
      simp only [term_encode] at hCode
      have hNode := (NatPairing.pair_eq_pair_iff.mp hCode).2
      have hTag := (NatPairing.pair_eq_pair_iff.mp hNode).1
      omega
  | _, _, .app leftFunction leftArguments, .bvar rightEntry, hCode => by
      simp only [term_encode] at hCode
      have hNode := (NatPairing.pair_eq_pair_iff.mp hCode).2
      have hTag := (NatPairing.pair_eq_pair_iff.mp hNode).1
      omega
  | _, _, .app leftFunction leftArguments, .fvar rightEntry, hCode => by
      simp only [term_encode] at hCode
      have hNode := (NatPairing.pair_eq_pair_iff.mp hCode).2
      have hTag := (NatPairing.pair_eq_pair_iff.mp hNode).1
      omega
  | _, _, .app leftFunction leftArguments,
      .app rightFunction rightArguments, hCode => by
      simp only [term_encode] at hCode
      have hNode := (NatPairing.pair_eq_pair_iff.mp hCode).2
      have hPayload := (NatPairing.pair_eq_pair_iff.mp hNode).2
      rcases NatPairing.pair_eq_pair_iff.mp hPayload with
        ⟨hFunction, hArguments⟩
      cases henkin_function_encode_injective hFunction
      cases arguments_encode_eq_core leftArguments
        rightArguments hArguments
      rfl

private theorem arguments_encode_eq_core
    {bound free : SortContext (HSignature SearchSignature)} :
    {leftSorts rightSorts : List SearchSignature.SortSymbol} →
      (left : Arguments (HSignature SearchSignature) bound free leftSorts) →
      (right : Arguments (HSignature SearchSignature) bound free rightSorts) →
      arguments_encode left = arguments_encode right →
      (⟨leftSorts, left⟩ :
        Σ sorts, Arguments (HSignature SearchSignature) bound free sorts) =
      ⟨rightSorts, right⟩
  | _, _, .nil, .nil, _ => rfl
  | _, _, .nil, .cons rightHead rightTail, hCode => by
      simp [arguments_encode] at hCode
  | _, _, .cons leftHead leftTail, .nil, hCode => by
      simp [arguments_encode] at hCode
  | _, _, .cons leftHead leftTail,
      .cons rightHead rightTail, hCode => by
      simp only [arguments_encode] at hCode
      have hPair := Nat.add_right_cancel hCode
      rcases NatPairing.pair_eq_pair_iff.mp hPair with
        ⟨hHead, hTail⟩
      cases term_encode_eq_core leftHead rightHead hHead
      cases arguments_encode_eq_core leftTail rightTail hTail
      rfl

end

theorem term_encode_eq
    {bound free : SortContext (HSignature SearchSignature)}
    {sort : SearchSignature.SortSymbol}
    {left right : Term (HSignature SearchSignature) bound free sort}
    (hCode : term_encode left = term_encode right) : left = right :=
  by
    cases term_encode_eq_core left right hCode
    rfl

theorem arguments_encode_eq
    {bound free : SortContext (HSignature SearchSignature)}
    {sorts : List SearchSignature.SortSymbol}
    {left right : Arguments (HSignature SearchSignature) bound free sorts}
    (hCode : arguments_encode left = arguments_encode right) : left = right :=
  by
    cases arguments_encode_eq_core left right hCode
    rfl

private theorem equality_formula_eq_of_codes
    {bound free : SortContext (HSignature SearchSignature)}
    {leftSort rightSort : SearchSignature.SortSymbol}
    {left₁ left₂ :
      Term (HSignature SearchSignature) bound free leftSort}
    {right₁ right₂ :
      Term (HSignature SearchSignature) bound free rightSort}
    (hLeft : term_encode left₁ = term_encode right₁)
    (hRight : term_encode left₂ = term_encode right₂) :
    Formula.equal left₁ left₂ = Formula.equal right₁ right₂ := by
  cases term_encode_eq_core left₁ right₁ hLeft
  cases term_encode_eq_core left₂ right₂ hRight
  rfl

def formula_encode
    {bound free : SortContext (HSignature SearchSignature)} :
    Formula (HSignature SearchSignature) bound free → Nat
  | .falsum => pair 0 0
  | .truth => pair 1 0
  | .rel relation arguments =>
      pair 2
        (pair (relation_symbol_encode relation) (arguments_encode arguments))
  | .equal left right =>
      pair 3 (pair (term_encode left) (term_encode right))
  | .neg body => pair 4 (formula_encode body)
  | .conj left right =>
      pair 5 (pair (formula_encode left) (formula_encode right))
  | .disj left right =>
      pair 6 (pair (formula_encode left) (formula_encode right))
  | .imp left right =>
      pair 7 (pair (formula_encode left) (formula_encode right))
  | .iff left right =>
      pair 8 (pair (formula_encode left) (formula_encode right))
  | .forallE sort body =>
      pair 9 (pair (core_sort_encode sort) (formula_encode body))
  | .existsE sort body =>
      pair 10 (pair (core_sort_encode sort) (formula_encode body))

theorem formula_encode_injective
    {bound free : SortContext (HSignature SearchSignature)} :
    Function.Injective (@formula_encode bound free) := by
  intro left
  induction left with
  | falsum =>
      intro right hCode
      cases right
      case falsum => rfl
      all_goals
        have hTag := (NatPairing.pair_eq_pair_iff.mp hCode).1
        omega
  | truth =>
      intro right hCode
      cases right
      case truth => rfl
      all_goals
        have hTag := (NatPairing.pair_eq_pair_iff.mp hCode).1
        omega
  | rel relation arguments =>
      intro right hCode
      cases right
      case rel relation' arguments' =>
        rcases NatPairing.pair_eq_pair_iff.mp hCode with ⟨_, hPayload⟩
        rcases NatPairing.pair_eq_pair_iff.mp hPayload with
          ⟨hRelation, hArguments⟩
        cases relation_symbol_encode_injective hRelation
        cases arguments_encode_eq hArguments
        rfl
      all_goals
        have hTag := (NatPairing.pair_eq_pair_iff.mp hCode).1
        omega
  | equal left right =>
      intro target hCode
      cases target
      case equal left' right' =>
        rcases NatPairing.pair_eq_pair_iff.mp hCode with ⟨_, hPayload⟩
        rcases NatPairing.pair_eq_pair_iff.mp hPayload with
          ⟨hLeft, hRight⟩
        exact equality_formula_eq_of_codes hLeft hRight
      all_goals
        have hTag := (NatPairing.pair_eq_pair_iff.mp hCode).1
        omega
  | neg body ih =>
      intro right hCode
      cases right
      case neg body' =>
        have hBody := (NatPairing.pair_eq_pair_iff.mp hCode).2
        cases ih hBody
        rfl
      all_goals
        have hTag := (NatPairing.pair_eq_pair_iff.mp hCode).1
        omega
  | conj left right ihLeft ihRight =>
      intro target hCode
      cases target
      case conj left' right' =>
        rcases NatPairing.pair_eq_pair_iff.mp hCode with ⟨_, hPayload⟩
        rcases NatPairing.pair_eq_pair_iff.mp hPayload with
          ⟨hLeft, hRight⟩
        cases ihLeft hLeft
        cases ihRight hRight
        rfl
      all_goals
        have hTag := (NatPairing.pair_eq_pair_iff.mp hCode).1
        omega
  | disj left right ihLeft ihRight =>
      intro target hCode
      cases target
      case disj left' right' =>
        rcases NatPairing.pair_eq_pair_iff.mp hCode with ⟨_, hPayload⟩
        rcases NatPairing.pair_eq_pair_iff.mp hPayload with
          ⟨hLeft, hRight⟩
        cases ihLeft hLeft
        cases ihRight hRight
        rfl
      all_goals
        have hTag := (NatPairing.pair_eq_pair_iff.mp hCode).1
        omega
  | imp left right ihLeft ihRight =>
      intro target hCode
      cases target
      case imp left' right' =>
        rcases NatPairing.pair_eq_pair_iff.mp hCode with ⟨_, hPayload⟩
        rcases NatPairing.pair_eq_pair_iff.mp hPayload with
          ⟨hLeft, hRight⟩
        cases ihLeft hLeft
        cases ihRight hRight
        rfl
      all_goals
        have hTag := (NatPairing.pair_eq_pair_iff.mp hCode).1
        omega
  | iff left right ihLeft ihRight =>
      intro target hCode
      cases target
      case iff left' right' =>
        rcases NatPairing.pair_eq_pair_iff.mp hCode with ⟨_, hPayload⟩
        rcases NatPairing.pair_eq_pair_iff.mp hPayload with
          ⟨hLeft, hRight⟩
        cases ihLeft hLeft
        cases ihRight hRight
        rfl
      all_goals
        have hTag := (NatPairing.pair_eq_pair_iff.mp hCode).1
        omega
  | forallE sort body ih =>
      intro right hCode
      cases right
      case forallE sort' body' =>
        rcases NatPairing.pair_eq_pair_iff.mp hCode with ⟨_, hPayload⟩
        rcases NatPairing.pair_eq_pair_iff.mp hPayload with
          ⟨hSort, hBody⟩
        cases core_sort_encode_injective hSort
        cases ih hBody
        rfl
      all_goals
        have hTag := (NatPairing.pair_eq_pair_iff.mp hCode).1
        omega
  | existsE sort body ih =>
      intro right hCode
      cases right
      case existsE sort' body' =>
        rcases NatPairing.pair_eq_pair_iff.mp hCode with ⟨_, hPayload⟩
        rcases NatPairing.pair_eq_pair_iff.mp hPayload with
          ⟨hSort, hBody⟩
        cases core_sort_encode_injective hSort
        cases ih hBody
        rfl
      all_goals
        have hTag := (NatPairing.pair_eq_pair_iff.mp hCode).1
        omega

def formula_coding :
    NatCoding (Sentence (HSignature SearchSignature)) where
  encode := formula_encode
  injective := formula_encode_injective

/-- ATP 搜索签名上的固定公平 Henkin 调度。 -/
noncomputable def henkin_schedule :
    Completeness.Henkin.Schedule SearchSignature :=
  Completeness.Henkin.Schedule.of_coding formula_coding

end SearchCompleteness

/-! ## checked ATP 语义证书回收到 Derives -/

namespace LogicSoundness
namespace SetLevel
namespace BackendSuccess

/-- checked 后端成功对象经强完备性直接生成标准 Hilbert 推导。 -/
theorem derives
    {problem : DeepProblem SearchMaterialization.SearchSignature}
    (success : BackendSuccess problem) :
    Logic.FirstOrder.Derives problem.theory [] problem.target :=
  _root_.YesMetaZFC.Logic.FirstOrder.Completeness.strong_completeness
    SearchCompleteness.henkin_schedule success.sound

end BackendSuccess
end SetLevel
end LogicSoundness
end Automation
end YesMetaZFC
