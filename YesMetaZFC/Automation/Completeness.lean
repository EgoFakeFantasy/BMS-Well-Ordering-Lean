import YesMetaZFC.Automation.SearchMaterialization
import YesMetaZFC.Logic.FirstOrder.Completeness
/-!
# 自动化后端的完备性接口
本模块为 ATP 实际消费的 `SearchMaterialization.SearchSignature` 建立完整自然数编码，
再把它提升为固定公平 Henkin 调度。后续同一模块负责把 checked 语义后端结果通过
强完备性回收到 `Derives`。
编码覆盖整个签名和原始 LN 公式，不依赖某次问题中临时出现的有限符号表。
-/
namespace YesMetaZFC
namespace Automation
namespace SearchCompleteness
open _root_.YesMetaZFC.Logic
open _root_.YesMetaZFC.Logic.FirstOrder
open _root_.YesMetaZFC.Logic.FirstOrder.Completeness.Henkin
abbrev SearchSignature := SearchMaterialization.SearchSignature
abbrev SearchTerm := Logic.FirstOrder.Term SearchSignature
abbrev SearchFormula := Logic.FirstOrder.Formula SearchSignature
private abbrev pair := NatPairing.pair
/-! ## 实际搜索签名的符号编码 -/
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
def symbol_kind_coding : NatCoding CoreSyntax.Search.SymbolKind where
  encode := symbol_kind_encode
  injective := symbol_kind_encode_injective
def function_symbol_encode (symbol : CoreSyntax.Search.FunctionSymbol) : Nat :=
  pair symbol.id <|
    pair symbol.arity <|
      pair (symbol_kind_encode symbol.kind) <|
        pair ((NatCoding.list core_sort_coding).encode symbol.inputSorts) (core_sort_encode symbol.outputSort)
theorem function_symbol_encode_injective :
    Function.Injective function_symbol_encode := by
  rintro ⟨id, arity, kind, inputSorts, outputSort⟩
    ⟨id', arity', kind', inputSorts', outputSort'⟩ hCode
  unfold function_symbol_encode at hCode
  rcases NatPairing.pair_eq_pair_iff.mp hCode with ⟨hId, hCode⟩
  rcases NatPairing.pair_eq_pair_iff.mp hCode with ⟨hArity, hCode⟩
  rcases NatPairing.pair_eq_pair_iff.mp hCode with ⟨hKind, hCode⟩
  rcases NatPairing.pair_eq_pair_iff.mp hCode with ⟨hInputs, hOutput⟩
  have hKind' := symbol_kind_encode_injective hKind
  have hInputs' := (NatCoding.list core_sort_coding).injective hInputs
  have hOutput' := core_sort_encode_injective hOutput
  cases hId
  cases hArity
  cases hKind'
  cases hInputs'
  cases hOutput'
  rfl
def function_symbol_coding : NatCoding CoreSyntax.Search.FunctionSymbol where
  encode := function_symbol_encode
  injective := function_symbol_encode_injective
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
      pair (predicate_role_encode symbol.role) ((NatCoding.list core_sort_coding).encode symbol.inputSorts)
theorem predicate_symbol_encode_injective :
    Function.Injective predicate_symbol_encode := by
  rintro ⟨id, arity, role, inputSorts⟩
    ⟨id', arity', role', inputSorts'⟩ hCode
  unfold predicate_symbol_encode at hCode
  rcases NatPairing.pair_eq_pair_iff.mp hCode with ⟨hId, hCode⟩
  rcases NatPairing.pair_eq_pair_iff.mp hCode with ⟨hArity, hCode⟩
  rcases NatPairing.pair_eq_pair_iff.mp hCode with ⟨hRole, hInputs⟩
  have hRole' := predicate_role_encode_injective hRole
  have hInputs' := (NatCoding.list core_sort_coding).injective hInputs
  cases hId
  cases hArity
  cases hRole'
  cases hInputs'
  rfl
def predicate_symbol_coding : NatCoding CoreSyntax.PredicateSymbol where
  encode := predicate_symbol_encode
  injective := predicate_symbol_encode_injective
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
def relation_symbol_coding : NatCoding SearchMaterialization.RelSymbol where
  encode := relation_symbol_encode
  injective := relation_symbol_encode_injective
/-! ## LN 项编码 -/
mutual
  def term_size : SearchTerm → Nat
    | .var _ => 1
    | .app _ arguments => term_list_size arguments + 1
  def term_list_size : List SearchTerm → Nat
    | [] => 0
    | term :: rest => term_size term + term_list_size rest + 1
end
mutual
  def term_encode : SearchTerm → Nat
    | .var (.bvar sort index) =>
        pair 0 (pair (core_sort_encode sort) index)
    | .var (.fvar sort id) =>
        pair 1 (pair (core_sort_encode sort) id)
    | .app function arguments =>
        pair 2 (pair (function_symbol_encode function) (term_list_encode arguments))
  def term_list_encode : List SearchTerm → Nat
    | [] => 0
    | term :: rest =>
        pair (term_encode term) (term_list_encode rest) + 1
end
mutual
  theorem term_encode_eq :
      ∀ {left right : SearchTerm},
        term_encode left = term_encode right → left = right
    | .var (.bvar sort index), .var (.bvar sort' index'), hCode => by
        rcases NatPairing.pair_eq_pair_iff.mp hCode with ⟨_, hPayload⟩
        rcases NatPairing.pair_eq_pair_iff.mp hPayload with
          ⟨hSort, hIndex⟩
        rw [core_sort_encode_injective hSort, hIndex]
    | .var (.bvar ..), .var (.fvar ..), hCode => by
        have hTag := (NatPairing.pair_eq_pair_iff.mp hCode).1
        omega
    | .var (.bvar ..), .app .., hCode => by
        have hTag := (NatPairing.pair_eq_pair_iff.mp hCode).1
        omega
    | .var (.fvar ..), .var (.bvar ..), hCode => by
        have hTag := (NatPairing.pair_eq_pair_iff.mp hCode).1
        omega
    | .var (.fvar sort id), .var (.fvar sort' id'), hCode => by
        rcases NatPairing.pair_eq_pair_iff.mp hCode with ⟨_, hPayload⟩
        rcases NatPairing.pair_eq_pair_iff.mp hPayload with
          ⟨hSort, hId⟩
        rw [core_sort_encode_injective hSort, hId]
    | .var (.fvar ..), .app .., hCode => by
        have hTag := (NatPairing.pair_eq_pair_iff.mp hCode).1
        omega
    | .app .., .var (.bvar ..), hCode => by
        have hTag := (NatPairing.pair_eq_pair_iff.mp hCode).1
        omega
    | .app .., .var (.fvar ..), hCode => by
        have hTag := (NatPairing.pair_eq_pair_iff.mp hCode).1
        omega
    | .app function arguments, .app function' arguments', hCode => by
        rcases NatPairing.pair_eq_pair_iff.mp hCode with ⟨_, hPayload⟩
        rcases NatPairing.pair_eq_pair_iff.mp hPayload with
          ⟨hFunction, hArguments⟩
        rw [function_symbol_encode_injective hFunction,
          term_list_encode_eq hArguments]
  termination_by left right _ => term_size left + term_size right
  decreasing_by
    all_goals simp [term_size]
    all_goals omega
  theorem term_list_encode_eq :
      ∀ {left right : List SearchTerm},
        term_list_encode left = term_list_encode right → left = right
    | [], [], _ => rfl
    | [], _ :: _, hCode => by
        simp [term_list_encode] at hCode
    | _ :: _, [], hCode => by
        simp [term_list_encode] at hCode
    | head :: tail, head' :: tail', hCode => by
        simp only [term_list_encode] at hCode
        have hPair := Nat.add_right_cancel hCode
        rcases NatPairing.pair_eq_pair_iff.mp hPair with
          ⟨hHead, hTail⟩
        rw [term_encode_eq hHead, term_list_encode_eq hTail]
  termination_by left right _ => term_list_size left + term_list_size right
  decreasing_by
    all_goals simp [term_list_size]
    all_goals omega
end
theorem term_encode_injective :
    Function.Injective term_encode :=
  fun _ _ => term_encode_eq
theorem term_list_encode_injective :
    Function.Injective term_list_encode :=
  fun _ _ => term_list_encode_eq
def term_coding : NatCoding SearchTerm where
  encode := term_encode
  injective := term_encode_injective
def term_list_coding : NatCoding (List SearchTerm) where
  encode := term_list_encode
  injective := term_list_encode_injective
/-! ## LN 公式编码与公平 schedule -/
def formula_encode : SearchFormula → Nat
  | .falsum => pair 0 0
  | .truth => pair 1 0
  | .rel relation arguments =>
      pair 2 (pair (relation_symbol_encode relation) (term_list_encode arguments))
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
theorem formula_encode_injective :
    Function.Injective formula_encode := by
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
        rw [relation_symbol_encode_injective hRelation,
          term_list_encode_injective hArguments]
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
        rw [term_encode_injective hLeft, term_encode_injective hRight]
      all_goals
        have hTag := (NatPairing.pair_eq_pair_iff.mp hCode).1
        omega
  | neg body ih =>
      intro right hCode
      cases right
      case neg body' =>
        have hBody := (NatPairing.pair_eq_pair_iff.mp hCode).2
        rw [ih hBody]
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
        rw [ihLeft hLeft, ihRight hRight]
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
        rw [ihLeft hLeft, ihRight hRight]
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
        rw [ihLeft hLeft, ihRight hRight]
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
        rw [ihLeft hLeft, ihRight hRight]
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
        rw [core_sort_encode_injective hSort, ih hBody]
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
        rw [core_sort_encode_injective hSort, ih hBody]
      all_goals
        have hTag := (NatPairing.pair_eq_pair_iff.mp hCode).1
        omega
def formula_coding : NatCoding SearchFormula where
  encode := formula_encode
  injective := formula_encode_injective
/--
ATP 实际签名上的固定公平 Henkin 调度。
它覆盖整个 `SearchSignature` 的全部 admissible 公式，而非单次搜索问题的有限切片。
-/
noncomputable def henkin_schedule :
    Completeness.Henkin.Schedule SearchSignature :=
  Completeness.Henkin.Schedule.of_coding formula_coding
/-! ## ATP 闭合边界到证明层句子 -/
mutual
  theorem term_freeSupport_eq_nil_of_freeClosed :
      ∀ {term : SearchTerm}, DAGCertificate.Term.FreeClosed term →
        Logic.FirstOrder.Term.freeSupport term = []
    | .var (.bvar ..), _ => rfl
    | .var (.fvar ..), hClosed => by
        simp [DAGCertificate.Term.FreeClosed] at hClosed
    | .app _ arguments, hClosed => by
        have hArguments :
            ∀ term, term ∈ arguments →
              DAGCertificate.Term.FreeClosed term := by
          simpa [DAGCertificate.Term.FreeClosed] using hClosed
        exact term_list_freeSupport_eq_nil_of_freeClosed hArguments
  termination_by term => term_size term
  decreasing_by
    simp [term_size]
  theorem term_list_freeSupport_eq_nil_of_freeClosed :
      ∀ {terms : List SearchTerm}, (∀ term, term ∈ terms → DAGCertificate.Term.FreeClosed term) →
          Logic.FirstOrder.Term.freeSupportList terms = []
    | [], _ => rfl
    | head :: tail, hClosed => by
        simp only [Logic.FirstOrder.Term.freeSupportList]
        rw [term_freeSupport_eq_nil_of_freeClosed (hClosed head (by simp))]
        simp only [List.nil_append]
        apply term_list_freeSupport_eq_nil_of_freeClosed
        intro term hTerm
        exact hClosed term (by simp [hTerm])
  termination_by terms => term_list_size terms
  decreasing_by
    all_goals simp [term_list_size]
    all_goals omega
end
theorem formula_freeSupport_eq_nil_of_freeClosed {formula : SearchFormula} (hClosed : DAGCertificate.Formula.FreeClosed formula) :
    Logic.FirstOrder.Formula.freeSupport formula = [] := by
  induction formula with
  | falsum =>
      rfl
  | truth =>
      rfl
  | rel relation arguments =>
      have hArguments :
          ∀ term, term ∈ arguments →
            DAGCertificate.Term.FreeClosed term := by
        simpa [DAGCertificate.Formula.FreeClosed] using hClosed
      exact term_list_freeSupport_eq_nil_of_freeClosed hArguments
  | equal left right =>
      have hTerms :
          DAGCertificate.Term.FreeClosed left ∧
            DAGCertificate.Term.FreeClosed right := by
        simpa [DAGCertificate.Formula.FreeClosed] using hClosed
      simp only [Logic.FirstOrder.Formula.freeSupport]
      rw [term_freeSupport_eq_nil_of_freeClosed hTerms.1,
        term_freeSupport_eq_nil_of_freeClosed hTerms.2]
      rfl
  | neg body ih =>
      have hBody : DAGCertificate.Formula.FreeClosed body := by
        simpa [DAGCertificate.Formula.FreeClosed] using hClosed
      exact ih hBody
  | conj left right ihLeft ihRight =>
      have hBoth :
          DAGCertificate.Formula.FreeClosed left ∧
            DAGCertificate.Formula.FreeClosed right := by
        simpa [DAGCertificate.Formula.FreeClosed] using hClosed
      simp only [Logic.FirstOrder.Formula.freeSupport]
      rw [ihLeft hBoth.1, ihRight hBoth.2]
      rfl
  | disj left right ihLeft ihRight =>
      have hBoth :
          DAGCertificate.Formula.FreeClosed left ∧
            DAGCertificate.Formula.FreeClosed right := by
        simpa [DAGCertificate.Formula.FreeClosed] using hClosed
      simp only [Logic.FirstOrder.Formula.freeSupport]
      rw [ihLeft hBoth.1, ihRight hBoth.2]
      rfl
  | imp left right ihLeft ihRight =>
      have hBoth :
          DAGCertificate.Formula.FreeClosed left ∧
            DAGCertificate.Formula.FreeClosed right := by
        simpa [DAGCertificate.Formula.FreeClosed] using hClosed
      simp only [Logic.FirstOrder.Formula.freeSupport]
      rw [ihLeft hBoth.1, ihRight hBoth.2]
      rfl
  | iff left right ihLeft ihRight =>
      have hBoth :
          DAGCertificate.Formula.FreeClosed left ∧
            DAGCertificate.Formula.FreeClosed right := by
        simpa [DAGCertificate.Formula.FreeClosed] using hClosed
      simp only [Logic.FirstOrder.Formula.freeSupport]
      rw [ihLeft hBoth.1, ihRight hBoth.2]
      rfl
  | forallE sort body ih =>
      have hBody : DAGCertificate.Formula.FreeClosed body := by
        simpa [DAGCertificate.Formula.FreeClosed] using hClosed
      exact ih hBody
  | existsE sort body ih =>
      have hBody : DAGCertificate.Formula.FreeClosed body := by
        simpa [DAGCertificate.Formula.FreeClosed] using hClosed
      exact ih hBody
theorem formula_sentence_of_admissible_of_freeClosed {formula : SearchFormula} (hAdmissible : Logic.FirstOrder.Formula.Admissible formula)
    (hClosed : DAGCertificate.Formula.FreeClosed formula) :
    Logic.FirstOrder.Formula.Sentence formula :=
  ⟨hAdmissible, formula_freeSupport_eq_nil_of_freeClosed hClosed⟩
end SearchCompleteness
/-! ## checked ATP 语义证书回收到 Derives -/
namespace LogicSoundness
namespace SetLevel
namespace BackendSuccess
/--
SearchSignature 上的 closed checked 后端成功对象通过强完备性直接生成 `Derives`。
搜索与 DAG checker 仍只负责构造语义证书；从语义证书到推导的最后一步统一经过
Henkin 强完备性，不向对象证明核加入新的 replay 规则。
-/
theorem derives_of_freeClosed
    {problem : DeepProblem SearchMaterialization.SearchSignature} (success : BackendSuccess problem) (hClosed : DAGCertificate.DeepProblem.FreeClosed problem) :
    Logic.FirstOrder.Derives problem.theory [] problem.target := by
  apply _root_.YesMetaZFC.Logic.FirstOrder.Completeness.Henkin.strong_completeness
      SearchCompleteness.henkin_schedule
  · intro formula hFormula
    exact success.admissible.2 formula hFormula
  · intro formula hFormula
    exact SearchCompleteness.formula_sentence_of_admissible_of_freeClosed (success.admissible.2 formula hFormula) (hClosed.2 formula hFormula)
  · exact success.admissible.1
  · exact success.sound
theorem derives_of_freeClosed_check
    {problem : DeepProblem SearchMaterialization.SearchSignature} (success : BackendSuccess problem)
    (hClosed : DAGCertificate.DeepProblem.freeClosed problem = true) :
    Logic.FirstOrder.Derives problem.theory [] problem.target :=
  derives_of_freeClosed success (DAGCertificate.DeepProblem.freeClosed_sound hClosed)
end BackendSuccess
end SetLevel
end LogicSoundness
end Automation
end YesMetaZFC
