import YesMetaZFC.Logic.FirstOrder.FormalSystem.FiniteSequenceConcatenation
/-!
# 一阶形式语言的集合编码
本模块把一阶形式语言本身编码为对象集合论中的有限自然数序列。编码分为三层：
* 原子符号编码：逻辑符号、隶属符号、变量、常元、函数符号和谓词符号；
* 项编码：变量与常元起始，并对有限参数列上的函数应用封闭的最小集合；
* 初始公式编码：等式、隶属原子和一般谓词应用。
文献中的 `XuLe` 直接解释为 `seq_spaceₘ(ωₘ)`，即自然数有限序列空间，不再引入
同义原子。`LJFH`、`WCFH₀`、`BYFH`、`CYFH`、`HSFH`、`WCFH`、`Xng`
与 `XnXL` 仅在注释中保留为检索索引。
文献用自然数递归逐层生成项编码集。这里采用等价但更稳定的最小闭包规格：
`TermCodeₘ` 是包含变量、常元并对函数应用构造封闭的最小集合。这样后续结构
归纳、唯一可读性与自动化都可以直接消费统一的闭包接口，而不必反复展开阶段函数。
本模块只建立定义公理、理论链和 proof-carrying 良构性边界。素数幂编码互不相交、
项构造反演、唯一可读性和对象语言结构归纳留给后续证明模块。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
/-! ## 公共编码积木 -/
/-- 自然数有限序列空间；文献索引为 `XuLe`。 -/
abbrev code_string_space_term : SetTerm :=
  seq_spaceₘ(ωₘ)
/-- 把一个自然数标签编码为长度为一的序列。 -/
abbrev singleton_symbol_code_term (number : SetTerm) :
    SetTerm :=
  {⟨numₘ(0), number⟩ₘ}ₘ
/-- 对有限项列表构造对象语言有限集合。 -/
def finite_set_literal_term :
    List SetTerm → SetTerm
  | [] => ∅ₘ
  | element :: rest =>
      {element}ₘ ∪ₘ finite_set_literal_term rest
/-- 固定素数的对象语言幂项。 -/
abbrev prime_power_code_term (prime : Nat) (exponent : SetTerm) :
    SetTerm :=
  numₘ(prime) ^ₘ exponent
/-- 以 `S(index)` 为指数的素数幂编码。 -/
abbrev indexed_prime_power_code_term (prime : Nat) (index : SetTerm) :
    SetTerm :=
  prime_power_code_term prime (Sₘ(index))
namespace Symbols
/-- 所有自然数有限序列组成的编码字符串空间。 -/
scoped notation:max "CodeStrₘ" =>
  code_string_space_term
/-- 单个自然数标签形成的长度一编码字符串。 -/
scoped notation:max "sym_codeₘ(" number ")" =>
  singleton_symbol_code_term number
end Symbols
open scoped Symbols
/-! ## 逻辑符号与隶属符号 -/
/-- 当前原始逻辑语言采用的八种逻辑符号。 -/
inductive LogicalSymbolKind where
  | equality
  | negation
  | implication
  | universal
  | leftParenthesis
  | rightParenthesis
  | existential
  | conjunction
  deriving DecidableEq, Repr
/-- 逻辑符号在底数 `2` 的幂编码中使用的指数。 -/
def logical_symbol_exponent :
    LogicalSymbolKind → Nat
  | .equality => 1
  | .negation => 2
  | .implication => 3
  | .universal => 4
  | .leftParenthesis => 5
  | .rightParenthesis => 6
  | .existential => 8
  | .conjunction => 9
/-- 八种逻辑符号的固定枚举。 -/
def logical_symbol_kinds :
    List LogicalSymbolKind :=
  [.equality, .negation, .implication, .universal,
    .leftParenthesis, .rightParenthesis, .existential,
    .conjunction]
/-- 一个逻辑符号的自然数标签。 -/
abbrev logical_symbol_number_term (symbol : LogicalSymbolKind) :
    SetTerm :=
  prime_power_code_term
    2 (numₘ(logical_symbol_exponent symbol))
/-- 一个逻辑符号的长度一序列编码。 -/
abbrev logical_symbol_code_term (symbol : LogicalSymbolKind) :
    SetTerm :=
  sym_codeₘ(logical_symbol_number_term symbol)
/-- 八个逻辑符号编码组成的对象语言有限集合。 -/
def logical_symbol_code_terms :
    List SetTerm :=
  logical_symbol_kinds.map logical_symbol_code_term
/-- 等号、括号等逻辑符号编码集合的定义公理；文献索引为 `Ξ₁₀₄a`。 -/
def logical_symbol_set_definition_axiom :
    SetFormula :=
  LogicSymₘ ≐ₘ
    finite_set_literal_term logical_symbol_code_terms
/-- 隶属关系符号的自然数标签 `2⁷`。 -/
abbrev membership_symbol_number_term : SetTerm :=
  prime_power_code_term 2 (numₘ(7))
/-- 隶属关系符号的长度一编码。 -/
abbrev membership_symbol_code_term : SetTerm :=
  sym_codeₘ(membership_symbol_number_term)
/-- 隶属关系符号编码集合的定义公理；文献索引为 `WCFH₀`。 -/
def membership_symbol_set_definition_axiom :
    SetFormula :=
  MembershipSymₘ ≐ₘ
    {membership_symbol_code_term}ₘ
/-- 等号符号的长度一编码。 -/
abbrev equality_symbol_code_term : SetTerm :=
  logical_symbol_code_term .equality
/-- 左括号符号的长度一编码。 -/
abbrev left_parenthesis_symbol_code_term : SetTerm :=
  logical_symbol_code_term .leftParenthesis
/-- 右括号符号的长度一编码。 -/
abbrev right_parenthesis_symbol_code_term : SetTerm :=
  logical_symbol_code_term .rightParenthesis
/-! ## 非逻辑符号族 -/
/-- 第 `index` 个变量符号的自然数标签 `3^(index+1)`。 -/
abbrev variable_symbol_number_term (index : SetTerm) :
    SetTerm :=
  indexed_prime_power_code_term 3 index
/-- 第 `index` 个变量符号的长度一编码。 -/
abbrev variable_symbol_code_term (index : SetTerm) :
    SetTerm :=
  sym_codeₘ(variable_symbol_number_term index)
/-- `symbol` 是某个变量符号编码。 -/
def variable_symbol_condition (symbol : SetTerm) :
    SetFormula := (symbol ∈ₘ CodeStrₘ) ∧ₘ (∃ₘ[SetSort.set, 200], ((x#200 ∈ₘ ωₘ) ∧ₘ (symbol ≐ₘ
          variable_symbol_code_term (x#200))))
/-- 变量符号集合定义公理；文献索引为 `BYFH`、`Ξ₁₀₅`。 -/
def variable_symbol_set_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0], ((x#0 ∈ₘ VarSymₘ) ↔ₘ
      variable_symbol_condition (x#0))
/-- 第 `index` 个常元符号的自然数标签 `5^(index+1)`。 -/
abbrev constant_symbol_number_term (index : SetTerm) :
    SetTerm :=
  indexed_prime_power_code_term 5 index
/-- 第 `index` 个常元符号的长度一编码。 -/
abbrev constant_symbol_code_term (index : SetTerm) :
    SetTerm :=
  sym_codeₘ(constant_symbol_number_term index)
/-- `symbol` 是某个常元符号编码。 -/
def constant_symbol_condition (symbol : SetTerm) :
    SetFormula := (symbol ∈ₘ CodeStrₘ) ∧ₘ (∃ₘ[SetSort.set, 201], ((x#201 ∈ₘ ωₘ) ∧ₘ (symbol ≐ₘ
          constant_symbol_code_term (x#201))))
/-- 常元符号集合定义公理；文献索引为 `CYFH`、`Ξ₁₀₆`。 -/
def constant_symbol_set_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0], ((x#0 ∈ₘ ConstSymₘ) ↔ₘ
      constant_symbol_condition (x#0))
/--
第 `symbolIndex` 个 `(arityPredecessor + 1)` 元函数符号的自然数标签。
-/
abbrev coded_function_symbol_number_term (arityPredecessor symbolIndex : SetTerm) :
    SetTerm :=
  indexed_prime_power_code_term 3 arityPredecessor *ₘ
    indexed_prime_power_code_term 5 symbolIndex
/-- 函数符号的长度一编码。 -/
abbrev coded_function_symbol_code_term (arityPredecessor symbolIndex : SetTerm) :
    SetTerm :=
  sym_codeₘ(
    coded_function_symbol_number_term
      arityPredecessor symbolIndex)
/-- `symbol` 是某个正元数函数符号编码。 -/
def coded_function_symbol_condition (symbol : SetTerm) :
    SetFormula := (symbol ∈ₘ CodeStrₘ) ∧ₘ (∃ₘ[SetSort.set, 202],
      ∃ₘ[SetSort.set, 203], (((x#202 ∈ₘ ωₘ) ∧ₘ (x#203 ∈ₘ ωₘ)) ∧ₘ (symbol ≐ₘ
            coded_function_symbol_code_term (x#202) (x#203))))
/-- 函数符号集合定义公理；文献索引为 `HSFH`、`Ξ₁₀₇`。 -/
def coded_function_symbol_set_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0], ((x#0 ∈ₘ FuncSymₘ) ↔ₘ
      coded_function_symbol_condition (x#0))
/--
第 `symbolIndex` 个 `(arityPredecessor + 1)` 元谓词符号的自然数标签。
-/
abbrev coded_predicate_symbol_number_term (arityPredecessor symbolIndex : SetTerm) :
    SetTerm :=
  indexed_prime_power_code_term 3 arityPredecessor *ₘ
    indexed_prime_power_code_term 7 symbolIndex
/-- 谓词符号的长度一编码。 -/
abbrev coded_predicate_symbol_code_term (arityPredecessor symbolIndex : SetTerm) :
    SetTerm :=
  sym_codeₘ(
    coded_predicate_symbol_number_term
      arityPredecessor symbolIndex)
/-- `symbol` 是某个正元数谓词符号编码。 -/
def coded_predicate_symbol_condition (symbol : SetTerm) :
    SetFormula := (symbol ∈ₘ CodeStrₘ) ∧ₘ (∃ₘ[SetSort.set, 204],
      ∃ₘ[SetSort.set, 205], (((x#204 ∈ₘ ωₘ) ∧ₘ (x#205 ∈ₘ ωₘ)) ∧ₘ (symbol ≐ₘ
            coded_predicate_symbol_code_term (x#204) (x#205))))
/-- 谓词符号集合定义公理；文献索引为 `WCFH`、`Ξ₁₀₈`。 -/
def coded_predicate_symbol_set_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0], ((x#0 ∈ₘ PredSymₘ) ↔ₘ
      coded_predicate_symbol_condition (x#0))
/-! ## 项编码的最小闭包 -/
/--
函数应用项的编码：
`函数符号 ⌢ 左括号 ⌢ 参数列折叠 ⌢ 右括号`。
-/
abbrev term_application_code_term (arityPredecessor symbolIndex arguments : SetTerm) :
    SetTerm := (((coded_function_symbol_code_term
        arityPredecessor symbolIndex ⌢ₘ
      left_parenthesis_symbol_code_term) ⌢ₘ
    flattenₘ(arguments)) ⌢ₘ
  right_parenthesis_symbol_code_term)
/-- `code` 可由 `source` 中的项编码作一次函数应用构造得到。 -/
def term_application_from_condition (source code : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set, 210],
    ∃ₘ[SetSort.set, 211],
      ∃ₘ[SetSort.set, 212], (((x#210 ∈ₘ ωₘ) ∧ₘ ((x#211 ∈ₘ ωₘ) ∧ₘ ((x#212 ∈ₘ
                  seq₊_spaceₘ(CodeStrₘ)) ∧ₘ (domₘ(x#212) ≐ₘ
                  Sₘ(x#210))))) ∧ₘ ((∀ₘ[SetSort.set, 213], (x#213 ∈ₘ domₘ(x#212)) ⟶ₘ ((x#212 ·ₘ x#213) ∈ₘ source)) ∧ₘ (code ≐ₘ
              term_application_code_term (x#210) (x#211) (x#212))))
/-- `candidate` 包含基础项编码，并对函数应用构造封闭。 -/
def term_code_closed_condition (candidate : SetTerm) :
    SetFormula := (VarSymₘ ⊆ₘ candidate) ∧ₘ ((ConstSymₘ ⊆ₘ candidate) ∧ₘ (∀ₘ[SetSort.set, 214],
        term_application_from_condition
            candidate (x#214) ⟶ₘ ((x#214) ∈ₘ candidate)))
/- 项码闭包的单步生成关系，与三个闭包分量逐项对应。 -/
def term_code_generation_condition (candidate code : SetTerm) :
    SetFormula :=
  (code ∈ₘ VarSymₘ) ∨ₘ
    ((code ∈ₘ ConstSymₘ) ∨ₘ
      term_application_from_condition candidate code)
/- 从项码集合中筛出一步生成成员的分离谓词。 -/
def term_code_generation_predicate :
    SetPredicate where
  body :=
    Formula.closeFreeAt SetSort.set 216 0
      (term_code_generation_condition TermCodeₘ (x#216))
  admissible_at := by
    prove_admissible_at
/- 项码反演所需的单个分离实例。 -/
def term_code_generation_separation_axiom : SetFormula :=
  term_code_generation_predicate.separation_axiom
/--
`candidate` 是所有项编码组成的最小闭集，并且其中每个编码都是代码字符串。
子集分量记录项编码的基本类型不变量；最小性仍只在满足同一闭包条件的候选之间比较。
-/
def term_code_set_spec (candidate : SetTerm) :
    SetFormula :=
  term_code_closed_condition candidate ∧ₘ ((candidate ⊆ₘ CodeStrₘ) ∧ₘ (∀ₘ[SetSort.set, 215],
        term_code_closed_condition (x#215) ⟶ₘ (candidate ⊆ₘ (x#215))))
/--
项编码集合定义公理。
该最小闭包与文献的 `T₀ = BYFH ∪ CYFH`、
`Tₙ₊₁ = Tₙ ∪ Y(Tₙ)`、`T = ⋃ₙ Tₙ` 等价。
-/
def term_code_set_definition_axiom :
    SetFormula :=
  term_code_set_spec TermCodeₘ
/-- “是项编码”谓词的定义实例；文献索引为 `Xng`、`Ξ₁₀₉`。 -/
def is_term_code_definition_instance (code : SetTerm) :
    SetFormula :=
  term_codeₘ(code) ↔ₘ (code ∈ₘ TermCodeₘ)
/-- “是项编码”谓词定义公理。 -/
def is_term_code_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    is_term_code_definition_instance (x#0)
/-! ## 非空有限项列 -/
/-- `sequence` 是由项编码组成的非空有限序列。 -/
def term_sequence_condition (sequence : SetTerm) :
    SetFormula := (sequence ∈ₘ seq₊_spaceₘ(CodeStrₘ)) ∧ₘ (∀ₘ[SetSort.set, 220], (x#220 ∈ₘ domₘ(sequence)) ⟶ₘ
        term_codeₘ(sequence ·ₘ x#220))
/-- 非空有限项列集合定义公理；文献索引为 `XnXL`、`Ξ₁₁₀`。 -/
def term_sequence_set_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0], ((x#0 ∈ₘ TermSeqₘ) ↔ₘ
      term_sequence_condition (x#0))
/-! ## 初始公式编码 -/
/-- 二元关系原子编码的公共括号化构造。 -/
abbrev binary_atomic_formula_code_term (relationCode left right : SetTerm) :
    SetTerm := ((((left_parenthesis_symbol_code_term ⌢ₘ
        left) ⌢ₘ
      relationCode) ⌢ₘ
    right) ⌢ₘ
  right_parenthesis_symbol_code_term)
/-- 等式原子的编码。 -/
abbrev equality_atomic_formula_code_term (left right : SetTerm) :
    SetTerm :=
  binary_atomic_formula_code_term
    equality_symbol_code_term left right
/-- 隶属原子的编码。 -/
abbrev membership_atomic_formula_code_term (left right : SetTerm) :
    SetTerm :=
  binary_atomic_formula_code_term
    membership_symbol_code_term left right
/-- 一般谓词应用原子的编码。 -/
abbrev predicate_application_code_term (arityPredecessor symbolIndex arguments : SetTerm) :
    SetTerm := (((coded_predicate_symbol_code_term
        arityPredecessor symbolIndex ⌢ₘ
      left_parenthesis_symbol_code_term) ⌢ₘ
    flattenₘ(arguments)) ⌢ₘ
  right_parenthesis_symbol_code_term)
/-- `code` 是一个一般谓词应用原子的编码。 -/
def predicate_application_code_condition (code : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set, 230],
    ∃ₘ[SetSort.set, 231],
      ∃ₘ[SetSort.set, 232], (((x#230 ∈ₘ ωₘ) ∧ₘ ((x#231 ∈ₘ ωₘ) ∧ₘ ((x#232 ∈ₘ TermSeqₘ) ∧ₘ (domₘ(x#232) ≐ₘ
                  Sₘ(x#230))))) ∧ₘ (code ≐ₘ
            predicate_application_code_term (x#230) (x#231) (x#232)))
/-- `code` 是等式原子或隶属原子的编码。 -/
def binary_atomic_formula_code_condition (code : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set, 233],
    ∃ₘ[SetSort.set, 234], ((term_codeₘ(x#233) ∧ₘ
          term_codeₘ(x#234)) ∧ₘ ((code ≐ₘ
            equality_atomic_formula_code_term (x#233) (x#234)) ∨ₘ (code ≐ₘ
            membership_atomic_formula_code_term (x#233) (x#234))))
/-- 原子公式编码条件。 -/
def atomic_formula_code_condition (code : SetTerm) :
    SetFormula :=
  binary_atomic_formula_code_condition code ∨ₘ
    predicate_application_code_condition code
/-- “是原子公式编码”谓词的定义实例。 -/
def is_atomic_formula_code_definition_instance (code : SetTerm) :
    SetFormula :=
  atomic_formula_codeₘ(code) ↔ₘ
    atomic_formula_code_condition code
/-- “是原子公式编码”谓词定义公理。 -/
def is_atomic_formula_code_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    is_atomic_formula_code_definition_instance (x#0)
/-! ## 理论组合 -/
/-- 加入逻辑符号编码集合后的理论。 -/
def logical_symbol_encoding_theory :
    SetTheory :=
  Theory.insert
    logical_symbol_set_definition_axiom
    finite_sequence_formal_system_theory
/-- 加入隶属关系符号编码集合后的理论。 -/
def membership_symbol_encoding_theory :
    SetTheory :=
  Theory.insert
    membership_symbol_set_definition_axiom
    logical_symbol_encoding_theory
/-- 加入变量符号编码集合后的理论。 -/
def variable_symbol_encoding_theory :
    SetTheory :=
  Theory.insert
    variable_symbol_set_definition_axiom
    membership_symbol_encoding_theory
/-- 加入常元符号编码集合后的理论。 -/
def constant_symbol_encoding_theory :
    SetTheory :=
  Theory.insert
    constant_symbol_set_definition_axiom
    variable_symbol_encoding_theory
/-- 加入函数符号编码集合后的理论。 -/
def function_symbol_encoding_theory :
    SetTheory :=
  Theory.insert
    coded_function_symbol_set_definition_axiom
    constant_symbol_encoding_theory
/-- 加入谓词符号编码集合后的理论。 -/
def predicate_symbol_encoding_theory :
    SetTheory :=
  Theory.insert
    coded_predicate_symbol_set_definition_axiom
    function_symbol_encoding_theory
/-- 原子符号编码层的稳定理论入口。 -/
def formal_language_symbol_theory :
    SetTheory :=
  predicate_symbol_encoding_theory
/-- 加入项编码最小闭包后的理论。 -/
def term_code_set_theory :
    SetTheory :=
  Theory.insert
    term_code_generation_separation_axiom
    (Theory.insert
      term_code_set_definition_axiom
      formal_language_symbol_theory)
/-- 加入项编码原子谓词后的理论。 -/
def term_code_predicate_theory :
    SetTheory :=
  Theory.insert
    is_term_code_definition_axiom
    term_code_set_theory
/-- 加入非空有限项列编码集合后的理论。 -/
def term_sequence_encoding_theory :
    SetTheory :=
  Theory.insert
    term_sequence_set_definition_axiom
    term_code_predicate_theory
/-- 加入原子公式编码谓词后的理论。 -/
def atomic_formula_encoding_theory :
    SetTheory :=
  Theory.insert
    is_atomic_formula_code_definition_axiom
    term_sequence_encoding_theory
/-- 一阶形式语言编码层的稳定理论入口。 -/
def formal_language_encoding_theory :
    SetTheory :=
  atomic_formula_encoding_theory
/-! ## proof-carrying 项边界 -/
theorem code_string_space_term_admissible :
    Term.Admissible
      code_string_space_term
      SetSort.set :=
  finite_sequence_space_term_admissible
    ωₘ omega_term_admissible
theorem finite_set_literal_term_admissible (elements : List SetTerm) (hElements :
      ∀ element, element ∈ elements →
        Term.Admissible element SetSort.set) :
    Term.Admissible (finite_set_literal_term elements)
      SetSort.set := by
  induction elements with
  | nil =>
      exact empty_set_term_admissible
  | cons element rest ih =>
      exact binary_union_term_admissible
        {element}ₘ (finite_set_literal_term rest) (singleton_term_admissible
          element (hElements element (by simp))) (ih (by
          intro member hMember
          exact hElements member (by simp [hMember])))
theorem singleton_symbol_code_term_admissible (number : SetTerm) (hNumber :
      Term.Admissible number SetSort.set) :
    Term.Admissible (singleton_symbol_code_term number)
      SetSort.set :=
  singleton_term_admissible
    ⟨numₘ(0), number⟩ₘ (ordered_pair_term_admissible (numₘ(0)) number (finite_numeral_term_admissible 0)
      hNumber)
theorem prime_power_code_term_admissible (prime : Nat) (exponent : SetTerm) (hExponent :
      Term.Admissible exponent SetSort.set) :
    Term.Admissible (prime_power_code_term prime exponent)
      SetSort.set :=
  natural_exponentiation_term_admissible (numₘ(prime)) exponent (finite_numeral_term_admissible prime)
    hExponent
theorem indexed_prime_power_code_term_admissible (prime : Nat) (index : SetTerm) (hIndex :
      Term.Admissible index SetSort.set) :
    Term.Admissible (indexed_prime_power_code_term prime index)
      SetSort.set :=
  prime_power_code_term_admissible
    prime (Sₘ(index)) (successor_term_admissible index hIndex)
/-- 固定逻辑符号的对象数值项是 admissible 闭项。 -/
theorem logical_symbol_number_term_admissible (symbol : LogicalSymbolKind) :
    Term.Admissible (logical_symbol_number_term symbol)
      SetSort.set :=
  prime_power_code_term_admissible
    2 (numₘ(logical_symbol_exponent symbol)) (finite_numeral_term_admissible (logical_symbol_exponent symbol))
/-- 隶属符号的对象数值项是 admissible 闭项。 -/
theorem membership_symbol_number_term_admissible :
    Term.Admissible
      membership_symbol_number_term
      SetSort.set :=
  prime_power_code_term_admissible
    2 (numₘ(7)) (finite_numeral_term_admissible 7)
/-- 变量符号数值构造保持项 admissibility。 -/
theorem variable_symbol_number_term_admissible (index : SetTerm) (hIndex : Term.Admissible index SetSort.set) :
    Term.Admissible (variable_symbol_number_term index)
      SetSort.set :=
  indexed_prime_power_code_term_admissible
    3 index hIndex
/-- 常元符号数值构造保持项 admissibility。 -/
theorem constant_symbol_number_term_admissible (index : SetTerm) (hIndex : Term.Admissible index SetSort.set) :
    Term.Admissible (constant_symbol_number_term index)
      SetSort.set :=
  indexed_prime_power_code_term_admissible
    5 index hIndex
/-- 函数符号数值构造保持两个编号参数的项 admissibility。 -/
theorem coded_function_symbol_number_term_admissible (arityPredecessor symbolIndex : SetTerm) (hArity : Term.Admissible arityPredecessor SetSort.set)
    (hIndex : Term.Admissible symbolIndex SetSort.set) :
    Term.Admissible (coded_function_symbol_number_term
        arityPredecessor symbolIndex)
      SetSort.set :=
  natural_multiplication_term_admissible (indexed_prime_power_code_term
      3 arityPredecessor) (indexed_prime_power_code_term
      5 symbolIndex) (indexed_prime_power_code_term_admissible
      3 arityPredecessor hArity) (indexed_prime_power_code_term_admissible
      5 symbolIndex hIndex)
/-- 谓词符号数值构造保持两个编号参数的项 admissibility。 -/
theorem coded_predicate_symbol_number_term_admissible (arityPredecessor symbolIndex : SetTerm) (hArity : Term.Admissible arityPredecessor SetSort.set)
    (hIndex : Term.Admissible symbolIndex SetSort.set) :
    Term.Admissible (coded_predicate_symbol_number_term
        arityPredecessor symbolIndex)
      SetSort.set :=
  natural_multiplication_term_admissible (indexed_prime_power_code_term
      3 arityPredecessor) (indexed_prime_power_code_term
      7 symbolIndex) (indexed_prime_power_code_term_admissible
      3 arityPredecessor hArity) (indexed_prime_power_code_term_admissible
      7 symbolIndex hIndex)
theorem logical_symbol_code_term_admissible (symbol : LogicalSymbolKind) :
    Term.Admissible (logical_symbol_code_term symbol)
      SetSort.set :=
  singleton_symbol_code_term_admissible (logical_symbol_number_term symbol) (logical_symbol_number_term_admissible symbol)
theorem membership_symbol_code_term_admissible :
    Term.Admissible
      membership_symbol_code_term
      SetSort.set :=
  singleton_symbol_code_term_admissible
    membership_symbol_number_term
    membership_symbol_number_term_admissible
theorem variable_symbol_code_term_admissible (index : SetTerm) (hIndex :
      Term.Admissible index SetSort.set) :
    Term.Admissible (variable_symbol_code_term index)
      SetSort.set :=
  singleton_symbol_code_term_admissible (variable_symbol_number_term index) (variable_symbol_number_term_admissible
      index hIndex)
theorem constant_symbol_code_term_admissible (index : SetTerm) (hIndex :
      Term.Admissible index SetSort.set) :
    Term.Admissible (constant_symbol_code_term index)
      SetSort.set :=
  singleton_symbol_code_term_admissible (constant_symbol_number_term index) (constant_symbol_number_term_admissible
      index hIndex)
theorem coded_function_symbol_code_term_admissible (arityPredecessor symbolIndex : SetTerm) (hArity :
      Term.Admissible arityPredecessor SetSort.set) (hIndex :
      Term.Admissible symbolIndex SetSort.set) :
    Term.Admissible (coded_function_symbol_code_term
        arityPredecessor symbolIndex)
      SetSort.set :=
  singleton_symbol_code_term_admissible (coded_function_symbol_number_term
      arityPredecessor symbolIndex) (coded_function_symbol_number_term_admissible
      arityPredecessor symbolIndex hArity hIndex)
theorem coded_predicate_symbol_code_term_admissible (arityPredecessor symbolIndex : SetTerm) (hArity :
      Term.Admissible arityPredecessor SetSort.set) (hIndex :
      Term.Admissible symbolIndex SetSort.set) :
    Term.Admissible (coded_predicate_symbol_code_term
        arityPredecessor symbolIndex)
      SetSort.set :=
  singleton_symbol_code_term_admissible (coded_predicate_symbol_number_term
      arityPredecessor symbolIndex) (coded_predicate_symbol_number_term_admissible
      arityPredecessor symbolIndex hArity hIndex)
theorem term_application_code_term_admissible (arityPredecessor symbolIndex arguments : SetTerm) (hArity :
      Term.Admissible arityPredecessor SetSort.set) (hIndex :
      Term.Admissible symbolIndex SetSort.set) (hArguments :
      Term.Admissible arguments SetSort.set) :
    Term.Admissible (term_application_code_term
        arityPredecessor symbolIndex arguments)
      SetSort.set := by
  have hFunction :=
    coded_function_symbol_code_term_admissible
      arityPredecessor symbolIndex hArity hIndex
  have hLeft :=
    logical_symbol_code_term_admissible
      .leftParenthesis
  have hRight :=
    logical_symbol_code_term_admissible
      .rightParenthesis
  have hFlatten :=
    finite_sequence_flatten_term_admissible
      arguments hArguments
  exact finite_sequence_concatenation_term_admissible (((coded_function_symbol_code_term
        arityPredecessor symbolIndex ⌢ₘ
      left_parenthesis_symbol_code_term) ⌢ₘ
      flattenₘ(arguments)))
    right_parenthesis_symbol_code_term (finite_sequence_concatenation_term_admissible (coded_function_symbol_code_term
          arityPredecessor symbolIndex ⌢ₘ
        left_parenthesis_symbol_code_term) (flattenₘ(arguments)) (finite_sequence_concatenation_term_admissible (coded_function_symbol_code_term
          arityPredecessor symbolIndex)
        left_parenthesis_symbol_code_term
        hFunction hLeft)
      hFlatten)
    hRight
theorem binary_atomic_formula_code_term_admissible (relationCode left right : SetTerm) (hRelation :
      Term.Admissible relationCode SetSort.set) (hLeft :
      Term.Admissible left SetSort.set) (hRight :
      Term.Admissible right SetSort.set) :
    Term.Admissible (binary_atomic_formula_code_term
        relationCode left right)
      SetSort.set := by
  have hOpen :=
    logical_symbol_code_term_admissible
      .leftParenthesis
  have hClose :=
    logical_symbol_code_term_admissible
      .rightParenthesis
  exact finite_sequence_concatenation_term_admissible ((((left_parenthesis_symbol_code_term ⌢ₘ
        left) ⌢ₘ relationCode) ⌢ₘ right))
    right_parenthesis_symbol_code_term (finite_sequence_concatenation_term_admissible (((left_parenthesis_symbol_code_term ⌢ₘ
          left) ⌢ₘ relationCode))
      right (finite_sequence_concatenation_term_admissible (left_parenthesis_symbol_code_term ⌢ₘ
          left)
        relationCode (finite_sequence_concatenation_term_admissible
          left_parenthesis_symbol_code_term
          left hOpen hLeft)
        hRelation)
      hRight)
    hClose
theorem predicate_application_code_term_admissible (arityPredecessor symbolIndex arguments : SetTerm) (hArity :
      Term.Admissible arityPredecessor SetSort.set) (hIndex :
      Term.Admissible symbolIndex SetSort.set) (hArguments :
      Term.Admissible arguments SetSort.set) :
    Term.Admissible (predicate_application_code_term
        arityPredecessor symbolIndex arguments)
      SetSort.set := by
  have hPredicate :=
    coded_predicate_symbol_code_term_admissible
      arityPredecessor symbolIndex hArity hIndex
  have hLeft :=
    logical_symbol_code_term_admissible
      .leftParenthesis
  have hRight :=
    logical_symbol_code_term_admissible
      .rightParenthesis
  have hFlatten :=
    finite_sequence_flatten_term_admissible
      arguments hArguments
  exact finite_sequence_concatenation_term_admissible (((coded_predicate_symbol_code_term
        arityPredecessor symbolIndex ⌢ₘ
      left_parenthesis_symbol_code_term) ⌢ₘ
      flattenₘ(arguments)))
    right_parenthesis_symbol_code_term (finite_sequence_concatenation_term_admissible (coded_predicate_symbol_code_term
          arityPredecessor symbolIndex ⌢ₘ
        left_parenthesis_symbol_code_term) (flattenₘ(arguments)) (finite_sequence_concatenation_term_admissible (coded_predicate_symbol_code_term
          arityPredecessor symbolIndex)
        left_parenthesis_symbol_code_term
        hPredicate hLeft)
      hFlatten)
    hRight
/-! ## 原子常元项边界 -/
theorem logical_symbol_set_term_admissible :
    Term.Admissible LogicSymₘ SetSort.set := by
  simpa using
    set_function_application_admissible
      .logicalSymbolSet []
      (by rfl) (by rfl)
theorem membership_symbol_set_term_admissible :
    Term.Admissible MembershipSymₘ SetSort.set := by
  simpa using
    set_function_application_admissible
      .membershipSymbolSet []
      (by rfl) (by rfl)
theorem variable_symbol_set_term_admissible :
    Term.Admissible VarSymₘ SetSort.set := by
  simpa using
    set_function_application_admissible
      .variableSymbolSet []
      (by rfl) (by rfl)
theorem constant_symbol_set_term_admissible :
    Term.Admissible ConstSymₘ SetSort.set := by
  simpa using
    set_function_application_admissible
      .constantSymbolSet []
      (by rfl) (by rfl)
theorem coded_function_symbol_set_term_admissible :
    Term.Admissible FuncSymₘ SetSort.set := by
  simpa using
    set_function_application_admissible
      .codedFunctionSymbolSet []
      (by rfl) (by rfl)
theorem coded_predicate_symbol_set_term_admissible :
    Term.Admissible PredSymₘ SetSort.set := by
  simpa using
    set_function_application_admissible
      .codedPredicateSymbolSet []
      (by rfl) (by rfl)
theorem term_code_set_term_admissible :
    Term.Admissible TermCodeₘ SetSort.set := by
  simpa using
    set_function_application_admissible
      .termCodeSet []
      (by rfl) (by rfl)
theorem term_sequence_set_term_admissible :
    Term.Admissible TermSeqₘ SetSort.set := by
  simpa using
    set_function_application_admissible
      .termSequenceSet []
      (by rfl) (by rfl)
/-! ## 良构性与理论边界 -/
theorem logical_symbol_set_definition_axiom_admissible :
    Formula.Admissible
      logical_symbol_set_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem membership_symbol_set_definition_axiom_admissible :
    Formula.Admissible
      membership_symbol_set_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem variable_symbol_set_definition_axiom_admissible :
    Formula.Admissible
      variable_symbol_set_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem constant_symbol_set_definition_axiom_admissible :
    Formula.Admissible
      constant_symbol_set_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem coded_function_symbol_set_definition_axiom_admissible :
    Formula.Admissible
      coded_function_symbol_set_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem coded_predicate_symbol_set_definition_axiom_admissible :
    Formula.Admissible
      coded_predicate_symbol_set_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem term_code_set_definition_axiom_admissible :
    Formula.Admissible
      term_code_set_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem term_code_generation_separation_axiom_admissible :
    Formula.Admissible
      term_code_generation_separation_axiom :=
  term_code_generation_predicate.separation_axiom_admissible
theorem is_term_code_definition_axiom_admissible :
    Formula.Admissible
      is_term_code_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem term_sequence_set_definition_axiom_admissible :
    Formula.Admissible
      term_sequence_set_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem is_atomic_formula_code_definition_axiom_admissible :
    Formula.Admissible
      is_atomic_formula_code_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem logical_symbol_encoding_theory_admissible :
    Theory.Admissible logical_symbol_encoding_theory :=
  Theory.admissible_insert
    logical_symbol_set_definition_axiom_admissible
    finite_sequence_formal_system_theory_admissible
theorem membership_symbol_encoding_theory_admissible :
    Theory.Admissible membership_symbol_encoding_theory :=
  Theory.admissible_insert
    membership_symbol_set_definition_axiom_admissible
    logical_symbol_encoding_theory_admissible
theorem variable_symbol_encoding_theory_admissible :
    Theory.Admissible variable_symbol_encoding_theory :=
  Theory.admissible_insert
    variable_symbol_set_definition_axiom_admissible
    membership_symbol_encoding_theory_admissible
theorem constant_symbol_encoding_theory_admissible :
    Theory.Admissible constant_symbol_encoding_theory :=
  Theory.admissible_insert
    constant_symbol_set_definition_axiom_admissible
    variable_symbol_encoding_theory_admissible
theorem function_symbol_encoding_theory_admissible :
    Theory.Admissible function_symbol_encoding_theory :=
  Theory.admissible_insert
    coded_function_symbol_set_definition_axiom_admissible
    constant_symbol_encoding_theory_admissible
theorem predicate_symbol_encoding_theory_admissible :
    Theory.Admissible predicate_symbol_encoding_theory :=
  Theory.admissible_insert
    coded_predicate_symbol_set_definition_axiom_admissible
    function_symbol_encoding_theory_admissible
theorem formal_language_symbol_theory_admissible :
    Theory.Admissible formal_language_symbol_theory :=
  predicate_symbol_encoding_theory_admissible
theorem term_code_set_theory_admissible :
    Theory.Admissible term_code_set_theory :=
  Theory.admissible_insert
    term_code_generation_separation_axiom_admissible
    (Theory.admissible_insert
      term_code_set_definition_axiom_admissible
      formal_language_symbol_theory_admissible)
theorem term_code_predicate_theory_admissible :
    Theory.Admissible term_code_predicate_theory :=
  Theory.admissible_insert
    is_term_code_definition_axiom_admissible
    term_code_set_theory_admissible
theorem term_sequence_encoding_theory_admissible :
    Theory.Admissible term_sequence_encoding_theory :=
  Theory.admissible_insert
    term_sequence_set_definition_axiom_admissible
    term_code_predicate_theory_admissible
theorem atomic_formula_encoding_theory_admissible :
    Theory.Admissible atomic_formula_encoding_theory :=
  Theory.admissible_insert
    is_atomic_formula_code_definition_axiom_admissible
    term_sequence_encoding_theory_admissible
theorem formal_language_encoding_theory_admissible :
    Theory.Admissible formal_language_encoding_theory :=
  atomic_formula_encoding_theory_admissible
/-! ## 闭理论边界 -/
@[derive_close_sentence]
theorem logical_symbol_encoding_theory_sentence
    {formula : SetFormula} (hFormula : logical_symbol_encoding_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact logical_symbol_set_definition_axiom_admissible
    · native_decide
  · exact finite_sequence_formal_system_theory_sentence hFormula
@[derive_close_sentence]
theorem membership_symbol_encoding_theory_sentence
    {formula : SetFormula} (hFormula : membership_symbol_encoding_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact membership_symbol_set_definition_axiom_admissible
    · native_decide
  · exact logical_symbol_encoding_theory_sentence hFormula
@[derive_close_sentence]
theorem variable_symbol_encoding_theory_sentence
    {formula : SetFormula} (hFormula : variable_symbol_encoding_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact variable_symbol_set_definition_axiom_admissible
    · native_decide
  · exact membership_symbol_encoding_theory_sentence hFormula
@[derive_close_sentence]
theorem constant_symbol_encoding_theory_sentence
    {formula : SetFormula} (hFormula : constant_symbol_encoding_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact constant_symbol_set_definition_axiom_admissible
    · native_decide
  · exact variable_symbol_encoding_theory_sentence hFormula
@[derive_close_sentence]
theorem function_symbol_encoding_theory_sentence
    {formula : SetFormula} (hFormula : function_symbol_encoding_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact coded_function_symbol_set_definition_axiom_admissible
    · native_decide
  · exact constant_symbol_encoding_theory_sentence hFormula
@[derive_close_sentence]
theorem predicate_symbol_encoding_theory_sentence
    {formula : SetFormula} (hFormula : predicate_symbol_encoding_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact coded_predicate_symbol_set_definition_axiom_admissible
    · native_decide
  · exact function_symbol_encoding_theory_sentence hFormula
@[derive_close_sentence]
theorem formal_language_symbol_theory_sentence
    {formula : SetFormula} (hFormula : formal_language_symbol_theory formula) :
    Formula.Sentence formula :=
  predicate_symbol_encoding_theory_sentence hFormula
@[derive_close_sentence]
theorem term_code_set_theory_sentence
    {formula : SetFormula} (hFormula : term_code_set_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact term_code_generation_separation_axiom_admissible
    · native_decide
  · rcases hFormula with rfl | hFormula
    · constructor
      · exact term_code_set_definition_axiom_admissible
      · native_decide
    · exact formal_language_symbol_theory_sentence hFormula
@[derive_close_sentence]
theorem term_code_predicate_theory_sentence
    {formula : SetFormula} (hFormula : term_code_predicate_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact is_term_code_definition_axiom_admissible
    · native_decide
  · exact term_code_set_theory_sentence hFormula
@[derive_close_sentence]
theorem term_sequence_encoding_theory_sentence
    {formula : SetFormula} (hFormula : term_sequence_encoding_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact term_sequence_set_definition_axiom_admissible
    · native_decide
  · exact term_code_predicate_theory_sentence hFormula
@[derive_close_sentence]
theorem atomic_formula_encoding_theory_sentence
    {formula : SetFormula} (hFormula : atomic_formula_encoding_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact is_atomic_formula_code_definition_axiom_admissible
    · native_decide
  · exact term_sequence_encoding_theory_sentence hFormula
@[derive_close_sentence]
theorem formal_language_encoding_theory_sentence
    {formula : SetFormula} (hFormula : formal_language_encoding_theory formula) :
    Formula.Sentence formula :=
  atomic_formula_encoding_theory_sentence hFormula
/-! ## 理论嵌入 -/
theorem finite_sequence_formal_system_theory_subset_logical_symbol_encoding_theory
    {formula : SetFormula} (hFormula : finite_sequence_formal_system_theory formula) :
    logical_symbol_encoding_theory formula :=
  Or.inr hFormula
theorem logical_symbol_encoding_theory_subset_membership_symbol_encoding_theory
    {formula : SetFormula} (hFormula : logical_symbol_encoding_theory formula) :
    membership_symbol_encoding_theory formula :=
  Or.inr hFormula
theorem membership_symbol_encoding_theory_subset_variable_symbol_encoding_theory
    {formula : SetFormula} (hFormula : membership_symbol_encoding_theory formula) :
    variable_symbol_encoding_theory formula :=
  Or.inr hFormula
theorem variable_symbol_encoding_theory_subset_constant_symbol_encoding_theory
    {formula : SetFormula} (hFormula : variable_symbol_encoding_theory formula) :
    constant_symbol_encoding_theory formula :=
  Or.inr hFormula
theorem constant_symbol_encoding_theory_subset_function_symbol_encoding_theory
    {formula : SetFormula} (hFormula : constant_symbol_encoding_theory formula) :
    function_symbol_encoding_theory formula :=
  Or.inr hFormula
theorem function_symbol_encoding_theory_subset_formal_language_symbol_theory
    {formula : SetFormula} (hFormula : function_symbol_encoding_theory formula) :
    formal_language_symbol_theory formula :=
  Or.inr hFormula
theorem formal_language_symbol_theory_subset_term_code_set_theory
    {formula : SetFormula} (hFormula : formal_language_symbol_theory formula) :
    term_code_set_theory formula :=
  Or.inr <| Or.inr hFormula
theorem term_code_set_theory_subset_term_code_predicate_theory
    {formula : SetFormula} (hFormula : term_code_set_theory formula) :
    term_code_predicate_theory formula :=
  Or.inr hFormula
theorem term_code_predicate_theory_subset_term_sequence_encoding_theory
    {formula : SetFormula} (hFormula : term_code_predicate_theory formula) :
    term_sequence_encoding_theory formula :=
  Or.inr hFormula
theorem term_sequence_encoding_theory_subset_formal_language_encoding_theory
    {formula : SetFormula} (hFormula : term_sequence_encoding_theory formula) :
    formal_language_encoding_theory formula :=
  Or.inr hFormula
/-! ## 待证明定理索引 -/
/-!
后续证明层将基于本模块处理：
* 六类符号编码的两两不交与素数幂反演；
* `TermCodeₘ` 与文献自然数阶段并集构造的等价性；
* 变量、常元和函数应用项的生成、反演与结构归纳；
* `TermSeqₘ` 对参数列操作的闭性；
* 等式、隶属和谓词应用原子的构造互斥性；
* 初始表达式唯一可读性，即构造标签与各参数编码的唯一恢复。
这些定理会使用 `prove_auto` 压缩逻辑骨架，但素数幂唯一分解、闭包最小性与
搜索器可能自举的关键反演步骤保留手工证明。
-/
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
