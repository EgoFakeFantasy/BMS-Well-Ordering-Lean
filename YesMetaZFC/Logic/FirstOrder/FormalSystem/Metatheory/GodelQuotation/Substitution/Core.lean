import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue
/-!
# Gödel 符号串替换的计算核心
本模块把逐位置替换落实为可计算的标准 `List Nat` 运算：
* 命中目标变量标签时，当前位置分片是完整替换串；
* 未命中时，当前位置分片是只含原标签的单元素串；
* 最终结果是全部分片按顺序 `flatten`；
* 项和 Hilbert 公式的 quotation 与该计算替换交换。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace GodelQuotation
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
universe u v w
attribute [local simp] finite_numeral_term_freeSupport
/-! ## 标准自然数符号串上的可计算替换 -/
/-- 一个源标签对应的替换分片。 -/
def substitution_piece_tokens (boundToken : Nat) (replacement : List Nat) (token : Nat) :
    List Nat :=
  if token = boundToken then replacement else [token]
/-- 源串逐位置产生的分片族；其长度与源串完全相同。 -/
def substitution_pieces_tokens (source : List Nat) (boundToken : Nat) (replacement : List Nat) :
    List (List Nat) :=
  source.map (substitution_piece_tokens boundToken replacement)
/-- 标准符号串替换：逐位置产生分片，再按原顺序折叠。 -/
def substitute_tokens (source : List Nat) (boundToken : Nat) (replacement : List Nat) :
    List Nat := (substitution_pieces_tokens source boundToken replacement).flatten
@[simp]
theorem substitution_piece_tokens_eq (boundToken : Nat) (replacement : List Nat) :
    substitution_piece_tokens boundToken replacement boundToken =
      replacement := by
  simp [substitution_piece_tokens]
@[simp]
theorem substitution_piece_tokens_ne
    {token boundToken : Nat} (replacement : List Nat) (hToken : token ≠ boundToken) :
    substitution_piece_tokens boundToken replacement token = [token] := by
  simp [substitution_piece_tokens, hToken]
/-- 分片族在每个标准指标上的值就是该源标签对应的替换分片。 -/
theorem substitution_pieces_tokens_getElem? (source : List Nat) (boundToken : Nat) (replacement : List Nat) (index : Nat) :
    (substitution_pieces_tokens source boundToken replacement)[index]? = (source[index]?).map (substitution_piece_tokens boundToken replacement) := by
  simp [substitution_pieces_tokens]
@[simp]
theorem substitute_tokens_nil (boundToken : Nat) (replacement : List Nat) :
    substitute_tokens [] boundToken replacement = [] := by
  simp [substitute_tokens, substitution_pieces_tokens]
@[simp]
theorem substitute_tokens_cons (token : Nat) (source replacement : List Nat) (boundToken : Nat) :
    substitute_tokens (token :: source) boundToken replacement =
      substitution_piece_tokens boundToken replacement token ++
        substitute_tokens source boundToken replacement := by
  simp [substitute_tokens, substitution_pieces_tokens]
/-- 替换与源串拼接交换；公式构造 quotation 可据此逐层归纳。 -/
theorem substitute_tokens_append (left right replacement : List Nat) (boundToken : Nat) :
    substitute_tokens (left ++ right) boundToken replacement =
      substitute_tokens left boundToken replacement ++
        substitute_tokens right boundToken replacement := by
  simp [substitute_tokens, substitution_pieces_tokens,
    List.map_append, List.flatten_append]

/--
替换串不含目标 token 时，完整替换结果也不含该 token。

命中位置被整个替换串覆盖，未命中位置只保留一个与目标不同的原 token。
-/
theorem substitute_tokens_not_mem
    (source replacement : List Nat) (boundToken : Nat)
    (hReplacement : boundToken ∉ replacement) :
    boundToken ∉
      substitute_tokens source boundToken replacement := by
  induction source with
  | nil =>
      simp
  | cons token source ih =>
      by_cases hToken : token = boundToken
      · subst token
        simp [substitute_tokens_cons,
          hReplacement, ih]
      · have hBound : boundToken ≠ token :=
          Ne.symm hToken
        simp [substitute_tokens_cons,
          substitution_piece_tokens, hToken,
          hBound, ih]

@[simp]
theorem substitute_tokens_singleton_ne
    {token boundToken : Nat} (replacement : List Nat) (hToken : token ≠ boundToken) :
    substitute_tokens [token] boundToken replacement = [token] := by
  simp [hToken]
/-! ## 标签互异与公式构造的替换同态 -/
/-- 变量标签 `3^(name+1)` 对名字单射。 -/
theorem variable_token_injective : Function.Injective variable_token := by
  intro left right hEqual
  have hLeftLe : left + 1 ≤ right + 1 := (Nat.pow_le_pow_iff_right (a := 3) (by omega)).mp (Nat.le_of_eq hEqual)
  have hRightLe : right + 1 ≤ left + 1 := (Nat.pow_le_pow_iff_right (a := 3) (by omega)).mp (Nat.le_of_eq hEqual.symm)
  omega
/-- 偶数的逻辑标签不可能等于奇数的变量标签。 -/
theorem logical_token_ne_variable_token (symbol : LogicalSymbolKind) (name : Nat) :
    logical_token symbol ≠ variable_token name := by
  intro hEqual
  have hParity := congrArg (fun token => token % 2) hEqual
  cases symbol <;>
    simp [Numbered.logical_token, logical_symbol_exponent,
      Numbered.variable_token, Nat.pow_mod] at hParity
/-- 隶属标签 `2^7` 与任何变量标签互异。 -/
theorem membership_token_ne_variable_token (name : Nat) :
    membership_token ≠ variable_token name := by
  intro hEqual
  have hParity := congrArg (fun token => token % 2) hEqual
  simp [Numbered.membership_token, Numbered.variable_token,
    Nat.pow_mod] at hParity
/-- 常元标签的 `5`-幂部分保证它不可能是变量标签。 -/
theorem constant_token_ne_variable_token (index name : Nat) :
    Numbered.constant_token index ≠ variable_token name := by
  intro hEqual
  have hCoprime :
      Nat.Coprime (5 ^ (index + 1)) (3 ^ (name + 1)) :=
    Nat.Coprime.pow (index + 1) (name + 1) (by decide)
  have hDiv : 5 ^ (index + 1) ∣ 3 ^ (name + 1) := by
    exact ⟨1, by simpa [Numbered.constant_token,
      Numbered.variable_token] using hEqual.symm⟩
  have hOne := hCoprime.eq_one_of_dvd hDiv
  simp at hOne
/-- 正元数函数标签的 `5`-幂因子保证它不可能是变量标签。 -/
theorem function_token_ne_variable_token (arityPredecessor index name : Nat) :
    Numbered.function_token arityPredecessor index ≠ variable_token name := by
  intro hEqual
  have hCoprime :
      Nat.Coprime (5 ^ (index + 1)) (3 ^ (name + 1)) :=
    Nat.Coprime.pow (index + 1) (name + 1) (by decide)
  have hDiv : 5 ^ (index + 1) ∣ 3 ^ (name + 1) := by
    refine ⟨3 ^ (arityPredecessor + 1), ?_⟩
    simpa [Numbered.function_token, Numbered.variable_token,
      Nat.mul_comm] using hEqual.symm
  have hOne := hCoprime.eq_one_of_dvd hDiv
  simp at hOne
/-- 正元数谓词标签的 `7`-幂因子保证它不可能是变量标签。 -/
theorem predicate_token_ne_variable_token (arityPredecessor index name : Nat) :
    Numbered.predicate_token arityPredecessor index ≠ variable_token name := by
  intro hEqual
  have hCoprime :
      Nat.Coprime (7 ^ (index + 1)) (3 ^ (name + 1)) :=
    Nat.Coprime.pow (index + 1) (name + 1) (by decide)
  have hDiv : 7 ^ (index + 1) ∣ 3 ^ (name + 1) := by
    refine ⟨3 ^ (arityPredecessor + 1), ?_⟩
    simpa [Numbered.predicate_token, Numbered.variable_token,
      Nat.mul_comm] using hEqual.symm
  have hOne := hCoprime.eq_one_of_dvd hDiv
  simp at hOne
/-- 不同名字产生不同变量标签。 -/
theorem variable_token_ne_variable_token
    {left right : Nat} (hNames : left ≠ right) :
    variable_token left ≠ variable_token right :=
  fun hTokens => hNames (variable_token_injective hTokens)
/-- 逐位置替换与有限符号串族的折叠交换。 -/
theorem substitute_tokens_flatten (pieces : List (List Nat)) (boundToken : Nat) (replacement : List Nat) :
    substitute_tokens pieces.flatten boundToken replacement = (pieces.map (fun piece => substitute_tokens piece boundToken replacement)).flatten := by
  induction pieces with
  | nil =>
      simp
  | cons head tail ih =>
      simp [substitute_tokens_append, ih]
/-- 正元数函数应用符号串构造与标准替换交换。 -/
theorem substitute_tokens_function_application_tokens (arityPredecessor index name : Nat) (arguments : List (List Nat)) (replacement : List Nat) :
    substitute_tokens (Numbered.function_application_tokens
          arityPredecessor index arguments) (variable_token name) replacement =
      Numbered.function_application_tokens arityPredecessor index (arguments.map (fun argument =>
          substitute_tokens argument (variable_token name) replacement)) := by
  simp [Numbered.function_application_tokens, substitute_tokens_append,
    substitute_tokens_flatten, logical_token_ne_variable_token,
    function_token_ne_variable_token]
/-- 正元数谓词应用符号串构造与标准替换交换。 -/
theorem substitute_tokens_predicate_application_tokens (arityPredecessor index name : Nat) (arguments : List (List Nat)) (replacement : List Nat) :
    substitute_tokens (Numbered.predicate_application_tokens
          arityPredecessor index arguments) (variable_token name) replacement =
      Numbered.predicate_application_tokens arityPredecessor index (arguments.map (fun argument =>
          substitute_tokens argument (variable_token name) replacement)) := by
  simp [Numbered.predicate_application_tokens, substitute_tokens_append,
    substitute_tokens_flatten, logical_token_ne_variable_token,
    predicate_token_ne_variable_token]
/-- 等式符号串构造与标准替换交换。 -/
theorem substitute_tokens_equality_tokens (left right replacement : List Nat) (name : Nat) :
    substitute_tokens (equality_tokens left right) (variable_token name) replacement =
      equality_tokens (substitute_tokens left (variable_token name) replacement) (substitute_tokens right (variable_token name) replacement) := by
  simp [Numbered.equality_tokens, substitute_tokens_append,
    logical_token_ne_variable_token]
/-- 隶属原子符号串构造与标准替换交换。 -/
theorem substitute_tokens_membership_tokens (left right replacement : List Nat) (name : Nat) :
    substitute_tokens (membership_tokens left right) (variable_token name) replacement =
      membership_tokens (substitute_tokens left (variable_token name) replacement) (substitute_tokens right (variable_token name) replacement) := by
  simp [Numbered.membership_tokens, substitute_tokens_append,
    logical_token_ne_variable_token,
    membership_token_ne_variable_token]
/-- 否定符号串构造与标准替换交换。 -/
theorem substitute_tokens_negation_tokens (body replacement : List Nat) (name : Nat) :
    substitute_tokens (negation_tokens body) (variable_token name) replacement =
      negation_tokens (substitute_tokens body (variable_token name) replacement) := by
  simp [Numbered.negation_tokens, substitute_tokens_append,
    logical_token_ne_variable_token]
/-- 蕴含符号串构造与标准替换交换。 -/
theorem substitute_tokens_implication_tokens (left right replacement : List Nat) (name : Nat) :
    substitute_tokens (implication_tokens left right) (variable_token name) replacement =
      implication_tokens (substitute_tokens left (variable_token name) replacement) (substitute_tokens right (variable_token name) replacement) := by
  simp [Numbered.implication_tokens, substitute_tokens_append,
    logical_token_ne_variable_token]
/-- 新量词名字与被替换名字不同时，全称符号串构造与标准替换交换。 -/
theorem substitute_tokens_universal_tokens (binderName targetName : Nat) (body replacement : List Nat) (hNames : binderName ≠ targetName) :
    substitute_tokens (universal_tokens binderName body) (variable_token targetName) replacement =
      universal_tokens binderName (substitute_tokens body (variable_token targetName) replacement) := by
  simp [Numbered.universal_tokens, substitute_tokens_append,
    logical_token_ne_variable_token,
    variable_token_ne_variable_token hNames]
/-! ## 项 quotation 与替换 -/
/-- bound-closed 项的符号串 quotation 不依赖当前 binder 名称栈。 -/
theorem quote_term_tokens_with?_eq_of_boundClosed
    {σ : Signature.{u, v, w}}
    [QuotationNumbering σ] [DecidableEq σ.SortSymbol] (freeNaming : FreeVarId → Nat) (leftNames rightNames : List Nat)
    (term : Term σ) (hClosed : Term.BoundClosed term) :
    Numbered.quote_term_tokens_with? freeNaming leftNames term =
      Numbered.quote_term_tokens_with? freeNaming rightNames term := by
  refine Term.rec (motive_1 := fun term =>
      Term.BoundClosed term →
        Numbered.quote_term_tokens_with? freeNaming leftNames term =
          Numbered.quote_term_tokens_with? freeNaming rightNames term) (motive_2 := fun terms =>
      (∀ candidate, candidate ∈ terms → Term.BoundClosed candidate) →
        terms.mapM (Numbered.quote_term_tokens_with? freeNaming leftNames) =
          terms.mapM (Numbered.quote_term_tokens_with? freeNaming rightNames))
    ?_ ?_ ?_ ?_ term hClosed
  · intro sourceVar hSourceClosed
    cases sourceVar with
    | bvar sort index =>
        cases hSourceClosed with
        | bvar hIndex =>
            simp [Scope.empty] at hIndex
    | fvar sort id =>
        simp [Numbered.quote_term_tokens_with?]
  · intro function arguments ih hAppClosed
    cases hAppClosed with
    | app _ _ hArgumentsClosed =>
        simp [Numbered.quote_term_tokens_with?,
          ih hArgumentsClosed]
  · intro hClosed
    rfl
  · intro head tail ihHead ihTail hClosed
    have hHead : Term.BoundClosed head :=
      hClosed head (by simp)
    have hTail : ∀ candidate, candidate ∈ tail →
        Term.BoundClosed candidate := by
      intro candidate hCandidate
      exact hClosed candidate (by simp [hCandidate])
    simp [ihHead hHead, ihTail hTail]
/--
任意可编号单排序签名上的项 quotation 都把自由变量替换精确翻译为标签串替换。
显式的 replacement quotation 等式既记录计算结果，也使本定理可用于任意合法的
binder 环境；`hTargetFresh` 排除自由变量标签与现有 bound 名称碰撞。
-/
theorem quote_term_tokens_with?_substituteFree
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ] [DecidableEq σ.SortSymbol] (freeNaming : FreeVarId → Nat) (hFreeNaming : Function.Injective freeNaming)
    (boundNames : List Nat) (id : FreeVarId) (hTargetFresh : freeNaming id ∉ boundNames) (replacement term : Term σ) (replacementTokens : List Nat)
    (hReplacement :
      Numbered.quote_term_tokens_with? freeNaming boundNames replacement =
        some replacementTokens) :
    Numbered.quote_term_tokens_with? freeNaming boundNames (Term.substituteFree numbering.objectSort id replacement term) =
      (Numbered.quote_term_tokens_with? freeNaming boundNames term).map (fun sourceTokens =>
          substitute_tokens sourceTokens (variable_token (freeNaming id)) replacementTokens) := by
  refine Term.rec (motive_1 := fun term =>
      Numbered.quote_term_tokens_with? freeNaming boundNames (Term.substituteFree numbering.objectSort id replacement term) =
        (Numbered.quote_term_tokens_with? freeNaming boundNames term).map (fun sourceTokens =>
            substitute_tokens sourceTokens (variable_token (freeNaming id)) replacementTokens)) (motive_2 := fun terms =>
      (terms.map (Term.substituteFree numbering.objectSort id replacement)).mapM (Numbered.quote_term_tokens_with? freeNaming boundNames) = (terms.mapM
          (Numbered.quote_term_tokens_with? freeNaming boundNames)).map (fun sourceCodes => sourceCodes.map (fun sourceTokens =>
            substitute_tokens sourceTokens (variable_token (freeNaming id)) replacementTokens)))
    ?_ ?_ ?_ ?_ term
  · intro sourceVar
    cases sourceVar with
    | bvar sort index =>
        cases hName : boundNames[index]? with
        | none =>
            simp [Term.substituteFree,
              Numbered.quote_term_tokens_with?, hName]
        | some name =>
            have hNames : name ≠ freeNaming id := by
              intro hEqual
              apply hTargetFresh
              rw [← hEqual]
              exact List.mem_of_getElem? hName
            simp [Term.substituteFree,
              Numbered.quote_term_tokens_with?, hName,
              variable_token_ne_variable_token hNames]
    | fvar sort freeId =>
        have hSort : sort = numbering.objectSort :=
          numbering.sort_eq_object sort
        subst sort
        by_cases hId : freeId = id
        · subst freeId
          simpa [Term.substituteFree,
            Numbered.quote_term_tokens_with?,
            substitute_tokens, substitution_pieces_tokens,
            substitution_piece_tokens] using hReplacement
        · have hNames : freeNaming freeId ≠ freeNaming id :=
            fun hEqual => hId (hFreeNaming hEqual)
          simp [Term.substituteFree,
            Numbered.quote_term_tokens_with?, hId,
            variable_token_ne_variable_token hNames]
  · intro function arguments ih
    simp only [Term.substituteFree,
      Numbered.quote_term_tokens_with?]
    rw [ih]
    cases hCodes : arguments.mapM (Numbered.quote_term_tokens_with? freeNaming boundNames) with
    | none =>
        simp
    | some codes =>
        cases codes with
        | nil =>
            simp [constant_token_ne_variable_token]
        | cons head tail =>
            simp [substitute_tokens_function_application_tokens]
  · rfl
  · intro head tail ihHead ihTail
    cases hHead : Numbered.quote_term_tokens_with?
        freeNaming boundNames head <;>
      cases hTail : tail.mapM (Numbered.quote_term_tokens_with? freeNaming boundNames) <;>
      simp_all
/-- 项列表 quotation 逐项把自由替换翻译为 token 替换。 -/
theorem quote_terms_tokens_with?_substituteFree
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ] [DecidableEq σ.SortSymbol] (freeNaming : FreeVarId → Nat) (hFreeNaming : Function.Injective freeNaming)
    (boundNames : List Nat) (id : FreeVarId) (hTargetFresh : freeNaming id ∉ boundNames) (replacement : Term σ) (replacementTokens : List Nat) (hReplacement :
      Numbered.quote_term_tokens_with? freeNaming boundNames replacement =
        some replacementTokens) (terms : List (Term σ)) : (terms.map (Term.substituteFree numbering.objectSort id replacement)).mapM
        (Numbered.quote_term_tokens_with? freeNaming boundNames) = (terms.mapM (Numbered.quote_term_tokens_with? freeNaming boundNames)).map
        (fun sourceCodes => sourceCodes.map (fun sourceTokens =>
          substitute_tokens sourceTokens (variable_token (freeNaming id)) replacementTokens)) := by
  induction terms with
  | nil =>
      rfl
  | cons head tail ih =>
      have hHead := quote_term_tokens_with?_substituteFree
        freeNaming hFreeNaming boundNames id hTargetFresh
        replacement head replacementTokens hReplacement
      cases hHeadCode : Numbered.quote_term_tokens_with?
          freeNaming boundNames head <;>
        cases hTailCodes : tail.mapM (Numbered.quote_term_tokens_with? freeNaming boundNames) <;>
        simp_all
/-! ## Hilbert quotation 与替换 -/
/--
显式具名 Hilbert quotation 把语法自由变量替换翻译为标准符号串替换。
`hBinderFresh` 是量词递归所需的唯一 α-条件：后续选择的每个 binder 名都不同于
目标自由变量名。规范偶/奇命名将在公共接口中自动满足它。
-/
theorem quote_hilbert_tokens_with?_substituteFree
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ] [DecidableEq σ.SortSymbol] (freeNaming binderNaming : Nat → Nat) (hFreeNaming : Function.Injective freeNaming)
    (boundNames : List Nat) (depth : Nat) (id : FreeVarId) (hTargetFresh : freeNaming id ∉ boundNames) (hBinderFresh : ∀ binderDepth,
      binderNaming binderDepth ≠ freeNaming id) (replacement : Term σ) (hReplacementClosed : Term.BoundClosed replacement) (replacementTokens : List Nat)
    (hReplacement :
      Numbered.quote_term_tokens_with? freeNaming boundNames replacement =
        some replacementTokens) (formula : Formula σ) :
    Numbered.quote_hilbert_tokens_with? freeNaming binderNaming
        boundNames depth (Formula.substituteFree numbering.objectSort id replacement formula) = (Numbered.quote_hilbert_tokens_with? freeNaming binderNaming
        boundNames depth formula).map (fun sourceTokens =>
          substitute_tokens sourceTokens (variable_token (freeNaming id)) replacementTokens) := by
  induction formula generalizing boundNames depth with
  | falsum =>
      rfl
  | truth =>
      rfl
  | rel relation arguments =>
      cases hKind : numbering.relation_kind relation with
      | membership =>
          cases arguments with
          | nil =>
              simp [Formula.substituteFree,
                Numbered.quote_hilbert_tokens_with?,
                Numbered.quote_relation_tokens_with?, hKind]
          | cons left rest =>
              cases rest with
              | nil =>
                  simp [Formula.substituteFree,
                    Numbered.quote_hilbert_tokens_with?,
                    Numbered.quote_relation_tokens_with?, hKind]
              | cons right tail =>
                  cases tail with
                  | cons extra tail =>
                      simp [Formula.substituteFree,
                        Numbered.quote_hilbert_tokens_with?,
                        Numbered.quote_relation_tokens_with?, hKind]
                  | nil =>
                      have hLeft :=
                        quote_term_tokens_with?_substituteFree
                          freeNaming hFreeNaming boundNames id
                          hTargetFresh replacement left
                          replacementTokens hReplacement
                      have hRight :=
                        quote_term_tokens_with?_substituteFree
                          freeNaming hFreeNaming boundNames id
                          hTargetFresh replacement right
                          replacementTokens hReplacement
                      simp only [Formula.substituteFree, List.map_cons,
                        List.map_nil,
                        Numbered.quote_hilbert_tokens_with?,
                        Numbered.quote_relation_tokens_with?, hKind]
                      rw [hLeft, hRight]
                      cases Numbered.quote_term_tokens_with?
                          freeNaming boundNames left <;>
                        cases Numbered.quote_term_tokens_with?
                            freeNaming boundNames right <;>
                          simp [substitute_tokens_membership_tokens]
      | predicate =>
          cases arguments with
          | nil =>
              simp [Formula.substituteFree,
                Numbered.quote_hilbert_tokens_with?,
                Numbered.quote_relation_tokens_with?, hKind]
          | cons head tail =>
              have hArguments :=
                quote_terms_tokens_with?_substituteFree
                  freeNaming hFreeNaming boundNames id hTargetFresh
                  replacement replacementTokens hReplacement (head :: tail)
              have hArguments' : (Term.substituteFree numbering.objectSort id replacement head ::
                      tail.map (Term.substituteFree
                        numbering.objectSort id replacement)).mapM (Numbered.quote_term_tokens_with?
                        freeNaming boundNames) = ((head :: tail).mapM (Numbered.quote_term_tokens_with?
                        freeNaming boundNames)).map (fun sourceCodes => sourceCodes.map (fun sourceTokens =>
                          substitute_tokens sourceTokens (variable_token (freeNaming id))
                            replacementTokens)) := by
                simpa only [List.map_cons] using hArguments
              simp only [Formula.substituteFree, List.map_cons,
                Numbered.quote_hilbert_tokens_with?,
                Numbered.quote_relation_tokens_with?, hKind]
              rw [hArguments']
              cases hCodes : (head :: tail).mapM (Numbered.quote_term_tokens_with?
                    freeNaming boundNames) with
              | none =>
                  simp
              | some codes =>
                  simp [substitute_tokens_predicate_application_tokens]
  | equal left right =>
      have hLeft := quote_term_tokens_with?_substituteFree
        freeNaming hFreeNaming boundNames id hTargetFresh
        replacement left replacementTokens hReplacement
      have hRight := quote_term_tokens_with?_substituteFree
        freeNaming hFreeNaming boundNames id hTargetFresh
        replacement right replacementTokens hReplacement
      simp only [Formula.substituteFree,
        Numbered.quote_hilbert_tokens_with?]
      rw [hLeft, hRight]
      cases Numbered.quote_term_tokens_with?
          freeNaming boundNames left <;>
        cases Numbered.quote_term_tokens_with?
            freeNaming boundNames right <;>
          simp [substitute_tokens_equality_tokens]
  | neg body ih =>
      simp only [Formula.substituteFree,
        Numbered.quote_hilbert_tokens_with?]
      rw [ih boundNames depth hTargetFresh hReplacement]
      cases Numbered.quote_hilbert_tokens_with? freeNaming binderNaming
          boundNames depth body <;>
        simp [substitute_tokens_negation_tokens]
  | conj left right =>
      rfl
  | disj left right =>
      rfl
  | imp left right ihLeft ihRight =>
      simp only [Formula.substituteFree,
        Numbered.quote_hilbert_tokens_with?]
      rw [ihLeft boundNames depth hTargetFresh hReplacement,
        ihRight boundNames depth hTargetFresh hReplacement]
      cases Numbered.quote_hilbert_tokens_with? freeNaming binderNaming
          boundNames depth left <;>
        cases Numbered.quote_hilbert_tokens_with? freeNaming binderNaming
            boundNames depth right <;>
          simp [substitute_tokens_implication_tokens]
  | iff left right =>
      rfl
  | forallE sort body ih =>
      let binderName := binderNaming depth
      have hTargetFresh' :
          freeNaming id ∉ binderName :: boundNames := by
        simp only [List.mem_cons, not_or]
        exact ⟨(hBinderFresh depth).symm, hTargetFresh⟩
      have hReplacement' :
          Numbered.quote_term_tokens_with? freeNaming (binderName :: boundNames) replacement =
            some replacementTokens := by
        rw [quote_term_tokens_with?_eq_of_boundClosed
          freeNaming (binderName :: boundNames) boundNames
          replacement hReplacementClosed]
        exact hReplacement
      simp only [Formula.substituteFree,
        Numbered.quote_hilbert_tokens_with?]
      rw [ih (binderName :: boundNames) (depth + 1)
        hTargetFresh' hReplacement']
      cases Numbered.quote_hilbert_tokens_with? freeNaming binderNaming (binderName :: boundNames) (depth + 1) body <;>
        simp [substitute_tokens_universal_tokens,
          hBinderFresh depth]
  | existsE sort body =>
      rfl
/-! ## `closeFreeAt` 与具名环境插入的通用交换律 -/
/--
对任意可编号单排序签名，项的 token quotation 把 `closeFreeAt` 精确解释为在
bound 名称表相应位置插入目标自由变量名。
-/
theorem quote_term_tokens_with?_closeFreeAt_insert
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ]
    [DecidableEq σ.SortSymbol] (freeNaming : FreeVarId → Nat) (boundNames : List Nat) (id depth : Nat) (term : Term σ) (hDepth : depth ≤ boundNames.length) :
    Numbered.quote_term_tokens_with? freeNaming (boundNames.insertIdx depth (freeNaming id)) (Term.closeFreeAt numbering.objectSort id depth term) =
      Numbered.quote_term_tokens_with? freeNaming boundNames term := by
  refine Term.rec (motive_1 := fun term =>
      ∀ depth, depth ≤ boundNames.length →
        Numbered.quote_term_tokens_with? freeNaming (boundNames.insertIdx depth (freeNaming id)) (Term.closeFreeAt
              numbering.objectSort id depth term) =
          Numbered.quote_term_tokens_with?
            freeNaming boundNames term) (motive_2 := fun terms =>
      ∀ depth, depth ≤ boundNames.length → (terms.map (Term.closeFreeAt
              numbering.objectSort id depth)).mapM (Numbered.quote_term_tokens_with? freeNaming (boundNames.insertIdx depth (freeNaming id))) =
          terms.mapM (Numbered.quote_term_tokens_with?
              freeNaming boundNames))
    ?_ ?_ ?_ ?_ term depth hDepth
  · intro sourceVar depth hDepth
    cases sourceVar with
    | bvar sort index =>
        have hSort : sort = numbering.objectSort :=
          numbering.sort_eq_object sort
        subst sort
        by_cases hIndex : depth ≤ index
        · have hStrict : depth < index + 1 := by omega
          simp [Term.closeFreeAt,
            Numbered.quote_term_tokens_with?, hIndex,
            List.getElem?_insertIdx_of_gt hStrict]
        · have hStrict : index < depth := by omega
          simp [Term.closeFreeAt,
            Numbered.quote_term_tokens_with?, hIndex,
            List.getElem?_insertIdx_of_lt hStrict]
    | fvar sort freeId =>
        have hSort : sort = numbering.objectSort :=
          numbering.sort_eq_object sort
        subst sort
        by_cases hId : freeId = id
        · subst freeId
          simp [Term.closeFreeAt,
            Numbered.quote_term_tokens_with?, hDepth,
            List.getElem?_insertIdx_self]
        · simp [Term.closeFreeAt,
            Numbered.quote_term_tokens_with?, hId]
  · intro function arguments ih depth hDepth
    simp only [Term.closeFreeAt,
      Numbered.quote_term_tokens_with?]
    rw [ih depth hDepth]
    simp
  · intro depth hDepth
    rfl
  · intro head tail ihHead ihTail depth hDepth
    simp only [List.map_cons, List.mapM_cons]
    rw [ihHead depth hDepth, ihTail depth hDepth]
/-- 项列表版本，供普通谓词和函数参数统一复用。 -/
theorem quote_terms_tokens_with?_closeFreeAt_insert
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ]
    [DecidableEq σ.SortSymbol] (freeNaming : FreeVarId → Nat) (boundNames : List Nat) (id depth : Nat) (terms : List (Term σ))
    (hDepth : depth ≤ boundNames.length) : (terms.map (Term.closeFreeAt
          numbering.objectSort id depth)).mapM (Numbered.quote_term_tokens_with? freeNaming (boundNames.insertIdx depth (freeNaming id))) =
      terms.mapM (Numbered.quote_term_tokens_with?
          freeNaming boundNames) := by
  induction terms with
  | nil =>
      rfl
  | cons head tail ih =>
      simp only [List.map_cons, List.mapM_cons]
      rw [quote_term_tokens_with?_closeFreeAt_insert
          freeNaming boundNames id depth head hDepth,
        ih]
/--
Hilbert 核 token quotation 与 `closeFreeAt` 的通用交换律。
该等式只改变具名环境，不要求公式良构或 admissible；因此也适用于逻辑公理模式中
仅由一次成功 quotation 保证可编码性的子公式。
-/
theorem quote_hilbert_tokens_with?_closeFreeAt_insert
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ]
    [DecidableEq σ.SortSymbol] (freeNaming binderNaming : Nat → Nat) (boundNames : List Nat) (quoteDepth id closeDepth : Nat) (formula : Formula σ)
    (hDepth : closeDepth ≤ boundNames.length) :
    Numbered.quote_hilbert_tokens_with?
        freeNaming binderNaming (boundNames.insertIdx closeDepth (freeNaming id))
        quoteDepth (Formula.closeFreeAt
          numbering.objectSort id closeDepth formula) =
      Numbered.quote_hilbert_tokens_with?
        freeNaming binderNaming boundNames quoteDepth formula := by
  induction formula generalizing
      boundNames quoteDepth closeDepth with
  | falsum =>
      rfl
  | truth =>
      rfl
  | rel relation arguments =>
      cases hKind : numbering.relation_kind relation with
      | membership =>
          cases arguments with
          | nil =>
              simp [Formula.closeFreeAt,
                Numbered.quote_hilbert_tokens_with?,
                Numbered.quote_relation_tokens_with?, hKind]
          | cons left rest =>
              cases rest with
              | nil =>
                  simp [Formula.closeFreeAt,
                    Numbered.quote_hilbert_tokens_with?,
                    Numbered.quote_relation_tokens_with?, hKind]
              | cons right tail =>
                  cases tail with
                  | cons extra tail =>
                      simp [Formula.closeFreeAt,
                        Numbered.quote_hilbert_tokens_with?,
                        Numbered.quote_relation_tokens_with?, hKind]
                  | nil =>
                      simp [Formula.closeFreeAt,
                        Numbered.quote_hilbert_tokens_with?,
                        Numbered.quote_relation_tokens_with?, hKind,
                        quote_term_tokens_with?_closeFreeAt_insert
                          freeNaming boundNames id closeDepth left hDepth,
                        quote_term_tokens_with?_closeFreeAt_insert
                          freeNaming boundNames id closeDepth right hDepth]
      | predicate =>
          cases arguments with
          | nil =>
              simp [Formula.closeFreeAt,
                Numbered.quote_hilbert_tokens_with?,
                Numbered.quote_relation_tokens_with?, hKind]
          | cons head tail =>
              have hArguments :=
                quote_terms_tokens_with?_closeFreeAt_insert
                  freeNaming boundNames id closeDepth (head :: tail) hDepth
              exact (by
                  simpa [Formula.closeFreeAt,
                    Numbered.quote_hilbert_tokens_with?,
                    Numbered.quote_relation_tokens_with?, hKind] using
                    congrArg (fun result =>
                        result.bind (fun codes =>
                          some (Numbered.predicate_application_tokens ((head :: tail).length - 1) (numbering.relation_number relation)
                              codes)))
                      hArguments)
  | equal left right =>
      simp [Formula.closeFreeAt,
        Numbered.quote_hilbert_tokens_with?,
        quote_term_tokens_with?_closeFreeAt_insert
          freeNaming boundNames id closeDepth left hDepth,
        quote_term_tokens_with?_closeFreeAt_insert
          freeNaming boundNames id closeDepth right hDepth]
  | neg body ih =>
      have hBody := ih boundNames quoteDepth closeDepth hDepth
      simpa [Formula.closeFreeAt,
        Numbered.quote_hilbert_tokens_with?] using
        congrArg (fun result =>
            result.bind (fun bodyTokens =>
              some (Numbered.negation_tokens bodyTokens)))
          hBody
  | conj left right =>
      rfl
  | disj left right =>
      rfl
  | imp left right ihLeft ihRight =>
      have hLeft :=
        ihLeft boundNames quoteDepth closeDepth hDepth
      have hRight :=
        ihRight boundNames quoteDepth closeDepth hDepth
      simp only [Formula.closeFreeAt,
        Numbered.quote_hilbert_tokens_with?]
      rw [hLeft, hRight]
  | iff left right =>
      rfl
  | forallE sort body ih =>
      have hSort : sort = numbering.objectSort :=
        numbering.sort_eq_object sort
      subst sort
      let name := binderNaming quoteDepth
      have hDepth' :
          closeDepth + 1 ≤ (name :: boundNames).length := by
        simp
        omega
      have hBody :=
        ih (name :: boundNames) (quoteDepth + 1) (closeDepth + 1) hDepth'
      simp only [List.insertIdx_succ_cons] at hBody
      simpa [Formula.closeFreeAt, Formula.next_depth,
        Numbered.quote_hilbert_tokens_with?, name] using
        congrArg (fun result =>
            result.bind (fun bodyTokens =>
              some (Numbered.universal_tokens name bodyTokens)))
          hBody
  | existsE sort body =>
      rfl
/--
对象项 quotation 上，`closeFreeAt` 同样由 bound 名称表插入精确实现。
-/
theorem quote_term_with?_closeFreeAt_insert
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ]
    [DecidableEq σ.SortSymbol] (freeNaming : FreeVarId → Nat) (boundNames : List Nat) (id depth : Nat) (term : Term σ) (hDepth : depth ≤ boundNames.length) :
    Numbered.quote_term_with? freeNaming (boundNames.insertIdx depth (freeNaming id)) (Term.closeFreeAt numbering.objectSort id depth term) =
      Numbered.quote_term_with? freeNaming boundNames term := by
  refine Term.rec (motive_1 := fun term =>
      ∀ depth, depth ≤ boundNames.length →
        Numbered.quote_term_with? freeNaming (boundNames.insertIdx depth (freeNaming id)) (Term.closeFreeAt
              numbering.objectSort id depth term) =
          Numbered.quote_term_with?
            freeNaming boundNames term) (motive_2 := fun terms =>
      ∀ depth, depth ≤ boundNames.length → (terms.map (Term.closeFreeAt
              numbering.objectSort id depth)).mapM (Numbered.quote_term_with? freeNaming (boundNames.insertIdx depth (freeNaming id))) =
          terms.mapM (Numbered.quote_term_with?
              freeNaming boundNames))
    ?_ ?_ ?_ ?_ term depth hDepth
  · intro sourceVar depth hDepth
    cases sourceVar with
    | bvar sort index =>
        have hSort : sort = numbering.objectSort :=
          numbering.sort_eq_object sort
        subst sort
        by_cases hIndex : depth ≤ index
        · have hStrict : depth < index + 1 := by omega
          simp [Term.closeFreeAt,
            Numbered.quote_term_with?, hIndex,
            List.getElem?_insertIdx_of_gt hStrict]
        · have hStrict : index < depth := by omega
          simp [Term.closeFreeAt,
            Numbered.quote_term_with?, hIndex,
            List.getElem?_insertIdx_of_lt hStrict]
    | fvar sort freeId =>
        have hSort : sort = numbering.objectSort :=
          numbering.sort_eq_object sort
        subst sort
        by_cases hId : freeId = id
        · subst freeId
          simp [Term.closeFreeAt,
            Numbered.quote_term_with?, hDepth,
            List.getElem?_insertIdx_self]
        · simp [Term.closeFreeAt,
            Numbered.quote_term_with?, hId]
  · intro function arguments ih depth hDepth
    simp only [Term.closeFreeAt,
      Numbered.quote_term_with?]
    rw [ih depth hDepth]
    simp
  · intro depth hDepth
    rfl
  · intro head tail ihHead ihTail depth hDepth
    simp only [List.map_cons, List.mapM_cons]
    rw [ihHead depth hDepth, ihTail depth hDepth]
/-- 对象项 quotation 的项列表版本。 -/
theorem quote_terms_with?_closeFreeAt_insert
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ]
    [DecidableEq σ.SortSymbol] (freeNaming : FreeVarId → Nat) (boundNames : List Nat) (id depth : Nat) (terms : List (Term σ))
    (hDepth : depth ≤ boundNames.length) : (terms.map (Term.closeFreeAt
          numbering.objectSort id depth)).mapM (Numbered.quote_term_with? freeNaming (boundNames.insertIdx depth (freeNaming id))) =
      terms.mapM (Numbered.quote_term_with?
          freeNaming boundNames) := by
  induction terms with
  | nil =>
      rfl
  | cons head tail ih =>
      simp only [List.map_cons, List.mapM_cons]
      rw [quote_term_with?_closeFreeAt_insert
          freeNaming boundNames id depth head hDepth,
        ih]
/-- Hilbert 核对象项 quotation 与 `closeFreeAt` 的通用交换律。 -/
theorem quote_hilbert_with?_closeFreeAt_insert
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ]
    [DecidableEq σ.SortSymbol] (freeNaming binderNaming : Nat → Nat) (boundNames : List Nat) (quoteDepth id closeDepth : Nat) (formula : Formula σ)
    (hDepth : closeDepth ≤ boundNames.length) :
    Numbered.quote_hilbert_with?
        freeNaming binderNaming (boundNames.insertIdx closeDepth (freeNaming id))
        quoteDepth (Formula.closeFreeAt
          numbering.objectSort id closeDepth formula) =
      Numbered.quote_hilbert_with?
        freeNaming binderNaming boundNames quoteDepth formula := by
  induction formula generalizing
      boundNames quoteDepth closeDepth with
  | falsum =>
      rfl
  | truth =>
      rfl
  | rel relation arguments =>
      cases hKind : numbering.relation_kind relation with
      | membership =>
          cases arguments with
          | nil =>
              simp [Formula.closeFreeAt,
                Numbered.quote_hilbert_with?,
                Numbered.quote_relation_with?, hKind]
          | cons left rest =>
              cases rest with
              | nil =>
                  simp [Formula.closeFreeAt,
                    Numbered.quote_hilbert_with?,
                    Numbered.quote_relation_with?, hKind]
              | cons right tail =>
                  cases tail with
                  | cons extra tail =>
                      simp [Formula.closeFreeAt,
                        Numbered.quote_hilbert_with?,
                        Numbered.quote_relation_with?, hKind]
                  | nil =>
                      simp [Formula.closeFreeAt,
                        Numbered.quote_hilbert_with?,
                        Numbered.quote_relation_with?, hKind,
                        quote_term_with?_closeFreeAt_insert
                          freeNaming boundNames id closeDepth left hDepth,
                        quote_term_with?_closeFreeAt_insert
                          freeNaming boundNames id closeDepth right hDepth]
      | predicate =>
          cases arguments with
          | nil =>
              simp [Formula.closeFreeAt,
                Numbered.quote_hilbert_with?,
                Numbered.quote_relation_with?, hKind]
          | cons head tail =>
              have hArguments :=
                quote_terms_with?_closeFreeAt_insert
                  freeNaming boundNames id closeDepth (head :: tail) hDepth
              exact (by
                  simpa [Formula.closeFreeAt,
                    Numbered.quote_hilbert_with?,
                    Numbered.quote_relation_with?,
                    Numbered.quote_terms_with?, hKind] using
                    congrArg (fun result =>
                        result.bind (fun codes =>
                          some (predicate_application_code_term (numₘ((head :: tail).length - 1)) (numₘ(numbering.relation_number relation))
                              (Numbered.argument_sequence codes))))
                      hArguments)
  | equal left right =>
      simp [Formula.closeFreeAt,
        Numbered.quote_hilbert_with?,
        quote_term_with?_closeFreeAt_insert
          freeNaming boundNames id closeDepth left hDepth,
        quote_term_with?_closeFreeAt_insert
          freeNaming boundNames id closeDepth right hDepth]
  | neg body ih =>
      have hBody := ih boundNames quoteDepth closeDepth hDepth
      simpa [Formula.closeFreeAt,
        Numbered.quote_hilbert_with?] using
        congrArg (fun result =>
            result.bind (fun bodyCode =>
              some (neg_codeₘ(bodyCode))))
          hBody
  | conj left right =>
      rfl
  | disj left right =>
      rfl
  | imp left right ihLeft ihRight =>
      have hLeft :=
        ihLeft boundNames quoteDepth closeDepth hDepth
      have hRight :=
        ihRight boundNames quoteDepth closeDepth hDepth
      simp only [Formula.closeFreeAt,
        Numbered.quote_hilbert_with?]
      rw [hLeft, hRight]
  | iff left right =>
      rfl
  | forallE sort body ih =>
      have hSort : sort = numbering.objectSort :=
        numbering.sort_eq_object sort
      subst sort
      let name := binderNaming quoteDepth
      have hDepth' :
          closeDepth + 1 ≤ (name :: boundNames).length := by
        simp
        omega
      have hBody :=
        ih (name :: boundNames) (quoteDepth + 1) (closeDepth + 1) hDepth'
      simp only [List.insertIdx_succ_cons] at hBody
      simpa [Formula.closeFreeAt, Formula.next_depth,
        Numbered.quote_hilbert_with?, name] using
        congrArg (fun result =>
            result.bind (fun bodyCode =>
              some (forall_codeₘ(
                Numbered.named_variable_code name,
                bodyCode))))
          hBody
  | existsE sort body =>
      rfl
/-! ## locally nameless 全称关闭的规范 token 方程 -/
/--
规范 binder 名称列表的最后一个位置始终是最外层 binder `bound_name 0`。
该位置在进入原公式的 `depth` 个内部 binder 后正好具有 de Bruijn 下标 `depth`，
因此是 `closeFreeAt · · depth` 新生成变量应读取的位置。
-/
@[simp]
theorem canonical_bound_names_getElem?_last (depth : Nat) : (canonical_bound_names (depth + 1))[depth]? =
      some (bound_name 0) := by
  induction depth with
  | zero =>
      simp [canonical_bound_names]
  | succ depth ih =>
      simpa [canonical_bound_names] using ih
/-- `getElem` 形式的最外层 binder 读取等式。 -/
@[simp]
theorem canonical_bound_names_getElem_last (depth : Nat) (hDepth :
      depth < (canonical_bound_names (depth + 1)).length) : (canonical_bound_names (depth + 1))[depth] =
      bound_name 0 := by
  have hValue := canonical_bound_names_getElem?_last depth
  rw [List.getElem?_eq_getElem hDepth] at hValue
  exact Option.some.inj hValue
/--
在一个额外 canonical 外层 binder 中，项级 `closeFreeAt` 精确等于把目标自由变量
token 替换为 `bound_name 0`。
`hScoped` 刻意使用少一层的原 scope：它排除原项引用刚加入的外层 binder，从而保证
`closeFreeAt` 对既有 de Bruijn 变量不做额外平移。这个条件正是顶层 admissible
公式及其递归子项自然携带的 scope 信息。
-/
theorem quote_term_tokens_with?_closeFreeAt_canonical_outer
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ]
    [DecidableEq σ.SortSymbol] (id innerDepth : Nat) (term : Term σ) (hScoped :
      TermScoped (Numbered.scope_of_names (canonical_bound_names innerDepth))
        term) :
    Numbered.quote_term_tokens_with?
        free_name (canonical_bound_names (innerDepth + 1)) (Term.closeFreeAt
          numbering.objectSort id innerDepth term) = (Numbered.quote_term_tokens_with?
          free_name (canonical_bound_names (innerDepth + 1))
          term).map (fun sourceTokens =>
          substitute_tokens sourceTokens (variable_token (free_name id))
            [variable_token (bound_name 0)]) := by
  refine Term.rec (motive_1 := fun term =>
      TermScoped (Numbered.scope_of_names (canonical_bound_names innerDepth))
          term →
        Numbered.quote_term_tokens_with?
            free_name (canonical_bound_names (innerDepth + 1)) (Term.closeFreeAt
              numbering.objectSort id innerDepth term) = (Numbered.quote_term_tokens_with?
              free_name (canonical_bound_names (innerDepth + 1))
              term).map (fun sourceTokens =>
              substitute_tokens sourceTokens (variable_token (free_name id))
                [variable_token (bound_name 0)])) (motive_2 := fun terms =>
      (∀ candidate, candidate ∈ terms →
        TermScoped (Numbered.scope_of_names (canonical_bound_names innerDepth))
          candidate) → (terms.map (Term.closeFreeAt
              numbering.objectSort id innerDepth)).mapM (Numbered.quote_term_tokens_with?
              free_name (canonical_bound_names (innerDepth + 1))) = (terms.mapM (Numbered.quote_term_tokens_with?
              free_name (canonical_bound_names (innerDepth + 1)))).map (fun sourceTokenLists =>
              sourceTokenLists.map (fun sourceTokens =>
                substitute_tokens sourceTokens (variable_token (free_name id))
                  [variable_token (bound_name 0)])))
    ?_ ?_ ?_ ?_ term hScoped
  · intro sourceVar hSourceScoped
    cases sourceVar with
    | bvar sort index =>
        have hSort : sort = numbering.objectSort :=
          numbering.sort_eq_object sort
        subst sort
        cases hSourceScoped with
        | bvar hIndex =>
            have hIndexSmall : index < innerDepth := by
              simpa [Numbered.scope_of_names] using hIndex
            have hIndexLarge :
                index < (canonical_bound_names (innerDepth + 1)).length := by
              simp
              omega
            let name := (canonical_bound_names (innerDepth + 1))[index]
            have hName : (canonical_bound_names (innerDepth + 1))[index]? =
                    some name := by
              simp [name]
            have hNameMember :
                name ∈
                  canonical_bound_names (innerDepth + 1) :=
              List.mem_of_getElem? hName
            rcases mem_canonical_bound_names hNameMember with
              ⟨binderDepth, _, hNameValue⟩
            have hNames :
                name ≠ free_name id := by
              rw [hNameValue]
              exact (free_name_ne_bound_name id binderDepth).symm
            have hTokens :
                variable_token name ≠
                  variable_token (free_name id) :=
              variable_token_ne_variable_token hNames
            simp [Term.closeFreeAt, Nat.not_le_of_lt hIndexSmall,
              Numbered.quote_term_tokens_with?, hName,
              substitute_tokens_singleton_ne
                [variable_token (bound_name 0)] hTokens]
    | fvar sort freeId =>
        have hSort : sort = numbering.objectSort :=
          numbering.sort_eq_object sort
        subst sort
        by_cases hId : freeId = id
        · subst freeId
          simp [Term.closeFreeAt,
            Numbered.quote_term_tokens_with?]
        · have hNames : free_name freeId ≠ free_name id :=
            fun hEqual => hId (free_name_injective hEqual)
          have hTokens :
              variable_token (free_name freeId) ≠
                variable_token (free_name id) :=
            variable_token_ne_variable_token hNames
          simp [Term.closeFreeAt, hId,
            Numbered.quote_term_tokens_with?,
            substitute_tokens_singleton_ne
              [variable_token (bound_name 0)] hTokens]
  · intro function arguments argumentsInduction hArgumentsScoped
    cases hArgumentsScoped with
    | app _ _ hArgumentsScoped =>
        simp only [Term.closeFreeAt,
          Numbered.quote_term_tokens_with?]
        rw [argumentsInduction hArgumentsScoped]
        cases hCodes :
            arguments.mapM (Numbered.quote_term_tokens_with?
                free_name (canonical_bound_names (innerDepth + 1))) with
        | none =>
            simp
        | some codes =>
            cases codes with
            | nil =>
                simp [constant_token_ne_variable_token]
            | cons head tail =>
                simp [substitute_tokens_function_application_tokens]
  · intro hScoped
    rfl
  · intro head tail headInduction tailInduction hScoped
    have hHead :
        TermScoped (Numbered.scope_of_names (canonical_bound_names innerDepth))
          head :=
      hScoped head (by simp)
    have hTail :
        ∀ candidate, candidate ∈ tail →
          TermScoped (Numbered.scope_of_names (canonical_bound_names innerDepth))
            candidate := by
      intro candidate hCandidate
      exact hScoped candidate (by simp [hCandidate])
    cases hHeadQuote :
        Numbered.quote_term_tokens_with?
          free_name (canonical_bound_names (innerDepth + 1))
          head <;>
      cases hTailQuote :
        tail.mapM (Numbered.quote_term_tokens_with?
            free_name (canonical_bound_names (innerDepth + 1))) <;>
      simp_all
/-- 项列表版本，供关系与函数参数 quotation 统一复用。 -/
theorem quote_terms_tokens_with?_closeFreeAt_canonical_outer
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ]
    [DecidableEq σ.SortSymbol] (id innerDepth : Nat) (terms : List (Term σ)) (hScoped :
      ∀ term, term ∈ terms →
        TermScoped (Numbered.scope_of_names (canonical_bound_names innerDepth))
          term) : (terms.map (Term.closeFreeAt
          numbering.objectSort id innerDepth)).mapM (Numbered.quote_term_tokens_with?
          free_name (canonical_bound_names (innerDepth + 1))) = (terms.mapM (Numbered.quote_term_tokens_with?
          free_name (canonical_bound_names (innerDepth + 1)))).map (fun sourceTokenLists =>
          sourceTokenLists.map (fun sourceTokens =>
            substitute_tokens sourceTokens (variable_token (free_name id))
              [variable_token (bound_name 0)])) := by
  induction terms with
  | nil =>
      rfl
  | cons head tail ih =>
      have hHead := quote_term_tokens_with?_closeFreeAt_canonical_outer
        id innerDepth head (hScoped head (by simp))
      have hTail :
          ∀ term, term ∈ tail →
            TermScoped (Numbered.scope_of_names (canonical_bound_names innerDepth))
              term := by
        intro term hTerm
        exact hScoped term (by simp [hTerm])
      cases hHeadQuote :
          Numbered.quote_term_tokens_with?
            free_name (canonical_bound_names (innerDepth + 1))
            head <;>
        cases hTailQuote :
          tail.mapM (Numbered.quote_term_tokens_with?
              free_name (canonical_bound_names (innerDepth + 1))) <;>
        simp_all
/--
公式级规范关闭方程。
把一个原本处于 `innerDepth` 层内部 scope 的 Hilbert 核公式放进新外层 binder 后，
`closeFreeAt` 的 quotation 正好是“先按新入口深度 quotation，再把目标偶数自由变量
token 替换成最外层奇数 binder token”。这条方程消除了全称闭包中的 α-命名歧义。
-/
theorem quote_hilbert_tokens_with?_closeFreeAt_canonical_outer
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ]
    [DecidableEq σ.SortSymbol] (id innerDepth : Nat) (formula : Formula σ) (hScoped :
      FormulaScoped (Numbered.scope_of_names (canonical_bound_names innerDepth))
        formula) :
    Numbered.quote_hilbert_tokens_with?
        free_name bound_name (canonical_bound_names (innerDepth + 1)) (innerDepth + 1) (Formula.closeFreeAt
          numbering.objectSort id innerDepth formula) = (Numbered.quote_hilbert_tokens_with?
          free_name bound_name (canonical_bound_names (innerDepth + 1)) (innerDepth + 1) formula).map (fun sourceTokens =>
          substitute_tokens sourceTokens (variable_token (free_name id))
            [variable_token (bound_name 0)]) := by
  induction formula generalizing innerDepth with
  | falsum =>
      rfl
  | truth =>
      rfl
  | rel relation arguments =>
      cases hScoped with
      | rel _ _ hArgumentsScoped =>
          cases hKind : numbering.relation_kind relation with
          | membership =>
              cases arguments with
              | nil =>
                  simp [Formula.closeFreeAt,
                    Numbered.quote_hilbert_tokens_with?,
                    Numbered.quote_relation_tokens_with?, hKind]
              | cons left rest =>
                  cases rest with
                  | nil =>
                      simp [Formula.closeFreeAt,
                        Numbered.quote_hilbert_tokens_with?,
                        Numbered.quote_relation_tokens_with?, hKind]
                  | cons right tail =>
                      cases tail with
                      | cons extra tail =>
                          simp [Formula.closeFreeAt,
                            Numbered.quote_hilbert_tokens_with?,
                            Numbered.quote_relation_tokens_with?, hKind]
                      | nil =>
                          have hLeft :=
                            quote_term_tokens_with?_closeFreeAt_canonical_outer
                              id innerDepth left (hArgumentsScoped left (by simp))
                          have hRight :=
                            quote_term_tokens_with?_closeFreeAt_canonical_outer
                              id innerDepth right (hArgumentsScoped right (by simp))
                          simp only [Formula.closeFreeAt, List.map_cons,
                            List.map_nil,
                            Numbered.quote_hilbert_tokens_with?,
                            Numbered.quote_relation_tokens_with?, hKind]
                          rw [hLeft, hRight]
                          cases Numbered.quote_term_tokens_with?
                              free_name (canonical_bound_names (innerDepth + 1)) left <;>
                            cases Numbered.quote_term_tokens_with?
                                free_name (canonical_bound_names (innerDepth + 1)) right <;>
                              simp [substitute_tokens_membership_tokens]
          | predicate =>
              cases arguments with
              | nil =>
                  simp [Formula.closeFreeAt,
                    Numbered.quote_hilbert_tokens_with?,
                    Numbered.quote_relation_tokens_with?, hKind]
              | cons head tail =>
                  have hArguments :=
                    quote_terms_tokens_with?_closeFreeAt_canonical_outer
                      id innerDepth (head :: tail) hArgumentsScoped
                  have hArguments' : (Term.closeFreeAt
                            numbering.objectSort id innerDepth head ::
                          tail.map (Term.closeFreeAt
                            numbering.objectSort id innerDepth)).mapM (Numbered.quote_term_tokens_with?
                            free_name (canonical_bound_names (innerDepth + 1))) = ((head :: tail).mapM (Numbered.quote_term_tokens_with?
                            free_name (canonical_bound_names (innerDepth + 1)))).map (fun sourceTokenLists =>
                            sourceTokenLists.map (fun sourceTokens =>
                              substitute_tokens sourceTokens (variable_token (free_name id))
                                [variable_token (bound_name 0)])) := by
                    simpa only [List.map_cons] using hArguments
                  simp only [Formula.closeFreeAt, List.map_cons,
                    Numbered.quote_hilbert_tokens_with?,
                    Numbered.quote_relation_tokens_with?, hKind]
                  rw [hArguments']
                  cases hCodes : (head :: tail).mapM (Numbered.quote_term_tokens_with?
                          free_name (canonical_bound_names (innerDepth + 1))) with
                  | none =>
                      simp
                  | some codes =>
                      simp [substitute_tokens_predicate_application_tokens]
  | equal left right =>
      cases hScoped with
      | equal hLeftScoped hRightScoped =>
          have hLeft :=
            quote_term_tokens_with?_closeFreeAt_canonical_outer
              id innerDepth left hLeftScoped
          have hRight :=
            quote_term_tokens_with?_closeFreeAt_canonical_outer
              id innerDepth right hRightScoped
          simp only [Formula.closeFreeAt,
            Numbered.quote_hilbert_tokens_with?]
          rw [hLeft, hRight]
          cases Numbered.quote_term_tokens_with?
              free_name (canonical_bound_names (innerDepth + 1)) left <;>
            cases Numbered.quote_term_tokens_with?
                free_name (canonical_bound_names (innerDepth + 1)) right <;>
              simp [substitute_tokens_equality_tokens]
  | neg body ih =>
      cases hScoped with
      | neg hBodyScoped =>
          simp only [Formula.closeFreeAt,
            Numbered.quote_hilbert_tokens_with?]
          rw [ih innerDepth hBodyScoped]
          cases Numbered.quote_hilbert_tokens_with?
              free_name bound_name (canonical_bound_names (innerDepth + 1)) (innerDepth + 1) body <;>
            simp [substitute_tokens_negation_tokens]
  | conj left right =>
      rfl
  | disj left right =>
      rfl
  | imp left right ihLeft ihRight =>
      cases hScoped with
      | imp hLeftScoped hRightScoped =>
          simp only [Formula.closeFreeAt,
            Numbered.quote_hilbert_tokens_with?]
          rw [ihLeft innerDepth hLeftScoped,
            ihRight innerDepth hRightScoped]
          cases Numbered.quote_hilbert_tokens_with?
              free_name bound_name (canonical_bound_names (innerDepth + 1)) (innerDepth + 1) left <;>
            cases Numbered.quote_hilbert_tokens_with?
                free_name bound_name (canonical_bound_names (innerDepth + 1)) (innerDepth + 1) right <;>
              simp [substitute_tokens_implication_tokens]
  | iff left right =>
      rfl
  | forallE sort body ih =>
      have hSort : sort = numbering.objectSort :=
        numbering.sort_eq_object sort
      subst sort
      cases hScoped with
      | forallE _ hBodyScoped =>
          have hBodyScoped' :
              FormulaScoped (Numbered.scope_of_names (canonical_bound_names (innerDepth + 1)))
                body := by
            rw [← Numbered.scope_of_names_cons (bound_name innerDepth) (canonical_bound_names innerDepth)
              numbering.objectSort] at hBodyScoped
            simpa [canonical_bound_names] using hBodyScoped
          have hBody :=
            ih (innerDepth + 1) hBodyScoped'
          cases hSource :
              Numbered.quote_hilbert_tokens_with?
                free_name bound_name (canonical_bound_names ((innerDepth + 1) + 1)) ((innerDepth + 1) + 1) body with
          | none =>
              rw [hSource] at hBody
              simp at hBody
              have hSource' :
                  Numbered.quote_hilbert_tokens_with?
                      free_name bound_name (bound_name (innerDepth + 1) ::
                        bound_name innerDepth ::
                          canonical_bound_names innerDepth) ((innerDepth + 1) + 1) body =
                    none := by
                simpa [canonical_bound_names] using hSource
              have hBody' :
                  Numbered.quote_hilbert_tokens_with?
                      free_name bound_name (bound_name (innerDepth + 1) ::
                        bound_name innerDepth ::
                          canonical_bound_names innerDepth) ((innerDepth + 1) + 1) (Formula.closeFreeAt
                        numbering.objectSort id (innerDepth + 1) body) =
                    none := by
                simpa [canonical_bound_names] using hBody
              simp [Formula.closeFreeAt, Formula.next_depth,
                Numbered.quote_hilbert_tokens_with?,
                canonical_bound_names, hSource', hBody']
          | some sourceTokens =>
              rw [hSource] at hBody
              simp at hBody
              have hSource' :
                  Numbered.quote_hilbert_tokens_with?
                      free_name bound_name (bound_name (innerDepth + 1) ::
                        bound_name innerDepth ::
                          canonical_bound_names innerDepth) ((innerDepth + 1) + 1) body =
                    some sourceTokens := by
                simpa [canonical_bound_names] using hSource
              have hBody' :
                  Numbered.quote_hilbert_tokens_with?
                      free_name bound_name (bound_name (innerDepth + 1) ::
                        bound_name innerDepth ::
                          canonical_bound_names innerDepth) ((innerDepth + 1) + 1) (Formula.closeFreeAt
                        numbering.objectSort id (innerDepth + 1) body) =
                    some (substitute_tokens sourceTokens (variable_token (free_name id))
                      [variable_token (bound_name 0)]) := by
                simpa [canonical_bound_names] using hBody
              simp [Formula.closeFreeAt, Formula.next_depth,
                Numbered.quote_hilbert_tokens_with?,
                canonical_bound_names, hSource', hBody',
                substitute_tokens_universal_tokens, (free_name_ne_bound_name
                  id (innerDepth + 1)).symm]
  | existsE sort body =>
      rfl
/-- 顶层版本：正是一次 `HilbertLogicalAxiom.forall_closure` 所需的 token 方程。 -/
theorem quote_hilbert_tokens_closeFreeAt_zero_canonical_outer
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ]
    [DecidableEq σ.SortSymbol] (id : FreeVarId) (formula : Formula σ) (hScoped : FormulaScoped Scope.empty formula) :
    Numbered.quote_hilbert_tokens_with?
        free_name bound_name [bound_name 0] 1 (Formula.closeFreeAt numbering.objectSort id 0 formula) = (Numbered.quote_hilbert_tokens_with?
          free_name bound_name [bound_name 0] 1 formula).map (fun sourceTokens =>
          substitute_tokens sourceTokens (variable_token (free_name id))
            [variable_token (bound_name 0)]) := by
  simpa [canonical_bound_names,
    Numbered.scope_of_names] using
    quote_hilbert_tokens_with?_closeFreeAt_canonical_outer
      id 0 formula hScoped
/-! ## 规范 quotation 的替换方程 -/
/-- 空 binder 环境中的通用规范项 token quotation。 -/
def quote_term_tokens?
    {σ : Signature.{u, v, w}} [QuotationNumbering σ] (term : Term σ) : Option (List Nat) :=
  Numbered.quote_term_tokens_with? free_name [] term
/--
空 binder 环境中的项 token quotation 一旦成功，源项必然 bound-closed。
这使 quotation substitution 不再要求调用方重复提交 scope 证明。
-/
theorem quote_term_tokens?_boundClosed_of_some
    {σ : Signature.{u, v, w}}
    [QuotationNumbering σ] [DecidableEq σ.SortSymbol]
    {term : Term σ} {tokens : List Nat} (hQuote : quote_term_tokens? term = some tokens) :
    Term.BoundClosed term := by
  unfold quote_term_tokens? at hQuote
  refine Term.rec (motive_1 := fun term =>
      ∀ tokens,
        Numbered.quote_term_tokens_with? free_name [] term =
            some tokens →
          Term.BoundClosed term) (motive_2 := fun terms =>
      ∀ pieces,
        terms.mapM (Numbered.quote_term_tokens_with? free_name []) =
            some pieces →
          ∀ term, term ∈ terms → Term.BoundClosed term)
    ?_ ?_ ?_ ?_ term tokens hQuote
  · intro sourceVar sourceTokens hSourceTokens
    cases sourceVar with
    | bvar sort index =>
        simp [Numbered.quote_term_tokens_with?] at hSourceTokens
    | fvar sort id =>
        exact TermScoped.fvar sort id
  · intro function arguments ih resultTokens hResultTokens
    cases hArgumentTokens :
        arguments.mapM (Numbered.quote_term_tokens_with? free_name []) with
    | none =>
        simp [Numbered.quote_term_tokens_with?,
          hArgumentTokens] at hResultTokens
    | some argumentTokens =>
        exact TermScoped.app function arguments (ih argumentTokens hArgumentTokens)
  · intro pieces hPieces term hTerm
    simp at hPieces
    subst pieces
    simp at hTerm
  · intro head tail ihHead ihTail pieces hPieces term hTerm
    cases hHeadTokens :
        Numbered.quote_term_tokens_with? free_name [] head with
    | none =>
        simp [hHeadTokens] at hPieces
    | some headTokens =>
        cases hTailTokens :
            tail.mapM (Numbered.quote_term_tokens_with? free_name []) with
        | none =>
            simp [hHeadTokens, hTailTokens] at hPieces
        | some tailTokens =>
            simp [hHeadTokens, hTailTokens] at hPieces
            subst pieces
            simp only [List.mem_cons] at hTerm
            rcases hTerm with rfl | hTerm
            · exact ihHead headTokens hHeadTokens
            · exact ihTail tailTokens hTailTokens term hTerm
/-- 每个 admissible 单排序项都有规范 token quotation。 -/
theorem quote_term_tokens?_exists
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ] [DecidableEq σ.SortSymbol]
    {term : Term σ} (hTerm : Term.Admissible term numbering.objectSort) :
    ∃ tokens, quote_term_tokens? term = some tokens := by
  have hScoped :
      TermScoped (Numbered.scope_of_names ([] : List Nat)) term := by
    simpa [Numbered.scope_of_names] using hTerm.2
  exact Numbered.quote_term_tokens_with?_exists free_name [] hScoped
/--
规范公式 quotation 与无捕获自由变量替换严格交换。
右侧是可计算的标准符号串替换；替换项的 quotation 结果显式出现，因而该定理不会
把对象层 `subst_codeₘ` 误当作 Lean 计算。
-/
theorem quote_tokens?_substituteFree_of_quote_term
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ] [DecidableEq σ.SortSymbol] (formula : Formula σ) (id : FreeVarId) (replacement : Term σ)
    (hReplacementClosed : Term.BoundClosed replacement) (replacementTokens : List Nat) (hQuoteReplacement :
      quote_term_tokens? replacement = some replacementTokens) :
    Numbered.quote_tokens? (Formula.substituteFree numbering.objectSort id replacement formula) = (Numbered.quote_tokens? formula).map (fun sourceTokens =>
          substitute_tokens sourceTokens (variable_token (free_name id)) replacementTokens) := by
  unfold quote_term_tokens? at hQuoteReplacement
  unfold Numbered.quote_tokens? Numbered.quote_tokens_with?
  rw [Formula.hilbertize_substituteFree]
  exact quote_hilbert_tokens_with?_substituteFree
    free_name bound_name free_name_injective [] 0 id (by simp) (fun binderDepth => (free_name_ne_bound_name id binderDepth).symm)
    replacement hReplacementClosed replacementTokens hQuoteReplacement (Formula.hilbertize numbering.objectSort formula)
/-- 已知源公式与替换项的具体符号串时，替换后 quotation 直接计算为标准替换串。 -/
theorem quote_tokens?_substituteFree_some
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ] [DecidableEq σ.SortSymbol]
    {formula : Formula σ} {id : FreeVarId} {replacement : Term σ}
    {sourceTokens replacementTokens : List Nat} (hReplacementClosed : Term.BoundClosed replacement)
    (hSourceQuote : Numbered.quote_tokens? formula = some sourceTokens) (hReplacementQuote :
      quote_term_tokens? replacement = some replacementTokens) :
    Numbered.quote_tokens? (Formula.substituteFree numbering.objectSort id replacement formula) =
      some (substitute_tokens sourceTokens (variable_token (free_name id)) replacementTokens) := by
  rw [quote_tokens?_substituteFree_of_quote_term
    formula id replacement hReplacementClosed replacementTokens
      hReplacementQuote,
    hSourceQuote]
  rfl
end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
