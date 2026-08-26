import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.TokenReflection.Parsing

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace GodelQuotation
set_option autoImplicit false
open Nonlogical.BasicSetTheory

/-! ## 正式 quotation 到原始 token 树 -/
universe u v w u₁ u₂
/-- 映射成功结果中的每个元素都来自一个对应的输入元素。 -/
private theorem option_mapM_eq_some_right
    {α : Type u₁} {β : Type u₂} (transform : α → Option β)
    {items : List α} {results : List β} (hMap : items.mapM transform = some results)
    {result : β} (hResult : result ∈ results) :
    ∃ item,
      item ∈ items ∧
        transform item = some result := by
  induction items generalizing results with
  | nil =>
      simp at hMap
      subst results
      simp at hResult
  | cons head tail ih =>
      cases hHead : transform head with
      | none =>
          simp [hHead] at hMap
      | some headResult =>
          cases hTail : tail.mapM transform with
          | none =>
              simp [hHead, hTail] at hMap
          | some tailResults =>
              simp [hHead, hTail] at hMap
              subst results
              rcases List.mem_cons.mp hResult with
                rfl | hTailResult
              · exact
                  ⟨head, by simp, hHead⟩
              · rcases ih hTail hTailResult with
                  ⟨item, hItem, hItemResult⟩
                have hCons :
                    item ∈ head :: tail :=
                  List.mem_cons_of_mem head hItem
                exact
                  ⟨item, hCons,
                    hItemResult⟩
/-- 变量 token 始终为奇数。 -/
theorem variable_token_odd (name : Nat) :
    Numbered.variable_token name % 2 = 1 := by
  simp [Numbered.variable_token, Nat.pow_mod]
/-- 常元 token 始终为奇数。 -/
theorem constant_token_odd (index : Nat) :
    Numbered.constant_token index % 2 = 1 := by
  simp [Numbered.constant_token, Nat.pow_mod]
/-- 正元函数 token 始终为奇数。 -/
theorem function_token_odd (arityPredecessor index : Nat) :
    Numbered.function_token
        arityPredecessor index % 2 =
      1 := by
  simp [Numbered.function_token, Nat.pow_mod,
    Nat.mul_mod]
/-- 正元谓词 token 始终为奇数。 -/
theorem predicate_token_odd (arityPredecessor index : Nat) :
    Numbered.predicate_token
        arityPredecessor index % 2 =
      1 := by
  simp [Numbered.predicate_token, Nat.pow_mod,
    Nat.mul_mod]
/-- 显式环境下的通用项 quotation 树。 -/
@[simp]
def quote_term_token_tree_with?
    {σ : Signature.{u, v, w}}
    [QuotationNumbering σ] (freeNaming : FreeVarId → Nat) (boundNames : List Nat) :
    Term σ → Option RawTermTokenTree
  | .var (.bvar _ index) =>
      (boundNames[index]?).map (fun name =>
          .atom (Numbered.variable_token name))
  | .var (.fvar _ id) =>
      some (.atom (Numbered.variable_token (freeNaming id)))
  | .app function arguments => do
      let trees ← arguments.mapM (quote_term_token_tree_with?
          freeNaming boundNames)
      match trees with
      | [] =>
          pure (.atom (Numbered.constant_token (QuotationNumbering.function_number
                  function)))
      | _ :: _ =>
          pure (.application (Numbered.function_token (arguments.length - 1) (QuotationNumbering.function_number
                  function))
              trees)
termination_by term => term
/-- 显式环境下的通用关系原子 quotation 树。 -/
@[simp]
def quote_relation_token_tree_with?
    {σ : Signature.{u, v, w}}
    [QuotationNumbering σ] (freeNaming : FreeVarId → Nat) (boundNames : List Nat) (relation : σ.RelSymbol) (arguments : List (Term σ)) :
    Option RawHilbertTokenTree :=
  match
      QuotationNumbering.relation_kind relation,
      arguments with
  | .membership, [left, right] => do
      let leftTree ←
        quote_term_token_tree_with?
          freeNaming boundNames left
      let rightTree ←
        quote_term_token_tree_with?
          freeNaming boundNames right
      pure (.membership leftTree rightTree)
  | .predicate, head :: tail => do
      let trees ← (head :: tail).mapM (quote_term_token_tree_with?
            freeNaming boundNames)
      pure (.predicate (Numbered.predicate_token ((head :: tail).length - 1) (QuotationNumbering.relation_number
              relation))
          trees)
  | _, _ =>
      none
/-- 显式环境下的通用 Hilbert 核 quotation 树。 -/
@[simp]
def quote_hilbert_token_tree_with?
    {σ : Signature.{u, v, w}}
    [QuotationNumbering σ] (freeNaming binderNaming : Nat → Nat) (boundNames : List Nat) (depth : Nat) :
    Formula σ → Option RawHilbertTokenTree
  | .rel relation arguments =>
      quote_relation_token_tree_with?
        freeNaming boundNames relation arguments
  | .equal left right => do
      let leftTree ←
        quote_term_token_tree_with?
          freeNaming boundNames left
      let rightTree ←
        quote_term_token_tree_with?
          freeNaming boundNames right
      pure (.equality leftTree rightTree)
  | .neg body => do
      let bodyTree ←
        quote_hilbert_token_tree_with?
          freeNaming binderNaming
          boundNames depth body
      pure (.negation bodyTree)
  | .imp left right => do
      let leftTree ←
        quote_hilbert_token_tree_with?
          freeNaming binderNaming
          boundNames depth left
      let rightTree ←
        quote_hilbert_token_tree_with?
          freeNaming binderNaming
          boundNames depth right
      pure (.implication leftTree rightTree)
  | .forallE _ body => do
      let name := binderNaming depth
      let bodyTree ←
        quote_hilbert_token_tree_with?
          freeNaming binderNaming (name :: boundNames) (depth + 1) body
      pure (.universal (Numbered.variable_token name)
          bodyTree)
  | _ =>
      none
/-- 每个成功的正式项 quotation 树都满足奇数首部条件。 -/
private theorem quote_term_token_tree_with?_heads_odd
    {σ : Signature.{u, v, w}}
    [QuotationNumbering σ] (freeNaming : FreeVarId → Nat) (boundNames : List Nat) :
    ∀ {term : Term σ} {tree : RawTermTokenTree},
      quote_term_token_tree_with?
          freeNaming boundNames term =
        some tree →
      tree.HeadsOdd
  | .var (.bvar sort index), tree, hTree => by
      cases hName : boundNames[index]? with
      | none =>
          simp [quote_term_token_tree_with?,
            hName] at hTree
      | some name =>
          simp [quote_term_token_tree_with?,
            hName] at hTree
          subst tree
          simpa [RawTermTokenTree.HeadsOdd]
            using variable_token_odd name
  | .var (.fvar sort id), tree, hTree => by
      simp [quote_term_token_tree_with?] at hTree
      subst tree
      simpa [RawTermTokenTree.HeadsOdd]
        using variable_token_odd (freeNaming id)
  | .app function arguments, tree, hTree => by
      cases hTrees :
          arguments.mapM (quote_term_token_tree_with?
              freeNaming boundNames) with
      | none =>
          simp [quote_term_token_tree_with?,
            hTrees] at hTree
      | some trees =>
          cases trees with
          | nil =>
              simp [quote_term_token_tree_with?,
                hTrees] at hTree
              subst tree
              simpa [RawTermTokenTree.HeadsOdd]
                using
                  constant_token_odd (QuotationNumbering.function_number
                      function)
          | cons first rest =>
              simp [quote_term_token_tree_with?,
                hTrees] at hTree
              subst tree
              simp only [RawTermTokenTree.HeadsOdd]
              constructor
              · exact
                  function_token_odd (arguments.length - 1) (QuotationNumbering.function_number
                      function)
              · intro candidate hCandidate
                rcases
                    option_mapM_eq_some_right (quote_term_token_tree_with?
                        freeNaming boundNames)
                      hTrees hCandidate with
                  ⟨argument, hArgument,
                    hArgumentTree⟩
                exact
                  quote_term_token_tree_with?_heads_odd
                    freeNaming boundNames
                    hArgumentTree
termination_by term tree _hTree => term
/-- 成功的关系原子 quotation 树满足 Hilbert parser 的词法条件。 -/
private theorem quote_relation_token_tree_with?_lexically_separated
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ] (freeNaming : FreeVarId → Nat) (boundNames : List Nat)
    {relation : σ.RelSymbol}
    {arguments : List (Term σ)}
    {tree : RawHilbertTokenTree} (hTree :
      quote_relation_token_tree_with?
          freeNaming boundNames
          relation arguments =
        some tree) :
    tree.LexicallySeparated := by
  cases hKind :
      numbering.relation_kind relation with
  | membership =>
      cases arguments with
      | nil =>
          simp [quote_relation_token_tree_with?,
            hKind] at hTree
      | cons left tail =>
          cases tail with
          | nil =>
              simp [quote_relation_token_tree_with?,
                hKind] at hTree
          | cons right extra =>
              cases extra with
              | nil =>
                  cases hLeft :
                      quote_term_token_tree_with?
                        freeNaming boundNames left with
                  | none =>
                      simp [quote_relation_token_tree_with?,
                        hKind, hLeft] at hTree
                  | some leftTree =>
                      cases hRight :
                          quote_term_token_tree_with?
                            freeNaming boundNames right with
                      | none =>
                          simp [quote_relation_token_tree_with?,
                            hKind, hLeft, hRight] at hTree
                      | some rightTree =>
                          simp [quote_relation_token_tree_with?,
                            hKind, hLeft, hRight] at hTree
                          subst tree
                          exact
                            ⟨
                              quote_term_token_tree_with?_heads_odd
                                freeNaming boundNames hLeft,
                              quote_term_token_tree_with?_heads_odd
                                freeNaming boundNames hRight
                            ⟩
              | cons extra rest =>
                  simp [quote_relation_token_tree_with?,
                    hKind] at hTree
  | predicate =>
      cases arguments with
      | nil =>
          simp [quote_relation_token_tree_with?,
            hKind] at hTree
      | cons head tail =>
          cases hTrees : (head :: tail).mapM (quote_term_token_tree_with?
                  freeNaming boundNames) with
          | none =>
              simp [quote_relation_token_tree_with?,
                hKind, hTrees] at hTree
          | some trees =>
              simp [quote_relation_token_tree_with?,
                hKind, hTrees] at hTree
              subst tree
              constructor
              · exact
                  predicate_token_odd ((head :: tail).length - 1) (numbering.relation_number relation)
              · intro candidate hCandidate
                rcases
                    option_mapM_eq_some_right (quote_term_token_tree_with?
                        freeNaming boundNames)
                      hTrees hCandidate with
                  ⟨argument, hArgument,
                    hArgumentTree⟩
                exact
                  quote_term_token_tree_with?_heads_odd
                    freeNaming boundNames
                    hArgumentTree
/-- 每个成功的正式 Hilbert quotation 树都满足 parser 词法条件。 -/
theorem quote_hilbert_token_tree_with?_lexically_separated
    {σ : Signature.{u, v, w}}
    [QuotationNumbering σ] (freeNaming binderNaming : Nat → Nat) (boundNames : List Nat) (depth : Nat) :
    ∀ {formula : Formula σ}
        {tree : RawHilbertTokenTree},
      quote_hilbert_token_tree_with?
          freeNaming binderNaming
          boundNames depth formula =
        some tree →
      tree.LexicallySeparated
  | .falsum, tree, hTree => by
      simp [quote_hilbert_token_tree_with?] at hTree
  | .truth, tree, hTree => by
      simp [quote_hilbert_token_tree_with?] at hTree
  | .rel relation arguments, tree, hTree =>
      quote_relation_token_tree_with?_lexically_separated
        freeNaming boundNames hTree
  | .equal left right, tree, hTree => by
      cases hLeft :
          quote_term_token_tree_with?
            freeNaming boundNames left with
      | none =>
          simp [quote_hilbert_token_tree_with?,
            hLeft] at hTree
      | some leftTree =>
          cases hRight :
              quote_term_token_tree_with?
                freeNaming boundNames right with
          | none =>
              simp [quote_hilbert_token_tree_with?,
                hLeft, hRight] at hTree
          | some rightTree =>
              simp [quote_hilbert_token_tree_with?,
                hLeft, hRight] at hTree
              subst tree
              exact
                ⟨
                  quote_term_token_tree_with?_heads_odd
                    freeNaming boundNames hLeft,
                  quote_term_token_tree_with?_heads_odd
                    freeNaming boundNames hRight
                ⟩
  | .neg body, tree, hTree => by
      cases hBody :
          quote_hilbert_token_tree_with?
            freeNaming binderNaming
            boundNames depth body with
      | none =>
          simp [quote_hilbert_token_tree_with?,
            hBody] at hTree
      | some bodyTree =>
          simp [quote_hilbert_token_tree_with?,
            hBody] at hTree
          subst tree
          change bodyTree.LexicallySeparated
          exact
            quote_hilbert_token_tree_with?_lexically_separated
              freeNaming binderNaming
              boundNames depth hBody
  | .conj left right, tree, hTree => by
      simp [quote_hilbert_token_tree_with?] at hTree
  | .disj left right, tree, hTree => by
      simp [quote_hilbert_token_tree_with?] at hTree
  | .imp left right, tree, hTree => by
      cases hLeft :
          quote_hilbert_token_tree_with?
            freeNaming binderNaming
            boundNames depth left with
      | none =>
          simp [quote_hilbert_token_tree_with?,
            hLeft] at hTree
      | some leftTree =>
          cases hRight :
              quote_hilbert_token_tree_with?
                freeNaming binderNaming
                boundNames depth right with
          | none =>
              simp [quote_hilbert_token_tree_with?,
                hLeft, hRight] at hTree
          | some rightTree =>
              simp [quote_hilbert_token_tree_with?,
                hLeft, hRight] at hTree
              subst tree
              exact
                ⟨
                  quote_hilbert_token_tree_with?_lexically_separated
                    freeNaming binderNaming
                    boundNames depth hLeft,
                  quote_hilbert_token_tree_with?_lexically_separated
                    freeNaming binderNaming
                    boundNames depth hRight
                ⟩
  | .iff left right, tree, hTree => by
      simp [quote_hilbert_token_tree_with?] at hTree
  | .forallE sort body, tree, hTree => by
      let name := binderNaming depth
      cases hBody :
          quote_hilbert_token_tree_with?
            freeNaming binderNaming (name :: boundNames) (depth + 1) body with
      | none =>
          simp [quote_hilbert_token_tree_with?,
            name, hBody] at hTree
      | some bodyTree =>
          simp [quote_hilbert_token_tree_with?,
            name, hBody] at hTree
          subst tree
          change bodyTree.LexicallySeparated
          exact
            quote_hilbert_token_tree_with?_lexically_separated
              freeNaming binderNaming (name :: boundNames) (depth + 1)
              hBody
  | .existsE sort body, tree, hTree => by
      simp [quote_hilbert_token_tree_with?] at hTree
/-! ## 正式 token quotation 与原始树序列化同步 -/
mutual
  /-- 单个项的正式 token quotation 等于原始项树序列化。 -/
  theorem quote_term_tokens_with?_eq_token_tree
      {σ : Signature.{u, v, w}}
      [QuotationNumbering σ] (freeNaming : FreeVarId → Nat) (boundNames : List Nat) :
      ∀ term : Term σ,
      Numbered.quote_term_tokens_with?
          freeNaming boundNames term = (quote_term_token_tree_with?
          freeNaming boundNames term).map
            RawTermTokenTree.tokens
    | .var (.bvar sort index) => by
        cases hName : boundNames[index]? <;>
          simp [Numbered.quote_term_tokens_with?,
            quote_term_token_tree_with?,
            RawTermTokenTree.tokens, hName]
    | .var (.fvar sort id) => by
        simp [Numbered.quote_term_tokens_with?,
          quote_term_token_tree_with?,
          RawTermTokenTree.tokens]
    | .app function arguments => by
        simp only [
          Numbered.quote_term_tokens_with?,
          quote_term_token_tree_with?]
        rw [
          quote_term_token_lists_with?_eq_token_trees
            freeNaming boundNames arguments]
        cases hTrees :
            arguments.mapM (quote_term_token_tree_with?
                freeNaming boundNames) with
        | none =>
            simp
        | some trees =>
            cases trees with
            | nil =>
                simp [RawTermTokenTree.tokens,
                  Numbered.constant_token]
            | cons first rest =>
                simp [RawTermTokenTree.tokens,
                  RawTermTokenTree.list_tokens,
                  Numbered.function_application_tokens,
                  List.append_assoc]
  termination_by term => sizeOf term
  /-- 一列项的 `mapM` quotation 与一列原始项树逐项同步。 -/
  theorem quote_term_token_lists_with?_eq_token_trees
      {σ : Signature.{u, v, w}}
      [QuotationNumbering σ] (freeNaming : FreeVarId → Nat) (boundNames : List Nat) :
      ∀ terms : List (Term σ),
      terms.mapM (Numbered.quote_term_tokens_with?
            freeNaming boundNames) = (terms.mapM (quote_term_token_tree_with?
            freeNaming boundNames)).map (List.map RawTermTokenTree.tokens)
    | [] =>
        rfl
    | head :: tail => by
        rw [
          List.mapM_cons,
          quote_term_tokens_with?_eq_token_tree
            freeNaming boundNames head,
          quote_term_token_lists_with?_eq_token_trees
            freeNaming boundNames tail]
        cases hHead :
            quote_term_token_tree_with?
              freeNaming boundNames head <;>
          cases hTail :
              tail.mapM (quote_term_token_tree_with?
                  freeNaming boundNames) <;>
          simp [hHead, hTail]
  termination_by terms => sizeOf terms
end
/-- 关系原子的正式 token quotation 等于原始 Hilbert 树序列化。 -/
private theorem quote_relation_tokens_with?_eq_token_tree
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ] (freeNaming : FreeVarId → Nat) (boundNames : List Nat) (relation : σ.RelSymbol) (arguments : List (Term σ)) :
    Numbered.quote_relation_tokens_with?
        freeNaming boundNames relation arguments = (quote_relation_token_tree_with?
        freeNaming boundNames
        relation arguments).map
          RawHilbertTokenTree.tokens := by
  cases hKind :
      numbering.relation_kind relation with
  | membership =>
      cases arguments with
      | nil =>
          simp [Numbered.quote_relation_tokens_with?,
            quote_relation_token_tree_with?, hKind]
      | cons left tail =>
          cases tail with
          | nil =>
              simp [Numbered.quote_relation_tokens_with?,
                quote_relation_token_tree_with?, hKind]
          | cons right extra =>
              cases extra with
              | nil =>
                  simp only [
                    Numbered.quote_relation_tokens_with?,
                    quote_relation_token_tree_with?,
                    hKind]
                  rw [
                    quote_term_tokens_with?_eq_token_tree,
                    quote_term_tokens_with?_eq_token_tree]
                  cases hLeft :
                      quote_term_token_tree_with?
                        freeNaming boundNames left <;>
                    cases hRight :
                      quote_term_token_tree_with?
                        freeNaming boundNames right <;>
                    simp [RawHilbertTokenTree.tokens,
                      Numbered.membership_tokens,
                      List.append_assoc]
              | cons extra rest =>
                  simp [Numbered.quote_relation_tokens_with?,
                    quote_relation_token_tree_with?,
                    hKind]
  | predicate =>
      cases arguments with
      | nil =>
          simp [Numbered.quote_relation_tokens_with?,
            quote_relation_token_tree_with?, hKind]
      | cons head tail =>
          simp only [
            Numbered.quote_relation_tokens_with?,
            quote_relation_token_tree_with?,
            hKind]
          rw [
            quote_term_token_lists_with?_eq_token_trees]
          cases hTrees : (head :: tail).mapM (quote_term_token_tree_with?
                  freeNaming boundNames) with
          | none =>
              simp
          | some trees =>
              simp [RawHilbertTokenTree.tokens,
                Numbered.predicate_application_tokens]
/--
正式 Hilbert token quotation 与通用原始树序列化严格同步。
后续反射证明只依赖这一条同步边界，不重新展开具体签名的函数与关系枚举。
-/
theorem quote_hilbert_tokens_with?_eq_generic_token_tree
    {σ : Signature.{u, v, w}}
    [QuotationNumbering σ] (freeNaming binderNaming : Nat → Nat) (boundNames : List Nat) (depth : Nat) (formula : Formula σ) :
    Numbered.quote_hilbert_tokens_with?
        freeNaming binderNaming
        boundNames depth formula = (quote_hilbert_token_tree_with?
        freeNaming binderNaming
        boundNames depth formula).map
          RawHilbertTokenTree.tokens := by
  induction formula generalizing boundNames depth with
  | falsum =>
      rfl
  | truth =>
      rfl
  | rel relation arguments =>
      exact
        quote_relation_tokens_with?_eq_token_tree
          freeNaming boundNames
          relation arguments
  | equal left right =>
      simp only [
        Numbered.quote_hilbert_tokens_with?,
        quote_hilbert_token_tree_with?]
      rw [
        quote_term_tokens_with?_eq_token_tree,
        quote_term_tokens_with?_eq_token_tree]
      cases hLeft :
          quote_term_token_tree_with?
            freeNaming boundNames left <;>
        cases hRight :
          quote_term_token_tree_with?
            freeNaming boundNames right <;>
        simp [RawHilbertTokenTree.tokens,
          Numbered.equality_tokens,
          List.append_assoc]
  | neg body ih =>
      simp only [
        Numbered.quote_hilbert_tokens_with?,
        quote_hilbert_token_tree_with?]
      rw [ih]
      cases hBody :
          quote_hilbert_token_tree_with?
            freeNaming binderNaming
            boundNames depth body <;>
        simp [RawHilbertTokenTree.tokens,
          Numbered.negation_tokens]
  | conj left right =>
      rfl
  | disj left right =>
      rfl
  | imp left right ihLeft ihRight =>
      simp only [
        Numbered.quote_hilbert_tokens_with?,
        quote_hilbert_token_tree_with?]
      rw [ihLeft, ihRight]
      cases hLeft :
          quote_hilbert_token_tree_with?
            freeNaming binderNaming
            boundNames depth left <;>
        cases hRight :
          quote_hilbert_token_tree_with?
            freeNaming binderNaming
            boundNames depth right <;>
        simp [RawHilbertTokenTree.tokens,
          Numbered.implication_tokens,
          List.append_assoc]
  | iff left right =>
      rfl
  | forallE sort body ih =>
      simp only [
        Numbered.quote_hilbert_tokens_with?,
        quote_hilbert_token_tree_with?]
      rw [ih]
      cases hBody :
          quote_hilbert_token_tree_with?
            freeNaming binderNaming (binderNaming depth :: boundNames) (depth + 1) body <;>
        simp [RawHilbertTokenTree.tokens,
          Numbered.universal_tokens]
  | existsE sort body =>
      rfl
/-! ## 规范 quotation 树的符号反演 -/
/-- 同一底数大于一时，自然数幂对指数单射。 -/
private theorem raw_power_exponent_injective
    {base left right : Nat} (hBase : 1 < base) (hEqual : base ^ left = base ^ right) :
    left = right := by
  have hLeftLe : left ≤ right := (Nat.pow_le_pow_iff_right hBase).mp (Nat.le_of_eq hEqual)
  have hRightLe : right ≤ left := (Nat.pow_le_pow_iff_right hBase).mp (Nat.le_of_eq hEqual.symm)
  exact Nat.le_antisymm hLeftLe hRightLe
/--
互素底数的正幂乘积唯一决定两边指数。
函数符号码 `3^a * 5^i` 与谓词符号码 `3^a * 7^i` 都通过这一条公共算术核反演。
-/
private theorem raw_coprime_power_product_injective
    {firstBase secondBase
      leftFirst leftSecond rightFirst rightSecond : Nat} (hFirstBase : 1 < firstBase) (hSecondBase : 1 < secondBase)
    (hCoprime : Nat.Coprime firstBase secondBase) (hEqual :
      firstBase ^ leftFirst * secondBase ^ leftSecond =
        firstBase ^ rightFirst * secondBase ^ rightSecond) :
    leftFirst = rightFirst ∧
      leftSecond = rightSecond := by
  have hLeftSecondDiv :
      secondBase ^ leftSecond ∣
        firstBase ^ rightFirst *
          secondBase ^ rightSecond := by
    refine ⟨firstBase ^ leftFirst, ?_⟩
    simpa [Nat.mul_comm] using hEqual.symm
  have hLeftSecondDivPower :
      secondBase ^ leftSecond ∣
        secondBase ^ rightSecond := (Nat.Coprime.pow
      leftSecond rightFirst hCoprime.symm).dvd_of_dvd_mul_left
        hLeftSecondDiv
  have hLeftSecondLe :
      leftSecond ≤ rightSecond := (Nat.pow_dvd_pow_iff_le_right hSecondBase).mp
      hLeftSecondDivPower
  have hRightSecondDiv :
      secondBase ^ rightSecond ∣
        firstBase ^ leftFirst *
          secondBase ^ leftSecond := by
    refine ⟨firstBase ^ rightFirst, ?_⟩
    simpa [Nat.mul_comm] using hEqual
  have hRightSecondDivPower :
      secondBase ^ rightSecond ∣
        secondBase ^ leftSecond := (Nat.Coprime.pow
      rightSecond leftFirst hCoprime.symm).dvd_of_dvd_mul_left
        hRightSecondDiv
  have hRightSecondLe :
      rightSecond ≤ leftSecond := (Nat.pow_dvd_pow_iff_le_right hSecondBase).mp
      hRightSecondDivPower
  have hSecond : leftSecond = rightSecond :=
    Nat.le_antisymm hLeftSecondLe hRightSecondLe
  subst rightSecond
  have hFirstPowers :
      firstBase ^ leftFirst =
        firstBase ^ rightFirst :=
    Nat.mul_right_cancel (Nat.pow_pos (by omega))
      hEqual
  exact
    ⟨raw_power_exponent_injective
        hFirstBase hFirstPowers,
      rfl⟩
/-- 变量 token 唯一决定变量名字。 -/
theorem token_reflection_variable_token_injective :
    Function.Injective Numbered.variable_token := by
  intro left right hEqual
  exact
    Nat.add_right_cancel (raw_power_exponent_injective (base := 3) (by omega) hEqual)
/-- 常元 token 唯一决定函数符号编号。 -/
theorem token_reflection_constant_token_injective :
    Function.Injective Numbered.constant_token := by
  intro left right hEqual
  exact
    Nat.add_right_cancel (raw_power_exponent_injective (base := 5) (by omega) hEqual)
/-- 常元 token 与变量 token 不相交。 -/
theorem token_reflection_constant_token_ne_variable_token
    (index name : Nat) :
    Numbered.constant_token index ≠
      Numbered.variable_token name := by
  intro hEqual
  have hCoprime :
      Nat.Coprime (5 ^ (index + 1)) (3 ^ (name + 1)) :=
    Nat.Coprime.pow (index + 1) (name + 1) (by decide)
  have hDiv :
      5 ^ (index + 1) ∣
        3 ^ (name + 1) := by
    exact
      ⟨1, by
        simpa [Numbered.constant_token,
          Numbered.variable_token]
          using hEqual.symm⟩
  have hOne := hCoprime.eq_one_of_dvd hDiv
  simp at hOne
/-- 正元函数 token 唯一决定元数前驱与函数符号编号。 -/
theorem token_reflection_function_token_injective
    {leftArity leftIndex rightArity rightIndex : Nat} (hEqual :
      Numbered.function_token leftArity leftIndex =
        Numbered.function_token rightArity rightIndex) :
    leftArity = rightArity ∧
      leftIndex = rightIndex := by
  rcases
      raw_coprime_power_product_injective (firstBase := 3) (secondBase := 5) (by omega) (by omega) (by decide)
        hEqual with
    ⟨hArity, hIndex⟩
  exact
    ⟨Nat.add_right_cancel hArity,
      Nat.add_right_cancel hIndex⟩
/-- 正元谓词 token 唯一决定元数前驱与关系符号编号。 -/
theorem token_reflection_predicate_token_injective
    {leftArity leftIndex rightArity rightIndex : Nat} (hEqual :
      Numbered.predicate_token leftArity leftIndex =
        Numbered.predicate_token rightArity rightIndex) :
    leftArity = rightArity ∧
      leftIndex = rightIndex := by
  rcases
      raw_coprime_power_product_injective (firstBase := 3) (secondBase := 7) (by omega) (by omega) (by decide)
        hEqual with
    ⟨hArity, hIndex⟩
  exact
    ⟨Nat.add_right_cancel hArity,
      Nat.add_right_cancel hIndex⟩

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
