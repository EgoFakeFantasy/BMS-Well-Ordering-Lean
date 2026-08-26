import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.Numbered
/-!
# 可编号单排序签名上的公共 token 反射
本模块为通用 Gödel quotation 建立可逆的 token 语法。函数项与普通谓词都采用
“奇数首部—左括号—参数列—右括号”的自定界结构；全括号 Hilbert 公式则由逻辑
token 唯一分隔。因此反射过程不需要枚举具体签名，也不依赖文献中的有限符号界限。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace GodelQuotation
set_option autoImplicit false
open Nonlogical.BasicSetTheory
/-! ## 原始项 token 树 -/
/-- 忘掉具体符号后保留的项 token 树。 -/
inductive RawTermTokenTree where
  | atom (head : Nat)
  | application (head : Nat) (arguments : List RawTermTokenTree)
namespace RawTermTokenTree
mutual
  /-- 原始项树的规范序列化。 -/
  def tokens : RawTermTokenTree → List Nat
    | .atom head => [head]
    | .application head arguments =>
        [head, Numbered.logical_token .leftParenthesis] ++
          list_tokens arguments ++
            [Numbered.logical_token .rightParenthesis]
  /-- 一列原始项树的扁平 token 串。 -/
  def list_tokens : List RawTermTokenTree → List Nat
    | [] => []
    | tree :: trees =>
        tree.tokens ++ list_tokens trees
end
@[simp]
theorem map_tokens_flatten_eq_list_tokens (trees : List RawTermTokenTree) : (trees.map tokens).flatten =
      list_tokens trees := by
  induction trees with
  | nil =>
      rfl
  | cons tree trees ih =>
      simp [list_tokens, ih]
mutual
  /-- 项 parser 消费一棵树所需的递归高度。 -/
  def height : RawTermTokenTree → Nat
    | .atom _ => 0
    | .application _ arguments =>
        list_height arguments + 1
  /-- 参数列 parser 所需的递归高度。 -/
  def list_height : List RawTermTokenTree → Nat
    | [] => 0
    | tree :: trees =>
        max tree.height (list_height trees) + 1
end
/-- quotation 的所有非逻辑首部都是奇数。 -/
def HeadsOdd : RawTermTokenTree → Prop
  | .atom head =>
      head % 2 = 1
  | .application head arguments =>
      head % 2 = 1 ∧
        ∀ tree, tree ∈ arguments → tree.HeadsOdd
/-- 一列原始项树逐项满足首部奇性。 -/
def ListHeadsOdd (trees : List RawTermTokenTree) : Prop :=
  ∀ tree, tree ∈ trees → tree.HeadsOdd
/-- 每棵项树的序列化都以其奇数首部开始。 -/
theorem tokens_eq_head_cons
    {tree : RawTermTokenTree} (hOdd : tree.HeadsOdd) :
    ∃ head tail,
      head % 2 = 1 ∧
        tree.tokens = head :: tail := by
  cases tree with
  | atom head =>
      have hHeadOdd : head % 2 = 1 := by
        simpa [HeadsOdd] using hOdd
      exact
        ⟨head, ([] : List Nat), hHeadOdd, rfl⟩
  | application head arguments =>
      have hApplicationOdd :
          head % 2 = 1 ∧
            ∀ tree, tree ∈ arguments →
              tree.HeadsOdd := by
        simpa [HeadsOdd] using hOdd
      have hHeadOdd : head % 2 = 1 := by
        exact hApplicationOdd.1
      exact
        ⟨head,
          Numbered.logical_token .leftParenthesis :: (list_tokens arguments ++
              [Numbered.logical_token .rightParenthesis]),
          hHeadOdd, rfl⟩
end RawTermTokenTree
theorem odd_token_ne_logical
    {token : Nat} (hOdd : token % 2 = 1) (symbol : LogicalSymbolKind) :
    token ≠ Numbered.logical_token symbol := by
  intro hEqual
  have hEven :
      Numbered.logical_token symbol % 2 = 0 := by
    cases symbol <;> native_decide
  rw [hEqual, hEven] at hOdd
  omega
private theorem logical_left_ne_right :
    Numbered.logical_token .leftParenthesis ≠
      Numbered.logical_token .rightParenthesis := by
  native_decide
private theorem logical_equality_ne_left :
    Numbered.logical_token .equality ≠
      Numbered.logical_token .leftParenthesis := by
  native_decide
private theorem membership_ne_logical_left :
    Numbered.membership_token ≠
      Numbered.logical_token .leftParenthesis := by
  native_decide
private theorem logical_implication_ne_left :
    Numbered.logical_token .implication ≠
      Numbered.logical_token .leftParenthesis := by
  native_decide
private theorem membership_ne_logical_equality :
    Numbered.membership_token ≠
      Numbered.logical_token .equality := by
  native_decide
private theorem logical_implication_ne_equality :
    Numbered.logical_token .implication ≠
      Numbered.logical_token .equality := by
  native_decide
private theorem logical_implication_ne_membership :
    Numbered.logical_token .implication ≠
      Numbered.membership_token := by
  native_decide
/-- 项结束后的后缀不能立即以左括号开始。 -/
def TermSuffixSeparated : List Nat → Prop
  | [] => True
  | head :: _ =>
      head ≠ Numbered.logical_token .leftParenthesis
private theorem raw_term_list_suffix_separated (trees : List RawTermTokenTree) (hOdd : RawTermTokenTree.ListHeadsOdd trees) (suffix : List Nat) :
    TermSuffixSeparated (RawTermTokenTree.list_tokens trees ++ (Numbered.logical_token .rightParenthesis ::
          suffix)) := by
  cases trees with
  | nil =>
      exact logical_left_ne_right.symm
  | cons tree trees =>
      have hTreeOdd : tree.HeadsOdd :=
        hOdd tree (by simp)
      rcases tree.tokens_eq_head_cons hTreeOdd with
        ⟨head, tail, hHeadOdd, hTokens⟩
      rw [RawTermTokenTree.list_tokens, hTokens]
      exact
        odd_token_ne_logical hHeadOdd
          .leftParenthesis
/-! ## 项与参数列 parser -/
mutual
  /-- 从输入前缀消费一棵原始项树。 -/
  private def parse_raw_term_tokens :
      Nat → List Nat →
        Option (RawTermTokenTree × List Nat)
    | 0, _ => none
    | fuel + 1, input =>
        match input with
        | [] => none
        | head :: rest =>
            match rest with
            | leftParenthesis :: body =>
                if leftParenthesis =
                    Numbered.logical_token .leftParenthesis then
                  do
                    let (arguments, suffix) ←
                      parse_raw_term_list_tokens fuel body
                    some (.application head arguments, suffix)
                else
                  some (.atom head, rest)
            | _ =>
                some (.atom head, rest)
  /-- 从输入前缀消费一列以右括号终止的原始项树。 -/
  private def parse_raw_term_list_tokens :
      Nat → List Nat →
        Option (List RawTermTokenTree × List Nat)
    | 0, _ => none
    | fuel + 1, input =>
        match input with
        | [] => none
        | head :: tail =>
            if head =
                Numbered.logical_token .rightParenthesis then
              some (([] : List RawTermTokenTree), tail)
            else
              do
                let (tree, afterTree) ←
                  parse_raw_term_tokens fuel input
                let (trees, suffix) ←
                  parse_raw_term_list_tokens fuel afterTree
                some (tree :: trees, suffix)
end
/--
项树及参数列序列化与 parser 同时互逆。
参数列使用右括号作为唯一终止符；奇数首部保证它不会与任何括号或逻辑分隔符
混淆。
-/
private theorem parse_raw_term_tokens_correct (fuel : Nat) : (∀ (tree : RawTermTokenTree),
      tree.HeadsOdd →
        ∀ (suffix : List Nat),
          TermSuffixSeparated suffix →
            tree.height < fuel →
              parse_raw_term_tokens fuel (tree.tokens ++ suffix) =
                some (tree, suffix)) ∧ (∀ (trees : List RawTermTokenTree),
      RawTermTokenTree.ListHeadsOdd trees →
        ∀ (suffix : List Nat),
          RawTermTokenTree.list_height trees < fuel →
            parse_raw_term_list_tokens fuel (RawTermTokenTree.list_tokens trees ++ (Numbered.logical_token
                      .rightParenthesis ::
                    suffix)) =
              some (trees, suffix)) := by
  induction fuel with
  | zero =>
      constructor
      · intro tree hOdd suffix hSuffix hFuel
        omega
      · intro trees hOdd suffix hFuel
        omega
  | succ fuel ih =>
      constructor
      · intro tree hOdd suffix hSuffix hFuel
        cases tree with
        | atom head =>
            cases suffix with
            | nil =>
                simp [RawTermTokenTree.tokens,
                  parse_raw_term_tokens]
            | cons suffixHead suffixTail =>
                simp only [TermSuffixSeparated] at hSuffix
                by_cases hLeft :
                    suffixHead =
                      Numbered.logical_token
                        .leftParenthesis
                · exact False.elim (hSuffix hLeft)
                · simp [RawTermTokenTree.tokens,
                    parse_raw_term_tokens, hLeft]
        | application head arguments =>
            have hApplicationOdd :
                head % 2 = 1 ∧
                  RawTermTokenTree.ListHeadsOdd
                    arguments := by
              simpa [RawTermTokenTree.HeadsOdd,
                RawTermTokenTree.ListHeadsOdd]
                using hOdd
            have hArgumentsFuel :
                RawTermTokenTree.list_height
                    arguments <
                  fuel := by
              simpa [RawTermTokenTree.height] using hFuel
            have hArgumentsOdd :
                RawTermTokenTree.ListHeadsOdd
                  arguments :=
              hApplicationOdd.2
            have hArgumentsParse :=
              ih.2 arguments hArgumentsOdd
                suffix hArgumentsFuel
            simp [RawTermTokenTree.tokens,
              parse_raw_term_tokens,
              List.append_assoc, hArgumentsParse]
      · intro trees hOdd suffix hFuel
        cases trees with
        | nil =>
            simp [RawTermTokenTree.list_tokens,
              parse_raw_term_list_tokens]
        | cons tree trees =>
            have hTreeOdd : tree.HeadsOdd :=
              hOdd tree (by simp)
            have hTreesOdd :
                RawTermTokenTree.ListHeadsOdd trees := by
              intro candidate hCandidate
              exact hOdd candidate (by simp [hCandidate])
            have hTreeFuel :
                tree.height < fuel := by
              simp [RawTermTokenTree.list_height] at hFuel
              omega
            have hTreesFuel :
                RawTermTokenTree.list_height
                    trees <
                  fuel := by
              simp [RawTermTokenTree.list_height] at hFuel
              omega
            have hSuffixSeparated :
                TermSuffixSeparated (RawTermTokenTree.list_tokens trees ++ (Numbered.logical_token
                        .rightParenthesis ::
                      suffix)) :=
              raw_term_list_suffix_separated
                trees hTreesOdd suffix
            have hTreeParse :=
              ih.1 tree hTreeOdd (RawTermTokenTree.list_tokens trees ++ (Numbered.logical_token
                      .rightParenthesis ::
                    suffix))
                hSuffixSeparated hTreeFuel
            have hTreesParse :=
              ih.2 trees hTreesOdd suffix hTreesFuel
            rcases tree.tokens_eq_head_cons hTreeOdd with
              ⟨head, tail, hHeadOdd, hTreeTokens⟩
            have hHeadNeRight :
                head ≠
                  Numbered.logical_token
                    .rightParenthesis :=
              odd_token_ne_logical hHeadOdd
                .rightParenthesis
            have hTreeParse' :
                parse_raw_term_tokens fuel (head :: (tail ++ (RawTermTokenTree.list_tokens
                            trees ++ (Numbered.logical_token
                              .rightParenthesis ::
                            suffix)))) =
                  some (tree,
                      RawTermTokenTree.list_tokens
                          trees ++ (Numbered.logical_token
                            .rightParenthesis ::
                          suffix)) := by
              simpa [hTreeTokens, List.append_assoc]
                using hTreeParse
            simp [RawTermTokenTree.list_tokens,
              hTreeTokens, List.append_assoc,
              parse_raw_term_list_tokens,
              hHeadNeRight, hTreeParse',
              hTreesParse]
/--
项与参数列 parser 的成功结果精确覆盖其已消费输入。
该方向不需要奇偶词法前提：parser 返回的树按定义重新序列化后，必与原输入的已消费
前缀逐 token 相同。
-/
private theorem parse_raw_term_tokens_sound (fuel : Nat) : (∀ (input : List Nat) (tree : RawTermTokenTree) (suffix : List Nat),
      parse_raw_term_tokens fuel input =
          some (tree, suffix) →
        input = tree.tokens ++ suffix) ∧ (∀ (input : List Nat) (trees : List RawTermTokenTree) (suffix : List Nat),
      parse_raw_term_list_tokens fuel input =
          some (trees, suffix) →
        input =
          RawTermTokenTree.list_tokens trees ++ (Numbered.logical_token .rightParenthesis ::
              suffix)) := by
  induction fuel with
  | zero =>
      constructor
      · intro input tree suffix hParse
        simp [parse_raw_term_tokens] at hParse
      · intro input trees suffix hParse
        simp [parse_raw_term_list_tokens] at hParse
  | succ fuel ih =>
      constructor
      · intro input tree suffix hParse
        cases input with
        | nil =>
            simp [parse_raw_term_tokens] at hParse
        | cons head rest =>
            cases rest with
            | nil =>
                have hResult : (.atom head, ([] : List Nat)) = (tree, suffix) := by
                  simpa [parse_raw_term_tokens] using hParse
                cases hResult
                simp [RawTermTokenTree.tokens]
            | cons leftParenthesis body =>
                by_cases hLeft :
                    leftParenthesis =
                      Numbered.logical_token
                        .leftParenthesis
                · cases hArguments :
                    parse_raw_term_list_tokens fuel body with
                  | none =>
                      simp [parse_raw_term_tokens, hLeft,
                        hArguments] at hParse
                  | some result =>
                      rcases result with
                        ⟨arguments, afterArguments⟩
                      have hResult : (.application head arguments,
                              afterArguments) = (tree, suffix) := by
                        simpa [parse_raw_term_tokens, hLeft,
                          hArguments] using hParse
                      have hTreeEquality :
                          tree =
                            .application head arguments := (congrArg Prod.fst hResult).symm
                      have hSuffixEquality :
                          suffix = afterArguments := (congrArg Prod.snd hResult).symm
                      subst tree
                      subst suffix
                      have hBody :=
                        ih.2 body arguments afterArguments
                          hArguments
                      simp [RawTermTokenTree.tokens, hLeft,
                        hBody, List.append_assoc]
                · have hResult : (.atom head,
                          leftParenthesis :: body) = (tree, suffix) := by
                    simpa [parse_raw_term_tokens, hLeft]
                      using hParse
                  cases hResult
                  simp [RawTermTokenTree.tokens]
      · intro input trees suffix hParse
        cases input with
        | nil =>
            simp [parse_raw_term_list_tokens] at hParse
        | cons head tail =>
            by_cases hRight :
                head =
                  Numbered.logical_token
                    .rightParenthesis
            · have hResult : (([] : List RawTermTokenTree), tail) = (trees, suffix) := by
                simpa [parse_raw_term_list_tokens, hRight]
                  using hParse
              cases hResult
              simp [RawTermTokenTree.list_tokens, hRight]
            · cases hTreeParse :
                parse_raw_term_tokens fuel (head :: tail) with
              | none =>
                  simp [parse_raw_term_list_tokens, hRight,
                    hTreeParse] at hParse
              | some treeResult =>
                  rcases treeResult with
                    ⟨tree, afterTree⟩
                  cases hTreesParse :
                      parse_raw_term_list_tokens fuel afterTree with
                  | none =>
                      simp [parse_raw_term_list_tokens, hRight,
                        hTreeParse, hTreesParse] at hParse
                  | some treesResult =>
                      rcases treesResult with
                        ⟨tailTrees, finalSuffix⟩
                      have hResult : (tree :: tailTrees, finalSuffix) = (trees, suffix) := by
                        simpa [parse_raw_term_list_tokens, hRight,
                          hTreeParse, hTreesParse] using hParse
                      have hTreesEquality :
                          trees = tree :: tailTrees := (congrArg Prod.fst hResult).symm
                      have hSuffixEquality :
                          suffix = finalSuffix := (congrArg Prod.snd hResult).symm
                      subst trees
                      subst suffix
                      have hInput :=
                        ih.1 (head :: tail) tree afterTree
                          hTreeParse
                      have hAfter :=
                        ih.2 afterTree tailTrees finalSuffix
                          hTreesParse
                      rw [hInput, hAfter]
                      simp [RawTermTokenTree.list_tokens,
                        List.append_assoc]
mutual
  /-- 单棵项树的递归高度严格小于其规范 token 串长度。 -/
  theorem RawTermTokenTree.height_lt_tokens_length (tree : RawTermTokenTree) :
      tree.height < tree.tokens.length := by
    cases tree with
    | atom head =>
        simp [RawTermTokenTree.height,
          RawTermTokenTree.tokens]
    | application head arguments =>
        have hArguments :=
          RawTermTokenTree.list_height_le_list_tokens_length
            arguments
        simp [RawTermTokenTree.height,
          RawTermTokenTree.tokens] at *
        omega
  /-- 项列表的递归高度不超过其扁平 token 串长度。 -/
  theorem RawTermTokenTree.list_height_le_list_tokens_length (trees : List RawTermTokenTree) :
      RawTermTokenTree.list_height trees ≤ (RawTermTokenTree.list_tokens trees).length := by
    cases trees with
    | nil =>
        simp [RawTermTokenTree.list_height,
          RawTermTokenTree.list_tokens]
    | cons tree trees =>
        have hTree :=
          RawTermTokenTree.height_lt_tokens_length tree
        have hTrees :=
          RawTermTokenTree.list_height_le_list_tokens_length
            trees
        simp [RawTermTokenTree.list_height,
          RawTermTokenTree.list_tokens] at *
        omega
end
namespace RawTermTokenTree
/-- 完整消费输入 token 串的公开项解析器。 -/
def parse? (input : List Nat) : Option RawTermTokenTree :=
  match parse_raw_term_tokens (input.length + 1) input with
  | some (tree, []) => some tree
  | _ => none

/-- 公开项 parser 成功时，返回树的规范 token 串恰好是完整输入。 -/
theorem parse?_sound
    {input : List Nat} {tree : RawTermTokenTree}
    (hParse : parse? input = some tree) :
    tree.tokens = input := by
  unfold parse? at hParse
  cases hRaw :
      parse_raw_term_tokens (input.length + 1) input with
  | none =>
      simp [hRaw] at hParse
  | some result =>
      rcases result with ⟨parsed, suffix⟩
      cases suffix with
      | nil =>
          have hTree : parsed = tree := by
            simpa [hRaw] using hParse
          subst parsed
          have hSound :=
            (parse_raw_term_tokens_sound
              (input.length + 1)).1 input tree [] hRaw
          simpa using hSound.symm
      | cons head tail =>
          simp [hRaw] at hParse

/-- 词法分离的规范项树序列化可被公开 parser 精确恢复。 -/
@[simp] theorem parse?_tokens
    (tree : RawTermTokenTree)
    (hOdd : tree.HeadsOdd) :
    parse? tree.tokens = some tree := by
  have hFuel :
      tree.height < tree.tokens.length + 1 := by
    exact Nat.lt_succ_of_lt
      tree.height_lt_tokens_length
  have hParse :
    parse_raw_term_tokens
          (tree.tokens.length + 1) tree.tokens =
        some (tree, []) := by
    simpa using
      (parse_raw_term_tokens_correct
        (tree.tokens.length + 1)).1
        tree hOdd []
        (by simp [TermSuffixSeparated])
        hFuel
  simp [parse?, hParse]
end RawTermTokenTree
/-! ## 原始 Hilbert token 树 -/
/-- 忘掉具体签名后保留的 Hilbert 核 token 树。 -/
inductive RawHilbertTokenTree where
  | equality (left right : RawTermTokenTree)
  | membership (left right : RawTermTokenTree)
  | predicate (head : Nat) (arguments : List RawTermTokenTree)
  | negation (body : RawHilbertTokenTree)
  | implication (left right : RawHilbertTokenTree)
  | universal (variableToken : Nat) (body : RawHilbertTokenTree)
namespace RawHilbertTokenTree
/-- 原始 Hilbert 树的规范全括号序列化。 -/
def tokens : RawHilbertTokenTree → List Nat
  | .equality left right =>
      [Numbered.logical_token .leftParenthesis] ++
        left.tokens ++
          [Numbered.logical_token .equality] ++
            right.tokens ++
              [Numbered.logical_token .rightParenthesis]
  | .membership left right =>
      [Numbered.logical_token .leftParenthesis] ++
        left.tokens ++
          [Numbered.membership_token] ++
            right.tokens ++
              [Numbered.logical_token .rightParenthesis]
  | .predicate head arguments =>
      [head, Numbered.logical_token .leftParenthesis] ++
        RawTermTokenTree.list_tokens arguments ++
          [Numbered.logical_token .rightParenthesis]
  | .negation body =>
      [Numbered.logical_token .leftParenthesis,
        Numbered.logical_token .negation] ++
          body.tokens ++
            [Numbered.logical_token .rightParenthesis]
  | .implication left right =>
      [Numbered.logical_token .leftParenthesis] ++
        left.tokens ++
          [Numbered.logical_token .implication] ++
            right.tokens ++
              [Numbered.logical_token .rightParenthesis]
  | .universal variableToken body =>
      [Numbered.logical_token .leftParenthesis,
        Numbered.logical_token .universal,
        variableToken] ++
          body.tokens ++
            [Numbered.logical_token .rightParenthesis]
/-- 公式 parser 消费一棵 Hilbert 树所需的递归高度。 -/
def height : RawHilbertTokenTree → Nat
  | .equality left right =>
      max left.height right.height + 1
  | .membership left right =>
      max left.height right.height + 1
  | .predicate _ arguments =>
      RawTermTokenTree.list_height arguments + 1
  | .negation body =>
      body.height + 1
  | .implication left right =>
      max left.height right.height + 1
  | .universal _ body =>
      body.height + 1
/-- parser 所需的唯一词法条件。 -/
def LexicallySeparated : RawHilbertTokenTree → Prop
  | .equality left right =>
      left.HeadsOdd ∧ right.HeadsOdd
  | .membership left right =>
      left.HeadsOdd ∧ right.HeadsOdd
  | .predicate head arguments =>
      head % 2 = 1 ∧
        RawTermTokenTree.ListHeadsOdd arguments
  | .negation body =>
      body.LexicallySeparated
  | .implication left right =>
      left.LexicallySeparated ∧
        right.LexicallySeparated
  | .universal _ body =>
      body.LexicallySeparated
end RawHilbertTokenTree
/-! ## Hilbert parser -/
/-- 从已消费的左式之后完成蕴含式解析。 -/
private def parse_raw_implication_tail (parseFormula :
      List Nat →
        Option (RawHilbertTokenTree × List Nat)) (left : RawHilbertTokenTree) (input : List Nat) :
    Option (RawHilbertTokenTree × List Nat) :=
  match input with
  | implication :: rightInput =>
      if implication =
          Numbered.logical_token .implication then
        do
          let (right, afterRight) ←
            parseFormula rightInput
          match afterRight with
          | rightParenthesis :: suffix =>
              if rightParenthesis =
                  Numbered.logical_token
                    .rightParenthesis then
                some (.implication left right, suffix)
              else
                none
          | _ => none
      else
        none
  | _ => none
/-- 从已消费的左项之后完成等式、隶属式或谓词左式蕴含的解析。 -/
private def parse_raw_atomic_or_predicate_implication_tail (parseTerm :
      List Nat →
        Option (RawTermTokenTree × List Nat)) (parseFormula :
      List Nat →
        Option (RawHilbertTokenTree × List Nat)) (left : RawTermTokenTree) (input : List Nat) :
    Option (RawHilbertTokenTree × List Nat) :=
  match input with
  | operator :: rightInput =>
      if operator =
          Numbered.logical_token .equality then
        do
          let (right, afterRight) ←
            parseTerm rightInput
          match afterRight with
          | rightParenthesis :: suffix =>
              if rightParenthesis =
                  Numbered.logical_token
                    .rightParenthesis then
                some (.equality left right, suffix)
              else
                none
          | _ => none
      else if operator =
          Numbered.membership_token then
        do
          let (right, afterRight) ←
            parseTerm rightInput
          match afterRight with
          | rightParenthesis :: suffix =>
              if rightParenthesis =
                  Numbered.logical_token
                    .rightParenthesis then
                some (.membership left right, suffix)
              else
                none
          | _ => none
      else if operator =
          Numbered.logical_token .implication then
        match left with
        | .atom _ => none
        | .application head arguments =>
            do
              let (right, afterRight) ←
                parseFormula rightInput
              match afterRight with
              | rightParenthesis :: suffix =>
                  if rightParenthesis =
                      Numbered.logical_token
                        .rightParenthesis then
                    some (.implication (.predicate head arguments)
                        right,
                        suffix)
                  else
                    none
              | _ => none
      else
        none
  | _ => none
/-- 从输入前缀消费一棵原始 Hilbert token 树。 -/
private def parse_raw_hilbert_tokens :
    Nat → List Nat →
      Option (RawHilbertTokenTree × List Nat)
  | 0, _ => none
  | fuel + 1, input =>
      match input with
      | [] => none
      | first :: rest =>
          if first =
              Numbered.logical_token .leftParenthesis then
            match rest with
            | [] => none
            | head :: tail =>
                if head =
                    Numbered.logical_token .negation then
                  do
                    let (body, afterBody) ←
                      parse_raw_hilbert_tokens fuel tail
                    match afterBody with
                    | rightParenthesis :: suffix =>
                        if rightParenthesis =
                            Numbered.logical_token
                              .rightParenthesis then
                          some (.negation body, suffix)
                        else
                          none
                    | _ => none
                else if head =
                    Numbered.logical_token .universal then
                  match tail with
                  | variableToken :: bodyInput =>
                      do
                        let (body, afterBody) ←
                          parse_raw_hilbert_tokens fuel
                            bodyInput
                        match afterBody with
                        | rightParenthesis :: suffix =>
                            if rightParenthesis =
                                Numbered.logical_token
                                  .rightParenthesis then
                              some (.universal
                                  variableToken body,
                                  suffix)
                            else
                              none
                        | _ => none
                  | _ => none
                else if head =
                    Numbered.logical_token
                      .leftParenthesis then
                  do
                    let (left, afterLeft) ←
                      parse_raw_hilbert_tokens fuel (head :: tail)
                    parse_raw_implication_tail (parse_raw_hilbert_tokens fuel)
                      left afterLeft
                else
                  do
                    let (left, afterLeft) ←
                      parse_raw_term_tokens fuel (head :: tail)
                    parse_raw_atomic_or_predicate_implication_tail (parse_raw_term_tokens fuel) (parse_raw_hilbert_tokens fuel)
                      left afterLeft
          else
            match rest with
            | leftParenthesis :: body =>
                if leftParenthesis =
                    Numbered.logical_token
                      .leftParenthesis then
                  do
                    let (arguments, suffix) ←
                      parse_raw_term_list_tokens fuel body
                    some (.predicate first arguments, suffix)
                else
                  none
            | _ => none
/--
蕴含尾部 parser 成功时，输入恰由蕴含符号、右公式 token、右括号和剩余后缀组成。
-/
private theorem parse_raw_implication_tail_sound (parseFormula :
      List Nat →
        Option (RawHilbertTokenTree × List Nat)) (hFormulaSound :
      ∀ input tree suffix,
        parseFormula input = some (tree, suffix) →
          input = tree.tokens ++ suffix) (left tree : RawHilbertTokenTree) (input suffix : List Nat) (hParse :
      parse_raw_implication_tail parseFormula left input =
        some (tree, suffix)) :
    ∃ right : RawHilbertTokenTree,
      tree = .implication left right ∧
        input =
          Numbered.logical_token .implication :: (right.tokens ++
              Numbered.logical_token .rightParenthesis ::
                suffix) := by
  cases input with
  | nil =>
      simp [parse_raw_implication_tail] at hParse
  | cons implication rightInput =>
      by_cases hImplication :
          implication =
            Numbered.logical_token .implication
      · cases hRightParse : parseFormula rightInput with
        | none =>
            simp [parse_raw_implication_tail,
              hImplication, hRightParse] at hParse
        | some rightResult =>
            rcases rightResult with ⟨right, afterRight⟩
            cases afterRight with
            | nil =>
                simp [parse_raw_implication_tail,
                  hImplication, hRightParse] at hParse
            | cons rightParenthesis finalSuffix =>
                by_cases hRightParenthesis :
                    rightParenthesis =
                      Numbered.logical_token
                        .rightParenthesis
                · have hResult : (.implication left right, finalSuffix) = (tree, suffix) := by
                    simpa [parse_raw_implication_tail,
                      hImplication, hRightParse,
                      hRightParenthesis] using hParse
                  have hTree :
                      tree = .implication left right := (congrArg Prod.fst hResult).symm
                  have hSuffix :
                      suffix = finalSuffix := (congrArg Prod.snd hResult).symm
                  subst tree
                  subst suffix
                  have hRightTokens :=
                    hFormulaSound rightInput right (rightParenthesis :: finalSuffix)
                      hRightParse
                  refine ⟨right, rfl, ?_⟩
                  simp [hImplication, hRightParenthesis,
                    hRightTokens]
                · simp [parse_raw_implication_tail,
                    hImplication, hRightParse,
                    hRightParenthesis] at hParse
      · simp [parse_raw_implication_tail,
          hImplication] at hParse
/--
原子公式或谓词左式蕴含尾部 parser 的成功结果精确给出其三种可能构造。
-/
private theorem
    parse_raw_atomic_or_predicate_implication_tail_sound (parseTerm :
      List Nat →
        Option (RawTermTokenTree × List Nat)) (parseFormula :
      List Nat →
        Option (RawHilbertTokenTree × List Nat)) (hTermSound :
      ∀ input tree suffix,
        parseTerm input = some (tree, suffix) →
          input = tree.tokens ++ suffix) (hFormulaSound :
      ∀ input tree suffix,
        parseFormula input = some (tree, suffix) →
          input = tree.tokens ++ suffix) (left : RawTermTokenTree) (tree : RawHilbertTokenTree) (input suffix : List Nat) (hParse :
      parse_raw_atomic_or_predicate_implication_tail
          parseTerm parseFormula left input =
        some (tree, suffix)) : (∃ right : RawTermTokenTree,
      tree = .equality left right ∧
        input =
          Numbered.logical_token .equality :: (right.tokens ++
              Numbered.logical_token .rightParenthesis ::
                suffix)) ∨ (∃ right : RawTermTokenTree,
      tree = .membership left right ∧
        input =
          Numbered.membership_token :: (right.tokens ++
              Numbered.logical_token .rightParenthesis ::
                suffix)) ∨ (∃ head arguments right,
      left = .application head arguments ∧
        tree =
          .implication (.predicate head arguments) right ∧
        input =
          Numbered.logical_token .implication :: (right.tokens ++
              Numbered.logical_token .rightParenthesis ::
                suffix)) := by
  cases input with
  | nil =>
      simp [parse_raw_atomic_or_predicate_implication_tail]
        at hParse
  | cons operator rightInput =>
      by_cases hEquality :
          operator =
            Numbered.logical_token .equality
      · cases hRightParse : parseTerm rightInput with
        | none =>
            simp [parse_raw_atomic_or_predicate_implication_tail,
              hEquality, hRightParse] at hParse
        | some rightResult =>
            rcases rightResult with ⟨right, afterRight⟩
            cases afterRight with
            | nil =>
                simp [parse_raw_atomic_or_predicate_implication_tail,
                  hEquality, hRightParse] at hParse
            | cons rightParenthesis finalSuffix =>
                by_cases hRightParenthesis :
                    rightParenthesis =
                      Numbered.logical_token
                        .rightParenthesis
                · have hResult : (.equality left right, finalSuffix) = (tree, suffix) := by
                    simpa [
                      parse_raw_atomic_or_predicate_implication_tail,
                      hEquality, hRightParse,
                      hRightParenthesis] using hParse
                  have hTree :
                      tree = .equality left right := (congrArg Prod.fst hResult).symm
                  have hSuffix :
                      suffix = finalSuffix := (congrArg Prod.snd hResult).symm
                  subst tree
                  subst suffix
                  have hRightTokens :=
                    hTermSound rightInput right (rightParenthesis :: finalSuffix)
                      hRightParse
                  exact Or.inl
                    ⟨right, rfl, by
                      simp [hEquality, hRightParenthesis,
                        hRightTokens]⟩
                · simp [
                    parse_raw_atomic_or_predicate_implication_tail,
                    hEquality, hRightParse,
                    hRightParenthesis] at hParse
      · by_cases hMembership :
          operator = Numbered.membership_token
        · cases hRightParse : parseTerm rightInput with
          | none =>
              simp [
                parse_raw_atomic_or_predicate_implication_tail,
                hMembership,
                membership_ne_logical_equality,
                hRightParse] at hParse
          | some rightResult =>
              rcases rightResult with ⟨right, afterRight⟩
              cases afterRight with
              | nil =>
                  simp [
                    parse_raw_atomic_or_predicate_implication_tail,
                    hMembership,
                    membership_ne_logical_equality,
                    hRightParse] at hParse
              | cons rightParenthesis finalSuffix =>
                  by_cases hRightParenthesis :
                      rightParenthesis =
                        Numbered.logical_token
                          .rightParenthesis
                  · have hResult : (.membership left right, finalSuffix) = (tree, suffix) := by
                      simpa [
                        parse_raw_atomic_or_predicate_implication_tail,
                        hEquality, hMembership, hRightParse,
                        hRightParenthesis,
                        membership_ne_logical_equality]
                        using hParse
                    have hTree :
                        tree = .membership left right := (congrArg Prod.fst hResult).symm
                    have hSuffix :
                        suffix = finalSuffix := (congrArg Prod.snd hResult).symm
                    subst tree
                    subst suffix
                    have hRightTokens :=
                      hTermSound rightInput right (rightParenthesis :: finalSuffix)
                        hRightParse
                    exact Or.inr <| Or.inl
                      ⟨right, rfl, by
                        simp [hMembership, hRightParenthesis,
                          hRightTokens]⟩
                  · simp [
                      parse_raw_atomic_or_predicate_implication_tail,
                      hMembership, hRightParse,
                      hRightParenthesis,
                      membership_ne_logical_equality]
                      at hParse
        · by_cases hImplication :
            operator =
              Numbered.logical_token .implication
          · cases left with
            | atom head =>
                simp [
                  parse_raw_atomic_or_predicate_implication_tail,
                  hImplication,
                  logical_implication_ne_equality,
                  logical_implication_ne_membership] at hParse
            | application head arguments =>
                cases hRightParse :
                    parseFormula rightInput with
                | none =>
                    simp [
                      parse_raw_atomic_or_predicate_implication_tail,
                      hImplication,
                      logical_implication_ne_equality,
                      logical_implication_ne_membership,
                      hRightParse] at hParse
                | some rightResult =>
                    rcases rightResult with
                      ⟨right, afterRight⟩
                    cases afterRight with
                    | nil =>
                        simp [
                          parse_raw_atomic_or_predicate_implication_tail,
                          hImplication,
                          logical_implication_ne_equality,
                          logical_implication_ne_membership,
                          hRightParse] at hParse
                    | cons rightParenthesis finalSuffix =>
                        by_cases hRightParenthesis :
                            rightParenthesis =
                              Numbered.logical_token
                                .rightParenthesis
                        · have hResult : (.implication (.predicate head arguments)
                                  right,
                                finalSuffix) = (tree, suffix) := by
                            simpa [
                              parse_raw_atomic_or_predicate_implication_tail,
                              hEquality, hMembership, hImplication,
                              logical_implication_ne_equality,
                              logical_implication_ne_membership,
                              hRightParse, hRightParenthesis]
                              using hParse
                          have hTree :
                              tree =
                                .implication (.predicate head arguments)
                                  right := (congrArg Prod.fst hResult).symm
                          have hSuffix :
                              suffix = finalSuffix := (congrArg Prod.snd hResult).symm
                          subst tree
                          subst suffix
                          have hRightTokens :=
                            hFormulaSound rightInput right (rightParenthesis :: finalSuffix)
                              hRightParse
                          exact Or.inr <| Or.inr
                            ⟨head, arguments, right, rfl, rfl, by
                              simp [hImplication,
                                hRightParenthesis, hRightTokens]⟩
                        · simp [
                            parse_raw_atomic_or_predicate_implication_tail,
                            hImplication,
                            logical_implication_ne_equality,
                            logical_implication_ne_membership,
                            hRightParse, hRightParenthesis] at hParse
          · simp [
              parse_raw_atomic_or_predicate_implication_tail,
              hEquality, hMembership, hImplication] at hParse
private theorem logical_universal_ne_negation :
    Numbered.logical_token .universal ≠
      Numbered.logical_token .negation := by
  native_decide
private theorem logical_left_ne_negation :
    Numbered.logical_token .leftParenthesis ≠
      Numbered.logical_token .negation := by
  native_decide
private theorem logical_left_ne_universal :
    Numbered.logical_token .leftParenthesis ≠
      Numbered.logical_token .universal := by
  native_decide
/--
原始 Hilbert parser 的成功结果精确覆盖其已消费输入。
该方向只刻画 parser 自身的控制流，不需要公式树满足额外词法条件。
-/
private theorem parse_raw_hilbert_tokens_sound (fuel : Nat) :
    ∀ (input : List Nat) (tree : RawHilbertTokenTree) (suffix : List Nat),
      parse_raw_hilbert_tokens fuel input =
          some (tree, suffix) →
        input = tree.tokens ++ suffix := by
  induction fuel with
  | zero =>
      intro input tree suffix hParse
      simp [parse_raw_hilbert_tokens] at hParse
  | succ fuel ih =>
      intro input tree suffix hParse
      cases input with
      | nil =>
          simp [parse_raw_hilbert_tokens] at hParse
      | cons first rest =>
          by_cases hFirstLeft :
              first =
                Numbered.logical_token
                  .leftParenthesis
          · cases rest with
            | nil =>
                simp [parse_raw_hilbert_tokens,
                  hFirstLeft] at hParse
            | cons head tail =>
                by_cases hNegation :
                    head =
                      Numbered.logical_token .negation
                · cases hBodyParse :
                    parse_raw_hilbert_tokens fuel tail with
                  | none =>
                      simp [parse_raw_hilbert_tokens,
                        hFirstLeft, hNegation,
                        hBodyParse] at hParse
                  | some bodyResult =>
                      rcases bodyResult with
                        ⟨body, afterBody⟩
                      cases afterBody with
                      | nil =>
                          simp [parse_raw_hilbert_tokens,
                            hFirstLeft, hNegation,
                            hBodyParse] at hParse
                      | cons rightParenthesis finalSuffix =>
                          by_cases hRightParenthesis :
                              rightParenthesis =
                                Numbered.logical_token
                                  .rightParenthesis
                          · have hResult : (.negation body,
                                    finalSuffix) = (tree, suffix) := by
                              simpa [
                                parse_raw_hilbert_tokens,
                                hFirstLeft, hNegation,
                                hBodyParse,
                                hRightParenthesis]
                                using hParse
                            have hTree :
                                tree = .negation body := (congrArg Prod.fst hResult).symm
                            have hSuffix :
                                suffix = finalSuffix := (congrArg Prod.snd hResult).symm
                            subst tree
                            subst suffix
                            have hBodyTokens :=
                              ih tail body (rightParenthesis ::
                                  finalSuffix)
                                hBodyParse
                            simp [RawHilbertTokenTree.tokens,
                              hFirstLeft, hNegation,
                              hRightParenthesis, hBodyTokens,
                              List.append_assoc]
                          · simp [parse_raw_hilbert_tokens,
                              hFirstLeft, hNegation,
                              hBodyParse,
                              hRightParenthesis] at hParse
                · by_cases hUniversal :
                    head =
                      Numbered.logical_token .universal
                  · cases tail with
                    | nil =>
                        simp [parse_raw_hilbert_tokens,
                          hFirstLeft,
                          hUniversal,
                          logical_universal_ne_negation]
                          at hParse
                    | cons variableToken bodyInput =>
                        cases hBodyParse :
                            parse_raw_hilbert_tokens fuel
                              bodyInput with
                        | none =>
                            simp [parse_raw_hilbert_tokens,
                              hFirstLeft,
                              hUniversal,
                              logical_universal_ne_negation,
                              hBodyParse] at hParse
                        | some bodyResult =>
                            rcases bodyResult with
                              ⟨body, afterBody⟩
                            cases afterBody with
                            | nil =>
                                simp [parse_raw_hilbert_tokens,
                                  hFirstLeft,
                                  hUniversal,
                                  logical_universal_ne_negation,
                                  hBodyParse] at hParse
                            | cons rightParenthesis finalSuffix =>
                                by_cases hRightParenthesis :
                                    rightParenthesis =
                                      Numbered.logical_token
                                        .rightParenthesis
                                · have hResult : (.universal
                                          variableToken body,
                                          finalSuffix) = (tree, suffix) := by
                                    simpa [
                                      parse_raw_hilbert_tokens,
                                      hFirstLeft, hNegation,
                                      hUniversal,
                                      logical_universal_ne_negation,
                                      hBodyParse,
                                      hRightParenthesis]
                                      using hParse
                                  have hTree :
                                      tree =
                                        .universal
                                          variableToken body := (congrArg Prod.fst
                                      hResult).symm
                                  have hSuffix :
                                      suffix = finalSuffix := (congrArg Prod.snd
                                      hResult).symm
                                  subst tree
                                  subst suffix
                                  have hBodyTokens :=
                                    ih bodyInput body (rightParenthesis ::
                                        finalSuffix)
                                      hBodyParse
                                  simp [
                                    RawHilbertTokenTree.tokens,
                                    hFirstLeft, hUniversal,
                                    hRightParenthesis,
                                    hBodyTokens,
                                    List.append_assoc]
                                · simp [
                                    parse_raw_hilbert_tokens,
                                    hFirstLeft,
                                    hUniversal,
                                    logical_universal_ne_negation,
                                    hBodyParse,
                                    hRightParenthesis] at hParse
                  · by_cases hNestedLeft :
                      head =
                        Numbered.logical_token
                          .leftParenthesis
                    · cases hLeftParse :
                        parse_raw_hilbert_tokens fuel (head :: tail) with
                      | none =>
                          have hLeftParse' :
                              parse_raw_hilbert_tokens fuel (Numbered.logical_token
                                      .leftParenthesis ::
                                    tail) =
                                none := by
                            simpa [hNestedLeft] using hLeftParse
                          simp [parse_raw_hilbert_tokens,
                            hFirstLeft, hNestedLeft,
                            logical_left_ne_negation,
                            logical_left_ne_universal,
                            hLeftParse'] at hParse
                      | some leftResult =>
                          rcases leftResult with
                            ⟨left, afterLeft⟩
                          have hLeftParse' :
                              parse_raw_hilbert_tokens fuel (Numbered.logical_token
                                      .leftParenthesis ::
                                    tail) =
                                some (left, afterLeft) := by
                            simpa [hNestedLeft] using hLeftParse
                          have hTailParse :
                              parse_raw_implication_tail (parse_raw_hilbert_tokens
                                    fuel)
                                  left afterLeft =
                                some (tree, suffix) := by
                            simpa [
                              parse_raw_hilbert_tokens,
                              hFirstLeft, hNegation,
                              hUniversal, hNestedLeft,
                              logical_left_ne_negation,
                              logical_left_ne_universal,
                              hLeftParse'] using hParse
                          have hLeftTokens :=
                            ih (head :: tail) left
                              afterLeft hLeftParse
                          rcases
                              parse_raw_implication_tail_sound (parse_raw_hilbert_tokens fuel)
                                ih left tree afterLeft suffix
                                hTailParse with
                            ⟨right, hTree, hAfterLeft⟩
                          subst tree
                          rw [hLeftTokens, hAfterLeft]
                          simp [RawHilbertTokenTree.tokens,
                            hFirstLeft, List.append_assoc]
                    · cases hLeftParse :
                        parse_raw_term_tokens fuel (head :: tail) with
                      | none =>
                          simp [parse_raw_hilbert_tokens,
                            hFirstLeft, hNegation,
                            hUniversal, hNestedLeft,
                            hLeftParse] at hParse
                      | some leftResult =>
                          rcases leftResult with
                            ⟨left, afterLeft⟩
                          have hTailParse :
                              parse_raw_atomic_or_predicate_implication_tail (parse_raw_term_tokens fuel) (parse_raw_hilbert_tokens
                                    fuel)
                                  left afterLeft =
                                some (tree, suffix) := by
                            simpa [
                              parse_raw_hilbert_tokens,
                              hFirstLeft, hNegation,
                              hUniversal, hNestedLeft,
                              hLeftParse] using hParse
                          have hLeftTokens := (parse_raw_term_tokens_sound fuel).1 (head :: tail) left
                              afterLeft hLeftParse
                          rcases
                              parse_raw_atomic_or_predicate_implication_tail_sound (parse_raw_term_tokens fuel) (parse_raw_hilbert_tokens fuel)
                                (parse_raw_term_tokens_sound
                                  fuel).1
                                ih left tree afterLeft suffix
                                hTailParse with
                            hEquality | hMembership |
                              hImplication
                          · rcases hEquality with
                              ⟨right, hTree, hAfterLeft⟩
                            subst tree
                            rw [hLeftTokens, hAfterLeft]
                            simp [RawHilbertTokenTree.tokens,
                              hFirstLeft, List.append_assoc]
                          · rcases hMembership with
                              ⟨right, hTree, hAfterLeft⟩
                            subst tree
                            rw [hLeftTokens, hAfterLeft]
                            simp [RawHilbertTokenTree.tokens,
                              hFirstLeft, List.append_assoc]
                          · rcases hImplication with
                              ⟨predicateHead, arguments, right,
                                hLeft, hTree, hAfterLeft⟩
                            subst left
                            subst tree
                            rw [hLeftTokens, hAfterLeft]
                            simp [RawHilbertTokenTree.tokens,
                              RawTermTokenTree.tokens,
                              hFirstLeft, List.append_assoc]
          · cases rest with
            | nil =>
                simp [parse_raw_hilbert_tokens,
                  hFirstLeft] at hParse
            | cons leftParenthesis body =>
                by_cases hLeftParenthesis :
                    leftParenthesis =
                      Numbered.logical_token
                        .leftParenthesis
                · cases hArgumentsParse :
                    parse_raw_term_list_tokens fuel body with
                  | none =>
                      simp [parse_raw_hilbert_tokens,
                        hFirstLeft, hLeftParenthesis,
                        hArgumentsParse] at hParse
                  | some argumentsResult =>
                      rcases argumentsResult with
                        ⟨arguments, finalSuffix⟩
                      have hResult : (.predicate first arguments,
                              finalSuffix) = (tree, suffix) := by
                        simpa [parse_raw_hilbert_tokens,
                          hFirstLeft, hLeftParenthesis,
                          hArgumentsParse] using hParse
                      have hTree :
                          tree =
                            .predicate first arguments := (congrArg Prod.fst hResult).symm
                      have hSuffix :
                          suffix = finalSuffix := (congrArg Prod.snd hResult).symm
                      subst tree
                      subst suffix
                      have hBodyTokens := (parse_raw_term_tokens_sound fuel).2
                          body arguments finalSuffix
                          hArgumentsParse
                      simp [RawHilbertTokenTree.tokens,
                        hLeftParenthesis, hBodyTokens,
                        List.append_assoc]
                · simp [parse_raw_hilbert_tokens,
                    hFirstLeft, hLeftParenthesis] at hParse
/-- 原始 Hilbert 树的序列化被通用 parser 精确恢复。 -/
private theorem parse_raw_hilbert_tokens_correct (tree : RawHilbertTokenTree) (hSeparated : tree.LexicallySeparated) (suffix : List Nat) (fuel : Nat)
    (hFuel : tree.height < fuel) :
    parse_raw_hilbert_tokens fuel (tree.tokens ++ suffix) =
      some (tree, suffix) := by
  induction fuel generalizing tree suffix with
  | zero =>
      omega
  | succ fuel ih =>
      cases tree with
      | equality left right =>
          rcases hSeparated with
            ⟨hLeftOdd, hRightOdd⟩
          have hLeftFuel : left.height < fuel := by
            simp [RawHilbertTokenTree.height] at hFuel
            omega
          have hRightFuel : right.height < fuel := by
            simp [RawHilbertTokenTree.height] at hFuel
            omega
          have hLeftSuffix :
              TermSuffixSeparated (Numbered.logical_token .equality :: (right.tokens ++
                    Numbered.logical_token
                        .rightParenthesis ::
                      suffix)) := by
            exact logical_equality_ne_left
          have hLeftParse := (parse_raw_term_tokens_correct fuel).1
              left hLeftOdd (Numbered.logical_token .equality :: (right.tokens ++
                  Numbered.logical_token
                      .rightParenthesis ::
                    suffix))
              hLeftSuffix hLeftFuel
          have hRightParse := (parse_raw_term_tokens_correct fuel).1
              right hRightOdd (Numbered.logical_token
                  .rightParenthesis ::
                suffix)
              logical_left_ne_right.symm hRightFuel
          rcases left.tokens_eq_head_cons hLeftOdd with
            ⟨head, tail, hHeadOdd, hLeftTokens⟩
          have hHeadNeNeg :
              head ≠
                Numbered.logical_token .negation :=
            odd_token_ne_logical hHeadOdd .negation
          have hHeadNeUniversal :
              head ≠
                Numbered.logical_token .universal :=
            odd_token_ne_logical hHeadOdd .universal
          have hHeadNeLeft :
              head ≠
                Numbered.logical_token
                  .leftParenthesis :=
            odd_token_ne_logical hHeadOdd
              .leftParenthesis
          simp [hLeftTokens]
            at hLeftParse
          simp [RawHilbertTokenTree.tokens,
            hLeftTokens, List.append_assoc,
            parse_raw_hilbert_tokens,
            hHeadNeNeg, hHeadNeUniversal,
            hHeadNeLeft, hLeftParse,
            parse_raw_atomic_or_predicate_implication_tail,
            hRightParse]
      | membership left right =>
          rcases hSeparated with
            ⟨hLeftOdd, hRightOdd⟩
          have hLeftFuel : left.height < fuel := by
            simp [RawHilbertTokenTree.height] at hFuel
            omega
          have hRightFuel : right.height < fuel := by
            simp [RawHilbertTokenTree.height] at hFuel
            omega
          have hLeftSuffix :
              TermSuffixSeparated (Numbered.membership_token :: (right.tokens ++
                    Numbered.logical_token
                        .rightParenthesis ::
                      suffix)) := by
            exact membership_ne_logical_left
          have hLeftParse := (parse_raw_term_tokens_correct fuel).1
              left hLeftOdd (Numbered.membership_token :: (right.tokens ++
                  Numbered.logical_token
                      .rightParenthesis ::
                    suffix))
              hLeftSuffix hLeftFuel
          have hRightParse := (parse_raw_term_tokens_correct fuel).1
              right hRightOdd (Numbered.logical_token
                  .rightParenthesis ::
                suffix)
              logical_left_ne_right.symm hRightFuel
          rcases left.tokens_eq_head_cons hLeftOdd with
            ⟨head, tail, hHeadOdd, hLeftTokens⟩
          have hHeadNeNeg :=
            odd_token_ne_logical hHeadOdd .negation
          have hHeadNeUniversal :=
            odd_token_ne_logical hHeadOdd .universal
          have hHeadNeLeft :=
            odd_token_ne_logical hHeadOdd
              .leftParenthesis
          simp [hLeftTokens]
            at hLeftParse
          simp [RawHilbertTokenTree.tokens,
            hLeftTokens, List.append_assoc,
            parse_raw_hilbert_tokens,
            hHeadNeNeg, hHeadNeUniversal,
            hHeadNeLeft, hLeftParse,
            parse_raw_atomic_or_predicate_implication_tail,
            membership_ne_logical_equality,
            hRightParse]
      | predicate head arguments =>
          rcases hSeparated with
            ⟨hHeadOdd, hArgumentsOdd⟩
          have hArgumentsFuel :
              RawTermTokenTree.list_height
                  arguments <
                fuel := by
            simpa [RawHilbertTokenTree.height] using hFuel
          have hArgumentsParse := (parse_raw_term_tokens_correct fuel).2
              arguments hArgumentsOdd suffix
              hArgumentsFuel
          have hHeadNeLeft :=
            odd_token_ne_logical hHeadOdd
              .leftParenthesis
          simp [RawHilbertTokenTree.tokens,
            parse_raw_hilbert_tokens,
            hHeadNeLeft, hArgumentsParse]
      | negation body =>
          have hBodyFuel : body.height < fuel := by
            simpa [RawHilbertTokenTree.height] using hFuel
          have hBodyParse :=
            ih body hSeparated (Numbered.logical_token
                  .rightParenthesis ::
                suffix)
              hBodyFuel
          simp [RawHilbertTokenTree.tokens,
            parse_raw_hilbert_tokens,
            List.append_assoc, hBodyParse]
      | implication left right =>
          rcases hSeparated with
            ⟨hLeftSeparated, hRightSeparated⟩
          have hLeftFuel : left.height < fuel := by
            simp [RawHilbertTokenTree.height] at hFuel
            omega
          have hRightFuel : right.height < fuel := by
            simp [RawHilbertTokenTree.height] at hFuel
            omega
          have hRightParse :=
            ih right hRightSeparated (Numbered.logical_token
                  .rightParenthesis ::
                suffix)
              hRightFuel
          cases left with
          | predicate head arguments =>
              rcases hLeftSeparated with
                ⟨hHeadOdd, hArgumentsOdd⟩
              have hArgumentsFuel :
                  RawTermTokenTree.list_height
                      arguments <
                    fuel := by
                simp [RawHilbertTokenTree.height]
                  at hLeftFuel
                omega
              let leftTerm : RawTermTokenTree :=
                .application head arguments
              have hLeftTermOdd :
                  leftTerm.HeadsOdd := by
                simpa [leftTerm,
                  RawTermTokenTree.HeadsOdd,
                  RawTermTokenTree.ListHeadsOdd]
                  using And.intro hHeadOdd hArgumentsOdd
              have hLeftTermHeight :
                  leftTerm.height < fuel := by
                dsimp [leftTerm,
                  RawTermTokenTree.height]
                simpa [RawHilbertTokenTree.height]
                  using hLeftFuel
              have hLeftSuffix :
                  TermSuffixSeparated (Numbered.logical_token
                        .implication :: (right.tokens ++
                        Numbered.logical_token
                            .rightParenthesis ::
                          suffix)) := by
                exact logical_implication_ne_left
              have hLeftParse := (parse_raw_term_tokens_correct fuel).1
                  leftTerm hLeftTermOdd (Numbered.logical_token
                      .implication :: (right.tokens ++
                      Numbered.logical_token
                          .rightParenthesis ::
                        suffix))
                  hLeftSuffix hLeftTermHeight
              have hHeadNeNeg :=
                odd_token_ne_logical
                  hHeadOdd .negation
              have hHeadNeUniversal :=
                odd_token_ne_logical
                  hHeadOdd .universal
              have hHeadNeLeft :=
                odd_token_ne_logical
                  hHeadOdd .leftParenthesis
              simp [leftTerm,
                RawTermTokenTree.tokens,
                List.append_assoc] at hLeftParse
              simp [RawHilbertTokenTree.tokens,
                List.append_assoc,
                parse_raw_hilbert_tokens,
                hHeadNeNeg, hHeadNeUniversal,
                hHeadNeLeft, hLeftParse,
                parse_raw_atomic_or_predicate_implication_tail,
                logical_implication_ne_equality,
                logical_implication_ne_membership,
                hRightParse]
          | equality leftTerm rightTerm =>
              have hLeftParse :=
                ih _ hLeftSeparated (Numbered.logical_token
                      .implication :: (right.tokens ++
                      Numbered.logical_token
                          .rightParenthesis ::
                        suffix))
                  hLeftFuel
              simp [RawHilbertTokenTree.tokens,
                List.append_assoc] at hLeftParse
              simp [RawHilbertTokenTree.tokens,
                parse_raw_hilbert_tokens,
                List.append_assoc, hLeftParse,
                parse_raw_implication_tail,
                logical_left_ne_negation,
                logical_left_ne_universal,
                hRightParse]
          | membership leftTerm rightTerm =>
              have hLeftParse :=
                ih _ hLeftSeparated (Numbered.logical_token
                      .implication :: (right.tokens ++
                      Numbered.logical_token
                          .rightParenthesis ::
                        suffix))
                  hLeftFuel
              simp [RawHilbertTokenTree.tokens,
                List.append_assoc] at hLeftParse
              simp [RawHilbertTokenTree.tokens,
                parse_raw_hilbert_tokens,
                List.append_assoc, hLeftParse,
                parse_raw_implication_tail,
                logical_left_ne_negation,
                logical_left_ne_universal,
                hRightParse]
          | negation body =>
              have hLeftParse :=
                ih _ hLeftSeparated (Numbered.logical_token
                      .implication :: (right.tokens ++
                      Numbered.logical_token
                          .rightParenthesis ::
                        suffix))
                  hLeftFuel
              simp [RawHilbertTokenTree.tokens,
                List.append_assoc] at hLeftParse
              simp [RawHilbertTokenTree.tokens,
                parse_raw_hilbert_tokens,
                List.append_assoc, hLeftParse,
                parse_raw_implication_tail,
                logical_left_ne_negation,
                logical_left_ne_universal,
                hRightParse]
          | implication leftLeft leftRight =>
              have hLeftParse :=
                ih _ hLeftSeparated (Numbered.logical_token
                      .implication :: (right.tokens ++
                      Numbered.logical_token
                          .rightParenthesis ::
                        suffix))
                  hLeftFuel
              simp [RawHilbertTokenTree.tokens,
                List.append_assoc] at hLeftParse
              simp [RawHilbertTokenTree.tokens,
                parse_raw_hilbert_tokens,
                List.append_assoc, hLeftParse,
                parse_raw_implication_tail,
                logical_left_ne_negation,
                logical_left_ne_universal,
                hRightParse]
          | universal variableToken body =>
              have hLeftParse :=
                ih _ hLeftSeparated (Numbered.logical_token
                      .implication :: (right.tokens ++
                      Numbered.logical_token
                          .rightParenthesis ::
                        suffix))
                  hLeftFuel
              simp [RawHilbertTokenTree.tokens,
                List.append_assoc] at hLeftParse
              simp [RawHilbertTokenTree.tokens,
                parse_raw_hilbert_tokens,
                List.append_assoc, hLeftParse,
                parse_raw_implication_tail,
                logical_left_ne_negation,
                logical_left_ne_universal,
                hRightParse]
      | universal variableToken body =>
          have hBodyFuel : body.height < fuel := by
            simpa [RawHilbertTokenTree.height] using hFuel
          have hBodyParse :=
            ih body hSeparated (Numbered.logical_token
                  .rightParenthesis ::
                suffix)
              hBodyFuel
          simp [RawHilbertTokenTree.tokens,
            parse_raw_hilbert_tokens,
            List.append_assoc, hBodyParse,
            logical_universal_ne_negation]
/-- 原始 Hilbert 树的递归高度严格小于其规范 token 串长度。 -/
theorem RawHilbertTokenTree.height_lt_tokens_length (tree : RawHilbertTokenTree) :
    tree.height < tree.tokens.length := by
  induction tree with
  | equality left right =>
      have hLeft :=
        RawTermTokenTree.height_lt_tokens_length left
      have hRight :=
        RawTermTokenTree.height_lt_tokens_length right
      simp [RawHilbertTokenTree.height,
        RawHilbertTokenTree.tokens] at *
      omega
  | membership left right =>
      have hLeft :=
        RawTermTokenTree.height_lt_tokens_length left
      have hRight :=
        RawTermTokenTree.height_lt_tokens_length right
      simp [RawHilbertTokenTree.height,
        RawHilbertTokenTree.tokens] at *
      omega
  | predicate head arguments =>
      have hArguments :=
        RawTermTokenTree.list_height_le_list_tokens_length
          arguments
      simp [RawHilbertTokenTree.height,
        RawHilbertTokenTree.tokens] at *
      omega
  | negation body ih =>
      simp [RawHilbertTokenTree.height,
        RawHilbertTokenTree.tokens] at *
      omega
  | implication left right ihLeft ihRight =>
      simp [RawHilbertTokenTree.height,
        RawHilbertTokenTree.tokens] at *
      omega
  | universal variableToken body ih =>
      simp [RawHilbertTokenTree.height,
        RawHilbertTokenTree.tokens] at *
      omega
namespace RawHilbertTokenTree
/--
完整消费输入 token 串的公开 Hilbert 解析器。
底层递归 fuel 由输入长度统一给出；成功结果不保留未消费后缀，因此后续分类器可以
直接对语法树做模式匹配。
-/
def parse? (input : List Nat) : Option RawHilbertTokenTree :=
  match parse_raw_hilbert_tokens (input.length + 1) input with
  | some (tree, []) => some tree
  | _ => none
/-- 公开 Hilbert parser 成功时，返回树的规范 token 串恰好是完整输入。 -/
theorem parse?_sound
    {input : List Nat} {tree : RawHilbertTokenTree} (hParse : parse? input = some tree) :
    tree.tokens = input := by
  unfold parse? at hParse
  cases hRaw :
      parse_raw_hilbert_tokens (input.length + 1) input with
  | none =>
      simp [hRaw] at hParse
  | some result =>
      rcases result with ⟨parsed, suffix⟩
      cases suffix with
      | nil =>
          have hTree : parsed = tree := by
            simpa [hRaw] using hParse
          subst parsed
          have hSound :=
            parse_raw_hilbert_tokens_sound (input.length + 1) input tree [] hRaw
          simpa using hSound.symm
      | cons head tail =>
          simp [hRaw] at hParse
/-- 词法分离的规范 Hilbert 树序列化可被公开解析器精确恢复。 -/
@[simp] theorem parse?_tokens (tree : RawHilbertTokenTree) (hSeparated : tree.LexicallySeparated) :
    parse? tree.tokens = some tree := by
  have hFuel :
      tree.height < tree.tokens.length + 1 := by
    exact Nat.lt_succ_of_lt tree.height_lt_tokens_length
  have hParse :
      parse_raw_hilbert_tokens (tree.tokens.length + 1) tree.tokens =
        some (tree, []) := by
    simpa using
      parse_raw_hilbert_tokens_correct
        tree hSeparated [] (tree.tokens.length + 1) hFuel
  simp [parse?, hParse]
end RawHilbertTokenTree
/-- 词法分离的原始 Hilbert token 序列化是单射。 -/
theorem RawHilbertTokenTree.tokens_injective
    {left right : RawHilbertTokenTree} (hLeft : left.LexicallySeparated) (hRight : right.LexicallySeparated) (hTokens : left.tokens = right.tokens) :
    left = right := by
  let fuel :=
    max left.height right.height + 1
  have hLeftFuel : left.height < fuel := by
    dsimp [fuel]
    omega
  have hRightFuel : right.height < fuel := by
    dsimp [fuel]
    omega
  have hLeftParse :=
    parse_raw_hilbert_tokens_correct
      left hLeft [] fuel hLeftFuel
  have hRightParse :=
    parse_raw_hilbert_tokens_correct
      right hRight [] fuel hRightFuel
  rw [hTokens] at hLeftParse
  rw [hRightParse] at hLeftParse
  exact (congrArg Prod.fst (Option.some.inj hLeftParse)).symm

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
