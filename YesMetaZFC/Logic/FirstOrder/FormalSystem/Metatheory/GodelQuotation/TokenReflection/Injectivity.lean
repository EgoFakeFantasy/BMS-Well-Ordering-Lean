import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.TokenReflection.Quotation

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace GodelQuotation
set_option autoImplicit false
open Nonlogical.BasicSetTheory

universe u v w u₁ u₂

/-! ## 规范变量与项树反演 -/
/-- 在深度 `depth` 的规范环境中，一个 LN 变量实际使用的内部名字。 -/
private def canonical_variable_name?
    {σ : Signature.{u, v, w}} (depth : Nat) :
    Var σ → Option Nat
  | .bvar _ index =>
      (canonical_bound_names depth)[index]?
  | .fvar _ id =>
      some (free_name id)
/-- 规范变量 quotation 正好先恢复内部名字，再施加变量 token。 -/
private theorem quote_variable_token_tree_canonical_eq
    {σ : Signature.{u, v, w}}
    [QuotationNumbering σ] (depth : Nat) (value : Var σ) :
    quote_term_token_tree_with?
        free_name (canonical_bound_names depth) (.var value) = (canonical_variable_name? depth value).map (fun name =>
          RawTermTokenTree.atom (Numbered.variable_token name)) := by
  cases value <;>
    simp [quote_term_token_tree_with?,
      canonical_variable_name?]
/--
规范偶/奇名字能够反演 LN 变量。
单排序性恢复 sort；规范环境的无重复性恢复 de Bruijn index；偶数自由名字与奇数
bound 名字的分离排除两类变量互相混淆。
-/
private theorem canonical_variable_name?_injective
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ] (depth : Nat)
    {left right : Var σ}
    {leftName rightName : Nat} (hLeft :
      canonical_variable_name? depth left =
        some leftName) (hRight :
      canonical_variable_name? depth right =
        some rightName) (hNames : leftName = rightName) :
    left = right := by
  cases left with
  | bvar leftSort leftIndex =>
      cases right with
      | bvar rightSort rightIndex =>
          have hLeftLookup : (canonical_bound_names depth)[leftIndex]? =
                some leftName := by
            simpa [canonical_variable_name?] using hLeft
          have hRightLookup : (canonical_bound_names depth)[rightIndex]? =
                some rightName := by
            simpa [canonical_variable_name?] using hRight
          have hLookups : (canonical_bound_names depth)[leftIndex]? = (canonical_bound_names depth)[rightIndex]? := by
            rw [hLeftLookup, hRightLookup, hNames]
          have hLeftIndex :
              leftIndex < (canonical_bound_names depth).length := (List.getElem?_eq_some_iff.mp
              hLeftLookup).1
          have hIndices : leftIndex = rightIndex := (List.getElem?_inj hLeftIndex (canonical_bound_names_nodup depth)).mp
                hLookups
          have hSorts : leftSort = rightSort := (numbering.sort_eq_object leftSort).trans (numbering.sort_eq_object rightSort).symm
          cases hSorts
          cases hIndices
          rfl
      | fvar rightSort rightId =>
          have hLeftLookup : (canonical_bound_names depth)[leftIndex]? =
                some leftName := by
            simpa [canonical_variable_name?] using hLeft
          have hRightName :
              rightName = free_name rightId := by
            simpa [canonical_variable_name?] using
              Option.some.inj hRight.symm
          have hMember :
              leftName ∈ canonical_bound_names depth :=
            List.mem_of_getElem? hLeftLookup
          have hFreeMember :
              free_name rightId ∈
                canonical_bound_names depth := by
            rw [← hRightName, ← hNames]
            exact hMember
          exact False.elim (free_name_not_mem_canonical
              rightId depth hFreeMember)
  | fvar leftSort leftId =>
      cases right with
      | bvar rightSort rightIndex =>
          have hLeftName :
              leftName = free_name leftId := by
            simpa [canonical_variable_name?] using
              Option.some.inj hLeft.symm
          have hRightLookup : (canonical_bound_names depth)[rightIndex]? =
                some rightName := by
            simpa [canonical_variable_name?] using hRight
          have hMember :
              rightName ∈ canonical_bound_names depth :=
            List.mem_of_getElem? hRightLookup
          have hFreeMember :
              free_name leftId ∈
                canonical_bound_names depth := by
            rw [← hLeftName, hNames]
            exact hMember
          exact False.elim (free_name_not_mem_canonical
              leftId depth hFreeMember)
      | fvar rightSort rightId =>
          have hLeftName :
              leftName = free_name leftId := by
            simpa [canonical_variable_name?] using
              Option.some.inj hLeft.symm
          have hRightName :
              rightName = free_name rightId := by
            simpa [canonical_variable_name?] using
              Option.some.inj hRight.symm
          have hIds : leftId = rightId :=
            free_name_injective (hLeftName.symm.trans (hNames.trans hRightName))
          have hSorts : leftSort = rightSort := (numbering.sort_eq_object leftSort).trans (numbering.sort_eq_object rightSort).symm
          cases hSorts
          cases hIds
          rfl
/-- 非空列表的成功 `mapM` 结果仍是非空，并逐项给出首尾证书。 -/
private theorem option_mapM_cons_eq_some_inv
    {α : Type u₁} {β : Type u₂} (transform : α → Option β)
    {head : α} {tail : List α}
    {results : List β} (hMap : (head :: tail).mapM transform =
        some results) :
    ∃ headResult tailResults,
      transform head = some headResult ∧
        tail.mapM transform = some tailResults ∧
          results = headResult :: tailResults := by
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
          exact
            ⟨headResult, tailResults,
              rfl, rfl, rfl⟩
mutual
  /--
  在规范偶/奇环境中，通用项到原始 token 树的 quotation 是单射。
  变量、常元与正元函数三种词法形状被同时反演；正元函数分支把符号编号反演与
  参数列表反演组合起来。
  -/
  private theorem quote_term_token_tree_with?_canonical_injective
      {σ : Signature.{u, v, w}}
      [numbering : QuotationNumbering σ] (depth : Nat) :
      ∀ {left right : Term σ}
          {leftTree rightTree : RawTermTokenTree},
        quote_term_token_tree_with?
            free_name (canonical_bound_names depth)
            left =
          some leftTree →
        quote_term_token_tree_with?
            free_name (canonical_bound_names depth)
            right =
          some rightTree →
        leftTree = rightTree →
        left = right
    | .var leftVariable, right,
        leftTree, rightTree,
        hLeft, hRight, hTrees => by
        rw [
          quote_variable_token_tree_canonical_eq
            depth leftVariable] at hLeft
        cases hLeftName :
            canonical_variable_name?
              depth leftVariable with
        | none =>
            simp [hLeftName] at hLeft
        | some leftName =>
            have hLeftTree :
                RawTermTokenTree.atom (Numbered.variable_token leftName) =
                  leftTree := by
              simpa [hLeftName] using hLeft
            cases right with
            | var rightVariable =>
                rw [
                  quote_variable_token_tree_canonical_eq
                    depth rightVariable] at hRight
                cases hRightName :
                    canonical_variable_name?
                      depth rightVariable with
                | none =>
                    simp [hRightName] at hRight
                | some rightName =>
                    have hRightTree :
                        RawTermTokenTree.atom (Numbered.variable_token
                              rightName) =
                          rightTree := by
                      simpa [hRightName] using hRight
                    have hNodes :
                        RawTermTokenTree.atom (Numbered.variable_token
                              leftName) =
                          RawTermTokenTree.atom (Numbered.variable_token
                              rightName) :=
                      hLeftTree.trans (hTrees.trans hRightTree.symm)
                    injection hNodes with hTokens
                    have hNames : leftName = rightName :=
                      token_reflection_variable_token_injective hTokens
                    have hVariables :
                        leftVariable = rightVariable :=
                      canonical_variable_name?_injective
                        depth hLeftName hRightName hNames
                    cases hVariables
                    rfl
            | app rightFunction rightArguments =>
                cases rightArguments with
                | nil =>
                    have hRightTree :
                        RawTermTokenTree.atom (Numbered.constant_token (numbering.function_number
                                rightFunction)) =
                          rightTree := by
                      simpa [quote_term_token_tree_with?]
                        using hRight
                    have hNodes :
                        RawTermTokenTree.atom (Numbered.variable_token
                              leftName) =
                          RawTermTokenTree.atom (Numbered.constant_token (numbering.function_number
                                rightFunction)) :=
                      hLeftTree.trans (hTrees.trans hRightTree.symm)
                    injection hNodes with hTokens
                    exact False.elim (token_reflection_constant_token_ne_variable_token (numbering.function_number
                          rightFunction)
                        leftName hTokens.symm)
                | cons rightHead rightTail =>
                    cases hRightTrees : (rightHead :: rightTail).mapM (quote_term_token_tree_with?
                            free_name (canonical_bound_names depth)) with
                    | none =>
                        simp [quote_term_token_tree_with?,
                          hRightTrees] at hRight
                    | some rightTrees =>
                        rcases
                            option_mapM_cons_eq_some_inv (quote_term_token_tree_with?
                                free_name (canonical_bound_names depth))
                              hRightTrees with
                          ⟨rightHeadTree,
                            rightTailTrees,
                            _hRightHead,
                            _hRightTail,
                            hRightTreesShape⟩
                        subst rightTrees
                        have hRightTree :
                            RawTermTokenTree.application (Numbered.function_token ((rightHead ::
                                      rightTail).length - 1) (numbering.function_number
                                    rightFunction)) (rightHeadTree ::
                                  rightTailTrees) =
                              rightTree := by
                          simpa [quote_term_token_tree_with?,
                            hRightTrees] using hRight
                        have hNodes :
                            RawTermTokenTree.atom (Numbered.variable_token
                                  leftName) =
                              RawTermTokenTree.application (Numbered.function_token ((rightHead ::
                                      rightTail).length - 1) (numbering.function_number
                                    rightFunction)) (rightHeadTree ::
                                  rightTailTrees) :=
                          hLeftTree.trans (hTrees.trans hRightTree.symm)
                        cases hNodes
    | .app leftFunction .nil, right,
        leftTree, rightTree,
        hLeft, hRight, hTrees => by
        have hLeftTree :
            RawTermTokenTree.atom (Numbered.constant_token (numbering.function_number
                    leftFunction)) =
              leftTree := by
          simpa [quote_term_token_tree_with?]
            using hLeft
        cases right with
        | var rightVariable =>
            rw [
              quote_variable_token_tree_canonical_eq
                depth rightVariable] at hRight
            cases hRightName :
                canonical_variable_name?
                  depth rightVariable with
            | none =>
                simp [hRightName] at hRight
            | some rightName =>
                have hRightTree :
                    RawTermTokenTree.atom (Numbered.variable_token
                          rightName) =
                      rightTree := by
                  simpa [hRightName] using hRight
                have hNodes :
                    RawTermTokenTree.atom (Numbered.constant_token (numbering.function_number
                            leftFunction)) =
                      RawTermTokenTree.atom (Numbered.variable_token
                          rightName) :=
                  hLeftTree.trans (hTrees.trans hRightTree.symm)
                injection hNodes with hTokens
                exact False.elim (token_reflection_constant_token_ne_variable_token (numbering.function_number
                      leftFunction)
                    rightName hTokens)
        | app rightFunction rightArguments =>
            cases rightArguments with
            | nil =>
                have hRightTree :
                    RawTermTokenTree.atom (Numbered.constant_token (numbering.function_number
                            rightFunction)) =
                      rightTree := by
                  simpa [quote_term_token_tree_with?]
                    using hRight
                have hNodes :
                    RawTermTokenTree.atom (Numbered.constant_token (numbering.function_number
                            leftFunction)) =
                      RawTermTokenTree.atom (Numbered.constant_token (numbering.function_number
                            rightFunction)) :=
                  hLeftTree.trans (hTrees.trans hRightTree.symm)
                injection hNodes with hTokens
                have hNumbers :
                    numbering.function_number leftFunction =
                      numbering.function_number
                        rightFunction :=
                  token_reflection_constant_token_injective hTokens
                have hFunctions :
                    leftFunction = rightFunction :=
                  numbering.function_number_injective
                    hNumbers
                cases hFunctions
                rfl
            | cons rightHead rightTail =>
                cases hRightTrees : (rightHead :: rightTail).mapM (quote_term_token_tree_with?
                        free_name (canonical_bound_names depth)) with
                | none =>
                    simp [quote_term_token_tree_with?,
                      hRightTrees] at hRight
                | some rightTrees =>
                    rcases
                        option_mapM_cons_eq_some_inv (quote_term_token_tree_with?
                            free_name (canonical_bound_names depth))
                          hRightTrees with
                      ⟨rightHeadTree,
                        rightTailTrees,
                        _hRightHead,
                        _hRightTail,
                        hRightTreesShape⟩
                    subst rightTrees
                    have hRightTree :
                        RawTermTokenTree.application (Numbered.function_token ((rightHead ::
                                  rightTail).length - 1) (numbering.function_number
                                rightFunction)) (rightHeadTree ::
                              rightTailTrees) =
                          rightTree := by
                      simpa [quote_term_token_tree_with?,
                        hRightTrees] using hRight
                    have hNodes :
                        RawTermTokenTree.atom (Numbered.constant_token (numbering.function_number
                                leftFunction)) =
                          RawTermTokenTree.application (Numbered.function_token ((rightHead ::
                                  rightTail).length - 1) (numbering.function_number
                                rightFunction)) (rightHeadTree ::
                              rightTailTrees) :=
                      hLeftTree.trans (hTrees.trans hRightTree.symm)
                    cases hNodes
    | .app leftFunction (leftHead :: leftTail), right,
        leftTree, rightTree,
        hLeft, hRight, hTrees => by
        cases hLeftTrees : (leftHead :: leftTail).mapM (quote_term_token_tree_with?
                free_name (canonical_bound_names depth)) with
        | none =>
            simp [quote_term_token_tree_with?,
              hLeftTrees] at hLeft
        | some leftTrees =>
            rcases
                option_mapM_cons_eq_some_inv (quote_term_token_tree_with?
                    free_name (canonical_bound_names depth))
                  hLeftTrees with
              ⟨leftHeadTree, leftTailTrees,
                _hLeftHead, _hLeftTail,
                hLeftTreesShape⟩
            subst leftTrees
            have hLeftTree :
                RawTermTokenTree.application (Numbered.function_token ((leftHead :: leftTail).length - 1) (numbering.function_number
                        leftFunction)) (leftHeadTree :: leftTailTrees) =
                  leftTree := by
              simpa [quote_term_token_tree_with?,
                hLeftTrees] using hLeft
            cases right with
            | var rightVariable =>
                rw [
                  quote_variable_token_tree_canonical_eq
                    depth rightVariable] at hRight
                cases hRightName :
                    canonical_variable_name?
                      depth rightVariable with
                | none =>
                    simp [hRightName] at hRight
                | some rightName =>
                    have hRightTree :
                        RawTermTokenTree.atom (Numbered.variable_token
                              rightName) =
                          rightTree := by
                      simpa [hRightName] using hRight
                    have hNodes :
                        RawTermTokenTree.application (Numbered.function_token ((leftHead ::
                                  leftTail).length - 1) (numbering.function_number
                                leftFunction)) (leftHeadTree ::
                              leftTailTrees) =
                          RawTermTokenTree.atom (Numbered.variable_token
                              rightName) :=
                      hLeftTree.trans (hTrees.trans hRightTree.symm)
                    cases hNodes
            | app rightFunction rightArguments =>
                cases rightArguments with
                | nil =>
                    have hRightTree :
                        RawTermTokenTree.atom (Numbered.constant_token (numbering.function_number
                                rightFunction)) =
                          rightTree := by
                      simpa [quote_term_token_tree_with?]
                        using hRight
                    have hNodes :
                        RawTermTokenTree.application (Numbered.function_token ((leftHead ::
                                  leftTail).length - 1) (numbering.function_number
                                leftFunction)) (leftHeadTree ::
                              leftTailTrees) =
                          RawTermTokenTree.atom (Numbered.constant_token (numbering.function_number
                                rightFunction)) :=
                      hLeftTree.trans (hTrees.trans hRightTree.symm)
                    cases hNodes
                | cons rightHead rightTail =>
                    cases hRightTrees : (rightHead :: rightTail).mapM (quote_term_token_tree_with?
                            free_name (canonical_bound_names depth)) with
                    | none =>
                        simp [quote_term_token_tree_with?,
                          hRightTrees] at hRight
                    | some rightTrees =>
                        rcases
                            option_mapM_cons_eq_some_inv (quote_term_token_tree_with?
                                free_name (canonical_bound_names depth))
                              hRightTrees with
                          ⟨rightHeadTree,
                            rightTailTrees,
                            _hRightHead,
                            _hRightTail,
                            hRightTreesShape⟩
                        subst rightTrees
                        have hRightTree :
                            RawTermTokenTree.application (Numbered.function_token ((rightHead ::
                                      rightTail).length - 1) (numbering.function_number
                                    rightFunction)) (rightHeadTree ::
                                  rightTailTrees) =
                              rightTree := by
                          simpa [quote_term_token_tree_with?,
                            hRightTrees] using hRight
                        have hNodes :
                            RawTermTokenTree.application (Numbered.function_token ((leftHead ::
                                      leftTail).length - 1) (numbering.function_number
                                    leftFunction)) (leftHeadTree ::
                                  leftTailTrees) =
                              RawTermTokenTree.application (Numbered.function_token ((rightHead ::
                                      rightTail).length - 1) (numbering.function_number
                                    rightFunction)) (rightHeadTree ::
                                  rightTailTrees) :=
                          hLeftTree.trans (hTrees.trans hRightTree.symm)
                        injection hNodes with
                          hHeadTokens hArgumentTrees
                        rcases
                            token_reflection_function_token_injective
                              hHeadTokens with
                          ⟨_hArities, hNumbers⟩
                        have hFunctions :
                            leftFunction = rightFunction :=
                          numbering.function_number_injective
                            hNumbers
                        have hArguments :
                            leftHead :: leftTail =
                              rightHead :: rightTail :=
                          quote_term_token_trees_with?_canonical_injective
                            depth hLeftTrees hRightTrees
                            hArgumentTrees
                        cases hFunctions
                        cases hArguments
                        rfl
  termination_by left => sizeOf left
  /-- 规范项树 quotation 对整列参数逐点单射。 -/
  private theorem quote_term_token_trees_with?_canonical_injective
      {σ : Signature.{u, v, w}}
      [QuotationNumbering σ] (depth : Nat) :
      ∀ {left right : List (Term σ)}
          {leftTrees rightTrees :
            List RawTermTokenTree},
        left.mapM (quote_term_token_tree_with?
              free_name (canonical_bound_names depth)) =
          some leftTrees →
        right.mapM (quote_term_token_tree_with?
              free_name (canonical_bound_names depth)) =
          some rightTrees →
        leftTrees = rightTrees →
        left = right
    | .nil, right,
        leftTrees, rightTrees,
        hLeft, hRight, hTrees => by
        have hLeftTreesNil :
            leftTrees = [] := by
          simpa using Option.some.inj hLeft.symm
        cases right with
        | nil =>
            rfl
        | cons rightHead rightTail =>
            rcases
                option_mapM_cons_eq_some_inv (quote_term_token_tree_with?
                    free_name (canonical_bound_names depth))
                  hRight with
              ⟨rightHeadTree, rightTailTrees,
                _hRightHead, _hRightTail,
                hRightTreesShape⟩
            have hImpossible : ([] : List RawTermTokenTree) =
                  rightHeadTree :: rightTailTrees :=
              hLeftTreesNil.symm.trans (hTrees.trans hRightTreesShape)
            cases hImpossible
    | leftHead :: leftTail, right,
        leftTrees, rightTrees,
        hLeft, hRight, hTrees => by
        rcases
            option_mapM_cons_eq_some_inv (quote_term_token_tree_with?
                free_name (canonical_bound_names depth))
              hLeft with
          ⟨leftHeadTree, leftTailTrees,
            hLeftHead, hLeftTail,
            hLeftTreesShape⟩
        cases right with
        | nil =>
            have hRightTreesNil :
                rightTrees = [] := by
              simpa using Option.some.inj hRight.symm
            have hImpossible :
                leftHeadTree :: leftTailTrees = ([] : List RawTermTokenTree) :=
              hLeftTreesShape.symm.trans (hTrees.trans hRightTreesNil)
            cases hImpossible
        | cons rightHead rightTail =>
            rcases
                option_mapM_cons_eq_some_inv (quote_term_token_tree_with?
                    free_name (canonical_bound_names depth))
                  hRight with
              ⟨rightHeadTree, rightTailTrees,
                hRightHead, hRightTail,
                hRightTreesShape⟩
            have hTreeLists :
                leftHeadTree :: leftTailTrees =
                  rightHeadTree :: rightTailTrees :=
              hLeftTreesShape.symm.trans (hTrees.trans hRightTreesShape)
            injection hTreeLists with
              hHeadTrees hTailTrees
            have hHeads : leftHead = rightHead :=
              quote_term_token_tree_with?_canonical_injective
                depth hLeftHead hRightHead hHeadTrees
            have hTails : leftTail = rightTail :=
              quote_term_token_trees_with?_canonical_injective
                depth hLeftTail hRightTail hTailTrees
            cases hHeads
            cases hTails
            rfl
  termination_by left => sizeOf left
end
/-! ## 关系原子反演 -/
/--
规范环境中，成功的关系原子 quotation 树同时决定关系符号与参数列。
专用隶属关系由 `membership_unique` 恢复；普通谓词由谓词 token 的指数唯一性和
`relation_number_injective` 恢复。
-/
private theorem quote_relation_token_tree_with?_canonical_injective
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ] (depth : Nat)
    {leftRelation rightRelation : σ.RelSymbol}
    {leftArguments rightArguments : List (Term σ)}
    {leftTree rightTree : RawHilbertTokenTree} (hLeft :
      quote_relation_token_tree_with?
          free_name (canonical_bound_names depth)
          leftRelation leftArguments =
        some leftTree) (hRight :
      quote_relation_token_tree_with?
          free_name (canonical_bound_names depth)
          rightRelation rightArguments =
        some rightTree) (hTrees : leftTree = rightTree) :
    leftRelation = rightRelation ∧
      leftArguments = rightArguments := by
  cases hLeftKind :
      numbering.relation_kind leftRelation with
  | membership =>
      cases leftArguments with
      | nil =>
          simp [quote_relation_token_tree_with?,
            hLeftKind] at hLeft
      | cons leftTerm leftTail =>
          cases leftTail with
          | nil =>
              simp [quote_relation_token_tree_with?,
                hLeftKind] at hLeft
          | cons leftRightTerm leftExtra =>
              cases leftExtra with
              | cons extra rest =>
                  simp [quote_relation_token_tree_with?,
                    hLeftKind] at hLeft
              | nil =>
                  cases hLeftTerm :
                      quote_term_token_tree_with?
                        free_name (canonical_bound_names depth)
                        leftTerm with
                  | none =>
                      simp [quote_relation_token_tree_with?,
                        hLeftKind, hLeftTerm] at hLeft
                  | some leftTermTree =>
                      cases hLeftRightTerm :
                          quote_term_token_tree_with?
                            free_name (canonical_bound_names depth)
                            leftRightTerm with
                      | none =>
                          simp [quote_relation_token_tree_with?,
                            hLeftKind, hLeftTerm,
                            hLeftRightTerm] at hLeft
                      | some leftRightTermTree =>
                          have hLeftTree :
                              RawHilbertTokenTree.membership
                                  leftTermTree
                                  leftRightTermTree =
                                leftTree := by
                            simpa [
                              quote_relation_token_tree_with?,
                              hLeftKind, hLeftTerm,
                              hLeftRightTerm] using hLeft
                          cases hRightKind :
                              numbering.relation_kind
                                rightRelation with
                          | membership =>
                              cases rightArguments with
                              | nil =>
                                  simp [
                                    quote_relation_token_tree_with?,
                                    hRightKind] at hRight
                              | cons rightTerm rightTail =>
                                  cases rightTail with
                                  | nil =>
                                      simp [
                                        quote_relation_token_tree_with?,
                                        hRightKind] at hRight
                                  | cons rightRightTerm rightExtra =>
                                      cases rightExtra with
                                      | cons extra rest =>
                                          simp [
                                            quote_relation_token_tree_with?,
                                            hRightKind] at hRight
                                      | nil =>
                                          cases hRightTerm :
                                              quote_term_token_tree_with?
                                                free_name (canonical_bound_names
                                                  depth)
                                                rightTerm with
                                          | none =>
                                              simp [
                                                quote_relation_token_tree_with?,
                                                hRightKind,
                                                hRightTerm] at hRight
                                          | some rightTermTree =>
                                              cases hRightRightTerm :
                                                  quote_term_token_tree_with?
                                                    free_name (canonical_bound_names
                                                      depth)
                                                    rightRightTerm with
                                              | none =>
                                                  simp [
                                                    quote_relation_token_tree_with?,
                                                    hRightKind,
                                                    hRightTerm,
                                                    hRightRightTerm] at hRight
                                              | some rightRightTermTree =>
                                                  have hRightTree :
                                                      RawHilbertTokenTree.membership
                                                          rightTermTree
                                                          rightRightTermTree =
                                                        rightTree := by
                                                    simpa [
                                                      quote_relation_token_tree_with?,
                                                      hRightKind,
                                                      hRightTerm,
                                                      hRightRightTerm] using
                                                        hRight
                                                  have hNodes :
                                                      RawHilbertTokenTree.membership
                                                          leftTermTree
                                                          leftRightTermTree =
                                                        RawHilbertTokenTree.membership
                                                          rightTermTree
                                                          rightRightTermTree :=
                                                    hLeftTree.trans (hTrees.trans
                                                        hRightTree.symm)
                                                  injection hNodes with
                                                    hTermTrees
                                                    hRightTermTrees
                                                  have hRelations :
                                                      leftRelation =
                                                        rightRelation :=
                                                    numbering.membership_unique
                                                      hLeftKind
                                                      hRightKind
                                                  have hTerms :
                                                      leftTerm =
                                                        rightTerm :=
                                                    quote_term_token_tree_with?_canonical_injective
                                                      depth
                                                      hLeftTerm
                                                      hRightTerm
                                                      hTermTrees
                                                  have hRightTerms :
                                                      leftRightTerm =
                                                        rightRightTerm :=
                                                    quote_term_token_tree_with?_canonical_injective
                                                      depth
                                                      hLeftRightTerm
                                                      hRightRightTerm
                                                      hRightTermTrees
                                                  exact
                                                    ⟨hRelations,
                                                      by
                                                        cases hTerms
                                                        cases hRightTerms
                                                        rfl⟩
                          | predicate =>
                              cases rightArguments with
                              | nil =>
                                  simp [
                                    quote_relation_token_tree_with?,
                                    hRightKind] at hRight
                              | cons rightHead rightTail =>
                                  cases hRightTrees : (rightHead ::
                                          rightTail).mapM (quote_term_token_tree_with?
                                          free_name (canonical_bound_names
                                            depth)) with
                                  | none =>
                                      simp [
                                        quote_relation_token_tree_with?,
                                        hRightKind,
                                        hRightTrees] at hRight
                                  | some rightTrees =>
                                      rcases
                                          option_mapM_cons_eq_some_inv (quote_term_token_tree_with?
                                              free_name (canonical_bound_names
                                                depth))
                                            hRightTrees with
                                        ⟨rightHeadTree,
                                          rightTailTrees,
                                          _hRightHead,
                                          _hRightTail,
                                          hRightTreesShape⟩
                                      subst rightTrees
                                      have hRightTree :
                                          RawHilbertTokenTree.predicate (Numbered.predicate_token ((rightHead ::
                                                    rightTail).length - 1) (numbering.relation_number
                                                  rightRelation)) (rightHeadTree ::
                                                rightTailTrees) =
                                            rightTree := by
                                        simpa [
                                          quote_relation_token_tree_with?,
                                          hRightKind,
                                          hRightTrees] using hRight
                                      have hNodes :
                                          RawHilbertTokenTree.membership
                                              leftTermTree
                                              leftRightTermTree =
                                            RawHilbertTokenTree.predicate (Numbered.predicate_token ((rightHead ::
                                                    rightTail).length - 1) (numbering.relation_number
                                                  rightRelation)) (rightHeadTree ::
                                                rightTailTrees) :=
                                        hLeftTree.trans (hTrees.trans
                                            hRightTree.symm)
                                      cases hNodes
  | predicate =>
      cases leftArguments with
      | nil =>
          simp [quote_relation_token_tree_with?,
            hLeftKind] at hLeft
      | cons leftHead leftTail =>
          cases hLeftTrees : (leftHead :: leftTail).mapM (quote_term_token_tree_with?
                  free_name (canonical_bound_names depth)) with
          | none =>
              simp [quote_relation_token_tree_with?,
                hLeftKind, hLeftTrees] at hLeft
          | some leftTrees =>
              rcases
                  option_mapM_cons_eq_some_inv (quote_term_token_tree_with?
                      free_name (canonical_bound_names depth))
                    hLeftTrees with
                ⟨leftHeadTree, leftTailTrees,
                  _hLeftHead, _hLeftTail,
                  hLeftTreesShape⟩
              subst leftTrees
              have hLeftTree :
                  RawHilbertTokenTree.predicate (Numbered.predicate_token ((leftHead :: leftTail).length - 1) (numbering.relation_number
                          leftRelation)) (leftHeadTree :: leftTailTrees) =
                    leftTree := by
                simpa [quote_relation_token_tree_with?,
                  hLeftKind, hLeftTrees] using hLeft
              cases hRightKind :
                  numbering.relation_kind rightRelation with
              | membership =>
                  cases rightArguments with
                  | nil =>
                      simp [quote_relation_token_tree_with?,
                        hRightKind] at hRight
                  | cons rightTerm rightTail =>
                      cases rightTail with
                      | nil =>
                          simp [
                            quote_relation_token_tree_with?,
                            hRightKind] at hRight
                      | cons rightRightTerm rightExtra =>
                          cases rightExtra with
                          | cons extra rest =>
                              simp [
                                quote_relation_token_tree_with?,
                                hRightKind] at hRight
                          | nil =>
                              cases hRightTerm :
                                  quote_term_token_tree_with?
                                    free_name (canonical_bound_names depth)
                                    rightTerm with
                              | none =>
                                  simp [
                                    quote_relation_token_tree_with?,
                                    hRightKind,
                                    hRightTerm] at hRight
                              | some rightTermTree =>
                                  cases hRightRightTerm :
                                      quote_term_token_tree_with?
                                        free_name (canonical_bound_names depth)
                                        rightRightTerm with
                                  | none =>
                                      simp [
                                        quote_relation_token_tree_with?,
                                        hRightKind,
                                        hRightTerm,
                                        hRightRightTerm] at hRight
                                  | some rightRightTermTree =>
                                      have hRightTree :
                                          RawHilbertTokenTree.membership
                                              rightTermTree
                                              rightRightTermTree =
                                            rightTree := by
                                        simpa [
                                          quote_relation_token_tree_with?,
                                          hRightKind,
                                          hRightTerm,
                                          hRightRightTerm] using hRight
                                      have hNodes :
                                          RawHilbertTokenTree.predicate (Numbered.predicate_token ((leftHead ::
                                                    leftTail).length - 1) (numbering.relation_number
                                                  leftRelation)) (leftHeadTree ::
                                                leftTailTrees) =
                                            RawHilbertTokenTree.membership
                                              rightTermTree
                                              rightRightTermTree :=
                                        hLeftTree.trans (hTrees.trans
                                            hRightTree.symm)
                                      cases hNodes
              | predicate =>
                  cases rightArguments with
                  | nil =>
                      simp [quote_relation_token_tree_with?,
                        hRightKind] at hRight
                  | cons rightHead rightTail =>
                      cases hRightTrees : (rightHead :: rightTail).mapM (quote_term_token_tree_with?
                              free_name (canonical_bound_names depth)) with
                      | none =>
                          simp [quote_relation_token_tree_with?,
                            hRightKind,
                            hRightTrees] at hRight
                      | some rightTrees =>
                          rcases
                              option_mapM_cons_eq_some_inv (quote_term_token_tree_with?
                                  free_name (canonical_bound_names depth))
                                hRightTrees with
                            ⟨rightHeadTree,
                              rightTailTrees,
                              _hRightHead,
                              _hRightTail,
                              hRightTreesShape⟩
                          subst rightTrees
                          have hRightTree :
                              RawHilbertTokenTree.predicate (Numbered.predicate_token ((rightHead ::
                                        rightTail).length - 1) (numbering.relation_number
                                      rightRelation)) (rightHeadTree ::
                                    rightTailTrees) =
                                rightTree := by
                            simpa [
                              quote_relation_token_tree_with?,
                              hRightKind,
                              hRightTrees] using hRight
                          have hNodes :
                              RawHilbertTokenTree.predicate (Numbered.predicate_token ((leftHead ::
                                        leftTail).length - 1) (numbering.relation_number
                                      leftRelation)) (leftHeadTree ::
                                    leftTailTrees) =
                                RawHilbertTokenTree.predicate (Numbered.predicate_token ((rightHead ::
                                        rightTail).length - 1) (numbering.relation_number
                                      rightRelation)) (rightHeadTree ::
                                    rightTailTrees) :=
                            hLeftTree.trans (hTrees.trans hRightTree.symm)
                          injection hNodes with
                            hHeadTokens hArgumentTrees
                          rcases
                              token_reflection_predicate_token_injective
                                hHeadTokens with
                            ⟨_hArities, hNumbers⟩
                          have hRelations :
                              leftRelation = rightRelation :=
                            numbering.relation_number_injective
                              hNumbers
                          have hArguments :
                              leftHead :: leftTail =
                                rightHead :: rightTail :=
                            quote_term_token_trees_with?_canonical_injective
                              depth hLeftTrees hRightTrees
                              hArgumentTrees
                          exact
                            ⟨hRelations, hArguments⟩
/-! ## Hilbert 根构造反演 -/
/-- 忘掉关系原子的内部种类后，原始 Hilbert 树的五类公式根标签。 -/
private def RawHilbertTokenTree.formulaRootTag :
    RawHilbertTokenTree → Nat
  | .membership _ _ => 0
  | .predicate _ _ => 0
  | .equality _ _ => 1
  | .negation _ => 2
  | .implication _ _ => 3
  | .universal _ _ => 4
/-- 正式公式处于 Hilbert 核时的五类根标签。 -/
private def hilbert_formula_root_tag?
    {σ : Signature.{u, v, w}} :
    Formula σ → Option Nat
  | .rel _ _ => some 0
  | .equal _ _ => some 1
  | .neg _ => some 2
  | .imp _ _ => some 3
  | .forallE _ _ => some 4
  | _ => none
/-- 每个成功的关系原子 quotation 树都保留关系公式根标签。 -/
private theorem quote_relation_token_tree_with?_formula_root_tag
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ] (freeNaming : FreeVarId → Nat) (boundNames : List Nat)
    {relation : σ.RelSymbol}
    {arguments : List (Term σ)}
    {tree : RawHilbertTokenTree} (hTree :
      quote_relation_token_tree_with?
          freeNaming boundNames relation arguments =
        some tree) :
    tree.formulaRootTag = 0 := by
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
              | cons extra rest =>
                  simp [quote_relation_token_tree_with?,
                    hKind] at hTree
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
                          rfl
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
              rfl
/-- 任意成功的通用 Hilbert quotation 树都保持五类公式根标签。 -/
private theorem quote_hilbert_token_tree_with?_formula_root_tag
    {σ : Signature.{u, v, w}}
    [QuotationNumbering σ] (freeNaming binderNaming : Nat → Nat) (boundNames : List Nat) (depth : Nat)
    {formula : Formula σ}
    {tree : RawHilbertTokenTree} (hTree :
      quote_hilbert_token_tree_with?
          freeNaming binderNaming
          boundNames depth formula =
        some tree) :
    hilbert_formula_root_tag? formula =
      some tree.formulaRootTag := by
  cases formula with
  | falsum =>
      simp [quote_hilbert_token_tree_with?] at hTree
  | truth =>
      simp [quote_hilbert_token_tree_with?] at hTree
  | rel relation arguments =>
      have hTag :
          tree.formulaRootTag = 0 :=
        quote_relation_token_tree_with?_formula_root_tag
          freeNaming boundNames hTree
      simp [hilbert_formula_root_tag?, hTag]
  | equal left right =>
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
              rfl
  | neg body =>
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
          rfl
  | conj left right =>
      simp [quote_hilbert_token_tree_with?] at hTree
  | disj left right =>
      simp [quote_hilbert_token_tree_with?] at hTree
  | imp left right =>
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
              rfl
  | iff left right =>
      simp [quote_hilbert_token_tree_with?] at hTree
  | forallE sort body =>
      let name := binderNaming depth
      cases hBody :
          quote_hilbert_token_tree_with?
            freeNaming binderNaming (name :: boundNames) (depth + 1)
            body with
      | none =>
          simp [quote_hilbert_token_tree_with?,
            name, hBody] at hTree
      | some bodyTree =>
          simp [quote_hilbert_token_tree_with?,
            name, hBody] at hTree
          subst tree
          rfl
  | existsE sort body =>
      simp [quote_hilbert_token_tree_with?] at hTree
/-- 相等的成功 quotation 树必然来自相同的 Hilbert 根构造。 -/
private theorem quote_hilbert_token_tree_with?_formula_root_tag_eq
    {σ : Signature.{u, v, w}}
    [QuotationNumbering σ] (freeNaming binderNaming : Nat → Nat) (boundNames : List Nat) (depth : Nat)
    {left right : Formula σ}
    {leftTree rightTree : RawHilbertTokenTree} (hLeft :
      quote_hilbert_token_tree_with?
          freeNaming binderNaming
          boundNames depth left =
        some leftTree) (hRight :
      quote_hilbert_token_tree_with?
          freeNaming binderNaming
          boundNames depth right =
        some rightTree) (hTrees : leftTree = rightTree) :
    hilbert_formula_root_tag? left =
      hilbert_formula_root_tag? right := by
  calc
    hilbert_formula_root_tag? left =
        some leftTree.formulaRootTag :=
      quote_hilbert_token_tree_with?_formula_root_tag
        freeNaming binderNaming
        boundNames depth hLeft
    _ = some rightTree.formulaRootTag := by
      exact congrArg (fun tree => some tree.formulaRootTag)
        hTrees
    _ = hilbert_formula_root_tag? right := (quote_hilbert_token_tree_with?_formula_root_tag
        freeNaming binderNaming
        boundNames depth hRight).symm
/-! ## 规范 Hilbert quotation 单射 -/
/--
规范偶/奇命名下，任意可编号单排序签名的 Hilbert 核公式到原始 token 树的
quotation 是单射。
-/
private theorem quote_hilbert_token_tree_with?_canonical_injective
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ] (depth : Nat)
    {left right : Formula σ}
    {leftTree rightTree : RawHilbertTokenTree} (hLeft :
      quote_hilbert_token_tree_with?
          free_name bound_name (canonical_bound_names depth)
          depth left =
        some leftTree) (hRight :
      quote_hilbert_token_tree_with?
          free_name bound_name (canonical_bound_names depth)
          depth right =
        some rightTree) (hTrees : leftTree = rightTree) :
    left = right := by
  induction left generalizing
      depth right leftTree rightTree with
  | falsum =>
      simp [quote_hilbert_token_tree_with?] at hLeft
  | truth =>
      simp [quote_hilbert_token_tree_with?] at hLeft
  | rel leftRelation leftArguments =>
      have hRootTags :=
        quote_hilbert_token_tree_with?_formula_root_tag_eq
          free_name bound_name (canonical_bound_names depth)
          depth hLeft hRight hTrees
      cases right <;>
        simp [hilbert_formula_root_tag?] at hRootTags
      case rel rightRelation rightArguments =>
          rcases
              quote_relation_token_tree_with?_canonical_injective
                depth hLeft hRight hTrees with
            ⟨hRelations, hArguments⟩
          cases hRelations
          cases hArguments
          rfl
  | equal leftTerm rightTerm =>
      have hRootTags :=
        quote_hilbert_token_tree_with?_formula_root_tag_eq
          free_name bound_name (canonical_bound_names depth)
          depth hLeft hRight hTrees
      cases right <;>
        simp [hilbert_formula_root_tag?] at hRootTags
      case equal targetLeftTerm targetRightTerm =>
          cases hLeftTerm :
              quote_term_token_tree_with?
                free_name (canonical_bound_names depth)
                leftTerm with
          | none =>
              simp [quote_hilbert_token_tree_with?,
                hLeftTerm] at hLeft
          | some leftTermTree =>
              cases hRightTerm :
                  quote_term_token_tree_with?
                    free_name (canonical_bound_names depth)
                    rightTerm with
              | none =>
                  simp [quote_hilbert_token_tree_with?,
                    hLeftTerm, hRightTerm] at hLeft
              | some rightTermTree =>
                  have hLeftTree :
                      RawHilbertTokenTree.equality
                          leftTermTree rightTermTree =
                        leftTree := by
                    simpa [quote_hilbert_token_tree_with?,
                      hLeftTerm, hRightTerm] using hLeft
                  cases hTargetLeftTerm :
                      quote_term_token_tree_with?
                        free_name (canonical_bound_names depth)
                        targetLeftTerm with
                  | none =>
                      simp [quote_hilbert_token_tree_with?,
                        hTargetLeftTerm] at hRight
                  | some targetLeftTermTree =>
                      cases hTargetRightTerm :
                          quote_term_token_tree_with?
                            free_name (canonical_bound_names depth)
                            targetRightTerm with
                      | none =>
                          simp [quote_hilbert_token_tree_with?,
                            hTargetLeftTerm,
                            hTargetRightTerm] at hRight
                      | some targetRightTermTree =>
                          have hRightTree :
                              RawHilbertTokenTree.equality
                                  targetLeftTermTree
                                  targetRightTermTree =
                                rightTree := by
                            simpa [
                              quote_hilbert_token_tree_with?,
                              hTargetLeftTerm,
                              hTargetRightTerm] using hRight
                          have hNodes :
                              RawHilbertTokenTree.equality
                                  leftTermTree
                                  rightTermTree =
                                RawHilbertTokenTree.equality
                                  targetLeftTermTree
                                  targetRightTermTree :=
                            hLeftTree.trans (hTrees.trans hRightTree.symm)
                          injection hNodes with
                            hLeftTermTrees
                            hRightTermTrees
                          have hLeftTerms :
                              leftTerm = targetLeftTerm :=
                            quote_term_token_tree_with?_canonical_injective
                              depth hLeftTerm
                              hTargetLeftTerm
                              hLeftTermTrees
                          have hRightTerms :
                              rightTerm = targetRightTerm :=
                            quote_term_token_tree_with?_canonical_injective
                              depth hRightTerm
                              hTargetRightTerm
                              hRightTermTrees
                          cases hLeftTerms
                          cases hRightTerms
                          rfl
  | neg body ih =>
      have hRootTags :=
        quote_hilbert_token_tree_with?_formula_root_tag_eq
          free_name bound_name (canonical_bound_names depth)
          depth hLeft hRight hTrees
      cases right <;>
        simp [hilbert_formula_root_tag?] at hRootTags
      case neg targetBody =>
          cases hBody :
              quote_hilbert_token_tree_with?
                free_name bound_name (canonical_bound_names depth)
                depth body with
          | none =>
              simp [quote_hilbert_token_tree_with?,
                hBody] at hLeft
          | some bodyTree =>
              have hLeftTree :
                  RawHilbertTokenTree.negation bodyTree =
                    leftTree := by
                simpa [quote_hilbert_token_tree_with?,
                  hBody] using hLeft
              cases hTargetBody :
                  quote_hilbert_token_tree_with?
                    free_name bound_name (canonical_bound_names depth)
                    depth targetBody with
              | none =>
                  simp [quote_hilbert_token_tree_with?,
                    hTargetBody] at hRight
              | some targetBodyTree =>
                  have hRightTree :
                      RawHilbertTokenTree.negation
                          targetBodyTree =
                        rightTree := by
                    simpa [quote_hilbert_token_tree_with?,
                      hTargetBody] using hRight
                  have hNodes :
                      RawHilbertTokenTree.negation bodyTree =
                        RawHilbertTokenTree.negation
                          targetBodyTree :=
                    hLeftTree.trans (hTrees.trans hRightTree.symm)
                  injection hNodes with hBodyTrees
                  have hBodies : body = targetBody :=
                    ih depth hBody hTargetBody hBodyTrees
                  cases hBodies
                  rfl
  | conj left right =>
      simp [quote_hilbert_token_tree_with?] at hLeft
  | disj left right =>
      simp [quote_hilbert_token_tree_with?] at hLeft
  | imp sourceLeft sourceRight ihLeft ihRight =>
      have hRootTags :=
        quote_hilbert_token_tree_with?_formula_root_tag_eq
          free_name bound_name (canonical_bound_names depth)
          depth hLeft hRight hTrees
      cases right <;>
        simp [hilbert_formula_root_tag?] at hRootTags
      case imp targetLeft targetRight =>
          cases hSourceLeft :
              quote_hilbert_token_tree_with?
                free_name bound_name (canonical_bound_names depth)
                depth sourceLeft with
          | none =>
              simp [quote_hilbert_token_tree_with?,
                hSourceLeft] at hLeft
          | some sourceLeftTree =>
              cases hSourceRight :
                  quote_hilbert_token_tree_with?
                    free_name bound_name (canonical_bound_names depth)
                    depth sourceRight with
              | none =>
                  simp [quote_hilbert_token_tree_with?,
                    hSourceLeft, hSourceRight] at hLeft
              | some sourceRightTree =>
                  have hLeftTree :
                      RawHilbertTokenTree.implication
                          sourceLeftTree
                          sourceRightTree =
                        leftTree := by
                    simpa [quote_hilbert_token_tree_with?,
                      hSourceLeft, hSourceRight] using hLeft
                  cases hTargetLeft :
                      quote_hilbert_token_tree_with?
                        free_name bound_name (canonical_bound_names depth)
                        depth targetLeft with
                  | none =>
                      simp [quote_hilbert_token_tree_with?,
                        hTargetLeft] at hRight
                  | some targetLeftTree =>
                      cases hTargetRight :
                          quote_hilbert_token_tree_with?
                            free_name bound_name (canonical_bound_names depth)
                            depth targetRight with
                      | none =>
                          simp [quote_hilbert_token_tree_with?,
                            hTargetLeft,
                            hTargetRight] at hRight
                      | some targetRightTree =>
                          have hRightTree :
                              RawHilbertTokenTree.implication
                                  targetLeftTree
                                  targetRightTree =
                                rightTree := by
                            simpa [
                              quote_hilbert_token_tree_with?,
                              hTargetLeft,
                              hTargetRight] using hRight
                          have hNodes :
                              RawHilbertTokenTree.implication
                                  sourceLeftTree
                                  sourceRightTree =
                                RawHilbertTokenTree.implication
                                  targetLeftTree
                                  targetRightTree :=
                            hLeftTree.trans (hTrees.trans hRightTree.symm)
                          injection hNodes with
                            hLeftTrees hRightTrees
                          have hLeftFormulas :
                              sourceLeft = targetLeft :=
                            ihLeft depth
                              hSourceLeft hTargetLeft
                              hLeftTrees
                          have hRightFormulas :
                              sourceRight = targetRight :=
                            ihRight depth
                              hSourceRight hTargetRight
                              hRightTrees
                          cases hLeftFormulas
                          cases hRightFormulas
                          rfl
  | iff left right =>
      simp [quote_hilbert_token_tree_with?] at hLeft
  | forallE sort body ih =>
      have hRootTags :=
        quote_hilbert_token_tree_with?_formula_root_tag_eq
          free_name bound_name (canonical_bound_names depth)
          depth hLeft hRight hTrees
      cases right <;>
        simp [hilbert_formula_root_tag?] at hRootTags
      case forallE targetSort targetBody =>
          cases hBody :
              quote_hilbert_token_tree_with?
                free_name bound_name (bound_name depth ::
                  canonical_bound_names depth) (depth + 1) body with
          | none =>
              simp [quote_hilbert_token_tree_with?,
                hBody] at hLeft
          | some bodyTree =>
              have hLeftTree :
                  RawHilbertTokenTree.universal (Numbered.variable_token (bound_name depth))
                      bodyTree =
                    leftTree := by
                simpa [quote_hilbert_token_tree_with?,
                  hBody] using hLeft
              cases hTargetBody :
                  quote_hilbert_token_tree_with?
                    free_name bound_name (bound_name depth ::
                      canonical_bound_names depth) (depth + 1) targetBody with
              | none =>
                  simp [quote_hilbert_token_tree_with?,
                    hTargetBody] at hRight
              | some targetBodyTree =>
                  have hRightTree :
                      RawHilbertTokenTree.universal (Numbered.variable_token (bound_name depth))
                          targetBodyTree =
                        rightTree := by
                    simpa [quote_hilbert_token_tree_with?,
                      hTargetBody] using hRight
                  have hNodes :
                      RawHilbertTokenTree.universal (Numbered.variable_token (bound_name depth))
                          bodyTree =
                        RawHilbertTokenTree.universal (Numbered.variable_token (bound_name depth))
                          targetBodyTree :=
                    hLeftTree.trans (hTrees.trans hRightTree.symm)
                  injection hNodes with
                    _hBinderTokens hBodyTrees
                  have hBodyCanonical :
                      quote_hilbert_token_tree_with?
                          free_name bound_name (canonical_bound_names (depth + 1)) (depth + 1) body =
                        some bodyTree := by
                    simpa [canonical_bound_names]
                      using hBody
                  have hTargetBodyCanonical :
                      quote_hilbert_token_tree_with?
                          free_name bound_name (canonical_bound_names (depth + 1)) (depth + 1) targetBody =
                        some targetBodyTree := by
                    simpa [canonical_bound_names]
                      using hTargetBody
                  have hBodies : body = targetBody :=
                    ih (depth + 1)
                      hBodyCanonical
                      hTargetBodyCanonical
                      hBodyTrees
                  have hSorts : sort = targetSort := (numbering.sort_eq_object sort).trans (numbering.sort_eq_object
                        targetSort).symm
                  cases hSorts
                  cases hBodies
                  rfl
  | existsE sort body =>
      simp [quote_hilbert_token_tree_with?] at hLeft
/--
规范 `quote_tokens?` 对可编号单排序签名的 Hilbert quotation 等价类单射。
两个成功 quotation 的扁平 token 串相等，就能反演出它们的 Hilbert 核相等。该接口
刻意以任意 `QuotationNumbering` 为参数，供集合论扩展签名与后续证明码反向表示共用。
-/
theorem quote_tokens?_some_injective
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ]
    [DecidableEq σ.SortSymbol]
    {left right : Formula σ}
    {leftTokens rightTokens : List Nat} (hLeft :
      Numbered.quote_tokens? left = some leftTokens) (hRight :
      Numbered.quote_tokens? right = some rightTokens) (hTokens : leftTokens = rightTokens) :
    Formula.hilbertize numbering.objectSort left =
      Formula.hilbertize numbering.objectSort right := by
  simp only [
    Numbered.quote_tokens?,
    Numbered.quote_tokens_with?] at hLeft hRight
  rw [
    quote_hilbert_tokens_with?_eq_generic_token_tree] at hLeft hRight
  cases hLeftTree :
      quote_hilbert_token_tree_with?
        free_name bound_name [] 0 (Formula.hilbertize numbering.objectSort left) with
  | none =>
      simp [hLeftTree] at hLeft
  | some leftTree =>
      cases hRightTree :
          quote_hilbert_token_tree_with?
            free_name bound_name [] 0 (Formula.hilbertize numbering.objectSort right) with
      | none =>
          simp [hRightTree] at hRight
      | some rightTree =>
          have hLeftTokens :
              leftTree.tokens = leftTokens := by
            simpa [hLeftTree] using hLeft
          have hRightTokens :
              rightTree.tokens = rightTokens := by
            simpa [hRightTree] using hRight
          have hLeftSeparated :
              leftTree.LexicallySeparated :=
            quote_hilbert_token_tree_with?_lexically_separated
              free_name bound_name [] 0 hLeftTree
          have hRightSeparated :
              rightTree.LexicallySeparated :=
            quote_hilbert_token_tree_with?_lexically_separated
              free_name bound_name [] 0 hRightTree
          have hTreeTokens :
              leftTree.tokens = rightTree.tokens :=
            hLeftTokens.trans (hTokens.trans hRightTokens.symm)
          have hTrees : leftTree = rightTree :=
            RawHilbertTokenTree.tokens_injective
              hLeftSeparated hRightSeparated hTreeTokens
          have hLeftCanonical :
              quote_hilbert_token_tree_with?
                  free_name bound_name (canonical_bound_names 0) 0 (Formula.hilbertize
                    numbering.objectSort left) =
                some leftTree := by
            simpa [canonical_bound_names] using hLeftTree
          have hRightCanonical :
              quote_hilbert_token_tree_with?
                  free_name bound_name (canonical_bound_names 0) 0 (Formula.hilbertize
                    numbering.objectSort right) =
                some rightTree := by
            simpa [canonical_bound_names] using hRightTree
          exact
            quote_hilbert_token_tree_with?_canonical_injective
              0 hLeftCanonical hRightCanonical hTrees

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
