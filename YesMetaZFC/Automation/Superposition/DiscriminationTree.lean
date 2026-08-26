import YesMetaZFC.Automation.CoreSyntax
import YesMetaZFC.Automation.Data.Util
/-!
# 超消元词项判别树
本模块提供搜索层词项的完美判别树骨架。判别树只负责候选检索：
它返回的是“可能匹配/可能合一”的保守候选集，真正的 soundness 仍由后续规则检查与
LCF replay 承担。
-/
namespace YesMetaZFC
namespace Automation
namespace Superposition
namespace DiscriminationTree
abbrev Term := CoreSyntax.Search.Term
abbrev SymbolKind := CoreSyntax.Search.SymbolKind
inductive DTToken where
  | wildcard (sort? : Option CoreSyntax.CoreSort)
  | bvar (sort : CoreSyntax.CoreSort) (index : Nat)
  | apply
  | lam (domain codomain : CoreSyntax.CoreSort)
  | sym (kind : SymbolKind) (id arity : Nat)
  deriving Repr, BEq, DecidableEq, Lean.ToExpr
namespace DTToken
def isWildcard : DTToken → Bool
  | wildcard _ => true
  | _ => false
def sortCompatible (left right : Option CoreSyntax.CoreSort) : Bool :=
  match left, right with
  | some leftSort, some rightSort => leftSort == rightSort
  | _, _ => true
def canMatch (query indexed : DTToken) : Bool :=
  match query, indexed with
  | wildcard querySort, wildcard indexedSort => sortCompatible querySort indexedSort
  | wildcard querySort, bvar sort _ => sortCompatible querySort (some sort)
  | wildcard querySort, apply => sortCompatible querySort none
  | wildcard querySort, lam domain codomain => sortCompatible querySort (some (CoreSyntax.CoreSort.arrow domain codomain))
  | wildcard querySort, sym .. => sortCompatible querySort none
  | bvar sort index, bvar sort' index' => sort == sort' && index == index'
  | apply, apply => true
  | lam domain codomain, lam domain' codomain' => domain == domain' && codomain == codomain'
  | sym kind id arity, sym kind' id' arity' => kind == kind' && id == id' && arity == arity'
  | _, _ => false
end DTToken
abbrev TermPath := Array DTToken
namespace TermPath
def summary (path : TermPath) : String :=
  s!"tokens={path.size}"
def containsWildcard (path : TermPath) : Bool :=
  path.any DTToken.isWildcard
end TermPath
def termSort? (term : Term) : Option CoreSyntax.CoreSort :=
  term.inferSort?
def wildcardToken (sort? : Option CoreSyntax.CoreSort) : DTToken :=
  DTToken.wildcard sort?
mutual
  partial def encodeArgs (args : List Term) (out : TermPath) : TermPath :=
    match args with
    | [] => out
    | arg :: rest => encodeArgs rest (encodeTermInto arg out)
  /--
  把搜索词项编码成判别树路径。
  应用和 λ 保留各自 token；函数符号保留 kind/id/arity，随后顺序展开参数。
  -/
  partial def encodeTermInto (term : Term) (out : TermPath) : TermPath :=
    match term with
    | CoreSyntax.Search.Term.var _ => out.push (wildcardToken (termSort? term))
    | CoreSyntax.Search.Term.bvar sort index => out.push (DTToken.bvar sort index)
    | CoreSyntax.Search.Term.fvar sort _ => out.push (wildcardToken (some sort))
    | CoreSyntax.Search.Term.app symbol args =>
        encodeArgs args (out.push (DTToken.sym symbol.kind symbol.id symbol.arity))
    | CoreSyntax.Search.Term.apply fn arg =>
        encodeTermInto arg (encodeTermInto fn (out.push DTToken.apply))
    | CoreSyntax.Search.Term.lam domain codomain body =>
        encodeTermInto body (out.push (DTToken.lam domain codomain))
end
def encodeTerm (term : Term) : TermPath :=
  encodeTermInto term #[]
def encodePattern (term : Term) : TermPath :=
  encodeTerm term
structure ArenaNode where
  firstEdge : Nat := 0
  firstWildcard : Nat := 0
  firstPayload : Nat := 0
  lastEdge : Nat := 0
  lastWildcard : Nat := 0
  lastPayload : Nat := 0
  deriving Repr, Inhabited, Lean.ToExpr
structure ArenaEdge where
  parent : Nat
  token : DTToken
  child : Nat
  hashNext : Nat := 0
  nodeNext : Nat := 0
  wildcardNext : Nat := 0
  deriving Repr, Lean.ToExpr
/--
平坦完美判别树。
节点、边、payload 和哈希槽全部连续存放。插入只追加记录并更新少量 1-based 链接，
不再递归复制父节点的 `edges : Array`。
-/
structure PerfectDiscriminationTree (α : Type) where
  nodes : Array ArenaNode := #[{}]
  edges : Array ArenaEdge := #[]
  payloads : Array α := #[]
  payloadNext : Array Nat := #[]
  hashSlots : Array Nat := Data.filledArray 16 0
  deriving Repr, Lean.ToExpr
namespace PerfectDiscriminationTree
variable {α : Type}
def empty : PerfectDiscriminationTree α := {}
@[inline]
def rootNode : Nat := 1
@[inline]
def node? (tree : PerfectDiscriminationTree α) (id : Nat) : Option ArenaNode :=
  if id == 0 then none else tree.nodes[id - 1]?
@[inline]
def edge? (tree : PerfectDiscriminationTree α) (id : Nat) : Option ArenaEdge :=
  if id == 0 then none else tree.edges[id - 1]?
partial def hashSort : CoreSyntax.CoreSort → UInt64
  | CoreSyntax.CoreSort.object => 3
  | CoreSyntax.CoreSort.bool => 5
  | CoreSyntax.CoreSort.prop => 7
  | CoreSyntax.CoreSort.named id => mixHash 11 (Hashable.hash id)
  | CoreSyntax.CoreSort.arrow domain codomain =>
      mixHash 13 (mixHash (hashSort domain) (hashSort codomain))
def hashToken : DTToken → UInt64
  | DTToken.wildcard sort? =>
      mixHash 17 <| match sort? with
        | some sort => hashSort sort
        | none => 0
  | DTToken.bvar sort index => mixHash 19 (mixHash (hashSort sort) (Hashable.hash index))
  | DTToken.apply => 29
  | DTToken.lam domain codomain =>
      mixHash 31 (mixHash (hashSort domain) (hashSort codomain))
  | DTToken.sym kind id arity =>
      let kindHash := match kind with
        | CoreSyntax.Search.SymbolKind.parameter => 37
        | CoreSyntax.Search.SymbolKind.skolem => 41
        | CoreSyntax.Search.SymbolKind.definition => 43
        | CoreSyntax.Search.SymbolKind.choice => 47
        | CoreSyntax.Search.SymbolKind.builtin => 53
        | CoreSyntax.Search.SymbolKind.extensionalWitness => 59
        | CoreSyntax.Search.SymbolKind.tuple => 61
      mixHash kindHash (mixHash (Hashable.hash id) (Hashable.hash arity))
@[inline]
def edgeHash (parent : Nat) (token : DTToken) : UInt64 :=
  mixHash (Hashable.hash parent) (hashToken token)
@[inline]
def edgeSlot (width parent : Nat) (token : DTToken) : Nat :=
  if width == 0 then 0 else (edgeHash parent token).toNat % width
def rehash (tree : PerfectDiscriminationTree α) (requestedWidth : Nat) :
    PerfectDiscriminationTree α := Id.run do
  let width := Nat.max 16 requestedWidth
  let mut slots := Data.filledArray width 0
  let mut edges := tree.edges
  for index in [:edges.size] do
    match edges[index]? with
    | some edge =>
        let slot := edgeSlot width edge.parent edge.token
        let next := slots[slot]!
        edges := edges.set! index { edge with hashNext := next }
        slots := slots.set! slot (index + 1)
    | none => pure ()
  return { tree with edges := edges, hashSlots := slots }
@[inline]
def ensureHashCapacity (tree : PerfectDiscriminationTree α) :
    PerfectDiscriminationTree α :=
  if tree.hashSlots.isEmpty then
    tree.rehash 16
  else if (tree.edges.size + 1) * 4 >= tree.hashSlots.size * 3 then
    tree.rehash (tree.hashSlots.size * 2)
  else
    tree
partial def findEdgeFrom? (tree : PerfectDiscriminationTree α) (parent : Nat) (token : DTToken) (link : Nat) : Option ArenaEdge :=
  match tree.edge? link with
  | some edge =>
      if edge.parent == parent && edge.token == token then
        some edge
      else
        tree.findEdgeFrom? parent token edge.hashNext
  | none => none
@[inline]
def findEdge? (tree : PerfectDiscriminationTree α) (parent : Nat) (token : DTToken) : Option ArenaEdge :=
  if tree.hashSlots.isEmpty then
    none
  else
    let slot := edgeSlot tree.hashSlots.size parent token
    tree.findEdgeFrom? parent token tree.hashSlots[slot]!
@[inline]
def pushNode (tree : PerfectDiscriminationTree α) : Nat × PerfectDiscriminationTree α :=
  let id := tree.nodes.size + 1
  (id, { tree with nodes := tree.nodes.push {} })
@[inline]
def setNode (tree : PerfectDiscriminationTree α) (id : Nat) (node : ArenaNode) :
    PerfectDiscriminationTree α :=
  if id == 0 || id > tree.nodes.size then
    tree
  else
    { tree with nodes := tree.nodes.set! (id - 1) node }
@[inline]
private def setEdge (tree : PerfectDiscriminationTree α) (id : Nat) (edge : ArenaEdge) :
    PerfectDiscriminationTree α :=
  if id == 0 || id > tree.edges.size then
    tree
  else
    { tree with edges := tree.edges.set! (id - 1) edge }
def pushEdge (tree : PerfectDiscriminationTree α) (parent : Nat) (token : DTToken) (child : Nat) : PerfectDiscriminationTree α :=
  let tree := tree.ensureHashCapacity
  match tree.node? parent with
  | none => tree
  | some parentNode =>
      let slot := edgeSlot tree.hashSlots.size parent token
      let edgeId := tree.edges.size + 1
      let wildcard := token.isWildcard
      let previousLastEdge := parentNode.lastEdge
      let previousLastWildcard := parentNode.lastWildcard
      let edge : ArenaEdge := {
        parent := parent
        token := token
        child := child
        hashNext := tree.hashSlots[slot]!
        nodeNext := 0
        wildcardNext := 0
      }
      let parentNode := {
        parentNode with
        firstEdge := if parentNode.firstEdge == 0 then edgeId else parentNode.firstEdge
        firstWildcard :=
          if wildcard && parentNode.firstWildcard == 0 then edgeId
          else parentNode.firstWildcard
        lastEdge := edgeId
        lastWildcard := if wildcard then edgeId else parentNode.lastWildcard
      }
      let tree := {
        tree with
        edges := tree.edges.push edge
        hashSlots := tree.hashSlots.set! slot edgeId
      }
      let tree :=
        match tree.edge? previousLastEdge with
        | some previous =>
            tree.setEdge previousLastEdge { previous with nodeNext := edgeId }
        | none => tree
      let tree :=
        if wildcard then
          match tree.edge? previousLastWildcard with
          | some previous =>
              tree.setEdge previousLastWildcard {
                previous with wildcardNext := edgeId
              }
          | none => tree
        else
          tree
      tree.setNode parent parentNode
def pushPayload (tree : PerfectDiscriminationTree α) (nodeId : Nat) (payload : α) :
    PerfectDiscriminationTree α :=
  match tree.node? nodeId with
  | none => tree
  | some node =>
      let payloadId := tree.payloads.size + 1
      let tree := {
        tree with
        payloads := tree.payloads.push payload
        payloadNext := tree.payloadNext.push 0
      }
      let tree :=
        if node.lastPayload == 0 then
          tree
        else
          {
            tree with
            payloadNext := tree.payloadNext.set! (node.lastPayload - 1) payloadId
          }
      tree.setNode nodeId {
        node with
        firstPayload := if node.firstPayload == 0 then payloadId else node.firstPayload
        lastPayload := payloadId
      }
def insertPath (tree : PerfectDiscriminationTree α) (path : TermPath) (payload : α) :
    PerfectDiscriminationTree α :=
  let rec go (tree : PerfectDiscriminationTree α) (nodeId index : Nat) :
      PerfectDiscriminationTree α :=
    if h : index < path.size then
      let token := path[index]
      match tree.findEdge? nodeId token with
      | some edge => go tree edge.child (index + 1)
      | none =>
          let (child, tree) := tree.pushNode
          go (tree.pushEdge nodeId token child) child (index + 1)
    else
      tree.pushPayload nodeId payload
  go tree rootNode 0
def insertTerm (tree : PerfectDiscriminationTree α) (term : Term) (payload : α) :
    PerfectDiscriminationTree α :=
  tree.insertPath (encodeTerm term) payload
/--
按原始插入顺序迭代折叠 payload 链。
链在写入时维护首尾指针，因此 visitor 返回 `done` 后不会继续扫描历史后缀，也不会占用
与链长成比例的原生调用栈。
-/
def foldPayloadLinksUntil {β : Type} (tree : PerfectDiscriminationTree α) (link : Nat) (initial : β) (visit : β → α → Data.FoldStep β) :
    Data.FoldStep β := Id.run do
  let mut link := link
  let mut out := initial
  while link != 0 do
    let next := tree.payloadNext[link - 1]?.getD 0
    match tree.payloads[link - 1]? with
    | some payload =>
        match visit out payload with
        | .done result => return .done result
        | .next state => out := state
    | none => pure ()
    link := next
  return .next out
def foldNodePayloadsUntil {β : Type} (tree : PerfectDiscriminationTree α) (nodeId : Nat) (initial : β) (visit : β → α → Data.FoldStep β) :
    Data.FoldStep β :=
  match tree.node? nodeId with
  | some node => tree.foldPayloadLinksUntil node.firstPayload initial visit
  | none => .next initial
def foldEdgeLinksUntil {β : Type} (tree : PerfectDiscriminationTree α) (link : Nat) (nextLink : ArenaEdge → Nat)
    (initial : β) (visit : β → ArenaEdge → Data.FoldStep β) :
    Data.FoldStep β := Id.run do
  let mut link := link
  let mut out := initial
  while link != 0 do
    match tree.edge? link with
    | some edge =>
        let next := nextLink edge
        match visit out edge with
        | .done result => return .done result
        | .next state => out := state
        link := next
    | none => return .next out
  return .next out
def foldNodeEdgesUntil {β : Type} (tree : PerfectDiscriminationTree α) (nodeId : Nat) (initial : β) (visit : β → ArenaEdge → Data.FoldStep β) :
    Data.FoldStep β :=
  match tree.node? nodeId with
  | some node => tree.foldEdgeLinksUntil node.firstEdge (·.nodeNext) initial visit
  | none => .next initial
def foldWildcardEdgesUntil {β : Type} (tree : PerfectDiscriminationTree α) (nodeId : Nat) (initial : β) (visit : β → ArenaEdge → Data.FoldStep β) :
    Data.FoldStep β :=
  match tree.node? nodeId with
  | some node =>
      tree.foldEdgeLinksUntil node.firstWildcard (·.wildcardNext) initial visit
  | none => .next initial
def tokenChildCount : DTToken → Nat
  | DTToken.apply => 2
  | DTToken.lam .. => 1
  | DTToken.sym _ _ arity => arity
  | _ => 0
/--
从 `nodeId` 开始消费连续 `count` 棵完整子项，返回所有可能的终止节点。
该入口只服务模式 wildcard；普通查询仍通过哈希边直达。
-/
partial def foldTermSequenceEndsUntil {β : Type} (tree : PerfectDiscriminationTree α) (nodeId count : Nat) (initial : β) (visit : β → Nat → Data.FoldStep β) :
    Data.FoldStep β :=
  match count with
  | 0 => visit initial nodeId
  | count + 1 =>
      tree.foldNodeEdgesUntil nodeId initial fun out edge =>
        match
            tree.foldTermSequenceEndsUntil
              edge.child (tokenChildCount edge.token) out fun out afterTerm =>
                tree.foldTermSequenceEndsUntil afterTerm count out visit with
        | .next next => .next next
        | .done result => .done result
mutual
  partial def skipTerm? (path : TermPath) (index : Nat) : Option Nat :=
    if h : index < path.size then
      match path[index] with
      | DTToken.wildcard .. => some (index + 1)
      | DTToken.bvar .. => some (index + 1)
      | DTToken.apply =>
          match skipTerm? path (index + 1) with
          | some next => skipTerm? path next
          | none => none
      | DTToken.lam .. => skipTerm? path (index + 1)
      | DTToken.sym _ _ arity => skipTerms? path (index + 1) arity
    else
      none
  partial def skipTerms? (path : TermPath) (index count : Nat) : Option Nat :=
    match count with
    | 0 => some index
    | count + 1 =>
        match skipTerm? path index with
        | some next => skipTerms? path next count
        | none => none
end
partial def foldMatchedByPathFromUntil {β : Type} (tree : PerfectDiscriminationTree α) (pattern : TermPath) (nodeId index : Nat)
    (initial : β) (visit : β → α → Data.FoldStep β) : Data.FoldStep β :=
  if h : index < pattern.size then
    let token := pattern[index]
    if token.isWildcard then
      tree.foldNodeEdgesUntil nodeId initial fun out edge =>
        if DTToken.canMatch token edge.token then
          tree.foldTermSequenceEndsUntil
            edge.child (tokenChildCount edge.token) out fun out nextNode =>
              tree.foldMatchedByPathFromUntil pattern nextNode (index + 1) out visit
        else
          .next out
    else
      match tree.findEdge? nodeId token with
      | some edge =>
          tree.foldMatchedByPathFromUntil pattern edge.child (index + 1) initial visit
      | none => .next initial
  else
    tree.foldNodePayloadsUntil nodeId initial visit
def foldMatchedByPathUntil {β : Type} (tree : PerfectDiscriminationTree α) (pattern : TermPath) (initial : β) (visit : β → α → Data.FoldStep β) : β :=
  (tree.foldMatchedByPathFromUntil pattern rootNode 0 initial visit).value
def foldMatchedByPath {β : Type} (tree : PerfectDiscriminationTree α) (pattern : TermPath) (initial : β) (visit : β → α → β) : β :=
  tree.foldMatchedByPathUntil pattern initial fun state payload =>
    .next (visit state payload)
def foldMatchedByUntil {β : Type} (tree : PerfectDiscriminationTree α) (pattern : Term) (initial : β) (visit : β → α → Data.FoldStep β) : β :=
  tree.foldMatchedByPathUntil (encodePattern pattern) initial visit
def foldMatchedBy {β : Type} (tree : PerfectDiscriminationTree α) (pattern : Term) (initial : β) (visit : β → α → β) : β :=
  tree.foldMatchedByUntil pattern initial fun state payload =>
    .next (visit state payload)
def appendMatchedByPath (tree : PerfectDiscriminationTree α) (pattern : TermPath) (initial : Array α := #[]) : Array α :=
  tree.foldMatchedByPath pattern initial Array.push
def appendMatchedBy (tree : PerfectDiscriminationTree α) (pattern : Term) (initial : Array α := #[]) : Array α :=
  tree.appendMatchedByPath (encodePattern pattern) initial
/--
查询所有可能匹配目标路径的 indexed pattern。
索引 wildcard 消费目标路径中的一个完整子项；非 wildcard 分支通过 arena 哈希表直达。
-/
partial def foldPatternsMatchingFromUntil {β : Type} (tree : PerfectDiscriminationTree α) (nodeId : Nat) (target : TermPath) (index : Nat)
    (initial : β) (visit : β → α → Data.FoldStep β) : Data.FoldStep β :=
  if h : index < target.size then
    let token := target[index]
    match
        tree.foldWildcardEdgesUntil nodeId initial fun out edge =>
        match skipTerm? target index with
        | some next =>
            tree.foldPatternsMatchingFromUntil edge.child target next out visit
        | none => .next out with
    | .done result => .done result
    | .next out =>
        if token.isWildcard then
          .next out
        else
          match tree.findEdge? nodeId token with
          | some edge =>
              tree.foldPatternsMatchingFromUntil
                edge.child target (index + 1) out visit
          | none => .next out
  else
    tree.foldNodePayloadsUntil nodeId initial visit
def foldPatternsMatchingPathUntil {β : Type} (tree : PerfectDiscriminationTree α) (target : TermPath) (initial : β) (visit : β → α → Data.FoldStep β) : β :=
  (tree.foldPatternsMatchingFromUntil rootNode target 0 initial visit).value
def foldPatternsMatchingPath {β : Type} (tree : PerfectDiscriminationTree α) (target : TermPath) (initial : β) (visit : β → α → β) : β :=
  tree.foldPatternsMatchingPathUntil target initial fun state payload =>
    .next (visit state payload)
def foldPatternsMatchingUntil {β : Type} (tree : PerfectDiscriminationTree α) (target : Term) (initial : β) (visit : β → α → Data.FoldStep β) : β :=
  tree.foldPatternsMatchingPathUntil (encodeTerm target) initial visit
def foldPatternsMatching {β : Type} (tree : PerfectDiscriminationTree α) (target : Term) (initial : β) (visit : β → α → β) : β :=
  tree.foldPatternsMatchingUntil target initial fun state payload =>
    .next (visit state payload)
def appendPatternsMatchingPath (tree : PerfectDiscriminationTree α) (target : TermPath) (initial : Array α := #[]) : Array α :=
  tree.foldPatternsMatchingPath target initial Array.push
def appendPatternsMatching (tree : PerfectDiscriminationTree α) (target : Term) (initial : Array α := #[]) : Array α :=
  tree.appendPatternsMatchingPath (encodeTerm target) initial
/--
近似合一查询。索引 wildcard 消费查询路径中的一个完整子项；普通 token 走精确哈希边。
-/
partial def foldUnifiableApproxFromUntil {β : Type} (tree : PerfectDiscriminationTree α) (nodeId : Nat) (query : TermPath) (index : Nat)
    (initial : β) (visit : β → α → Data.FoldStep β) : Data.FoldStep β :=
  if h : index < query.size then
    let token := query[index]
    match
        tree.foldWildcardEdgesUntil nodeId initial fun out edge =>
        match skipTerm? query index with
        | some next =>
            tree.foldUnifiableApproxFromUntil edge.child query next out visit
        | none => .next out with
    | .done result => .done result
    | .next out =>
        match tree.findEdge? nodeId token with
        | some edge =>
            tree.foldUnifiableApproxFromUntil edge.child query (index + 1) out visit
        | none => .next out
  else
    tree.foldNodePayloadsUntil nodeId initial visit
def foldUnifiableApproxPathUntil {β : Type} (tree : PerfectDiscriminationTree α) (path : TermPath) (initial : β) (visit : β → α → Data.FoldStep β) : β :=
  if path.containsWildcard then
    Data.foldArrayUntil tree.payloads initial visit
  else
    (tree.foldUnifiableApproxFromUntil rootNode path 0 initial visit).value
def foldUnifiableApproxPath {β : Type} (tree : PerfectDiscriminationTree α) (path : TermPath) (initial : β) (visit : β → α → β) : β :=
  tree.foldUnifiableApproxPathUntil path initial fun state payload =>
    .next (visit state payload)
def foldUnifiableApproxUntil {β : Type} (tree : PerfectDiscriminationTree α) (term : Term) (initial : β) (visit : β → α → Data.FoldStep β) : β :=
  tree.foldUnifiableApproxPathUntil (encodeTerm term) initial visit
def foldUnifiableApprox {β : Type} (tree : PerfectDiscriminationTree α) (term : Term) (initial : β) (visit : β → α → β) : β :=
  tree.foldUnifiableApproxUntil term initial fun state payload =>
    .next (visit state payload)
/--
把近似可合一候选追加到同一个数组。
查询自身含 wildcard 时索引必须保守返回全部 payload；空输出可直接复用 arena 数组，
避免逐项复制。
-/
def appendUnifiableApproxPath (tree : PerfectDiscriminationTree α) (path : TermPath) (initial : Array α := #[]) : Array α :=
  if path.containsWildcard then
    if initial.isEmpty then tree.payloads else Data.appendArray initial tree.payloads
  else
    tree.foldUnifiableApproxPath path initial Array.push
def appendUnifiableApprox (tree : PerfectDiscriminationTree α) (term : Term) (initial : Array α := #[]) : Array α :=
  tree.appendUnifiableApproxPath (encodeTerm term) initial
def entries (tree : PerfectDiscriminationTree α) : Array α :=
  tree.payloads
@[inline]
def isEmpty (tree : PerfectDiscriminationTree α) : Bool :=
  tree.payloads.isEmpty
end PerfectDiscriminationTree
end DiscriminationTree
end Superposition
end Automation
end YesMetaZFC
