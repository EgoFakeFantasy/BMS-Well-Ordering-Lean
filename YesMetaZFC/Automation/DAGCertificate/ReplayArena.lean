import YesMetaZFC.Automation.DAGCertificate.LinearReplay
import YesMetaZFC.Automation.Data.CertificateBlob

/-!
# DAG 连续回放竞技场

本层用单个 `ByteArray` 保存 DAG 的线性回放日程。节点值只保留在唯一的 DAG 输入中；
竞技场只保存定宽结构字段和顺序父边，不复制节点对象或证明树。

布局：

* 20 字节总头：magic、版本、总字节数、节点数和根编号；
* 每节点 28 字节定宽头；
* 节点头之后紧跟该节点的全部 32 位父编号；
* 最后一个父编号之后必须恰好到达 `blob.size`。

因此 `blob.size - offset` 同时是解析燃料。每个节点至少消耗 28 字节，每条父边再消耗
4 字节；检查器不构造 slice、cursor 对象或临时数组。
-/

namespace YesMetaZFC
namespace Automation
namespace DAGCertificate
namespace DAG
namespace ReplayArena

open Data.CertificateBlob

variable {σ : Signature}

private def ra_magic : UInt32 := 0x52415659
private def ra_version : UInt16 := 1
def ra_headerBytes : Nat := 20
def ra_nodeFixedBytes : Nat := 28

@[inline]
def ra_payloadTag : Payload σ → UInt8
  | .source _ => 0
  | .avatarSplit _ => 1
  | .avatarComponent _ => 2
  | .localRule _ => 3
  | .theoryConflict _ => 4
  | .propositionalLearnedClause _ => 5
  | .residualCdcl _ => 6

@[inline]
def ra_nodeBytes (node : @& Node σ) : Nat :=
  ra_nodeFixedBytes + 4 * node.parents.size

def ra_encodedBytes (dag : DAG σ) : Nat :=
  dag.nodes.foldl (fun total node => total + ra_nodeBytes node)
    ra_headerBytes

@[inline]
def ra_fitsU32 (value : Nat) : Bool :=
  value < 4294967296

private def ra_parentsEncodable (parents : @& Array NodeId) : Bool :=
  parents.all ra_fitsU32

private def ra_nodeEncodable (node : @& Node σ) : Bool :=
  ra_fitsU32 node.id &&
    ra_fitsU32 node.parents.size &&
      ra_fitsU32 node.guards.size &&
        ra_fitsU32 node.conclusion.literals.size &&
          ra_fitsU32 node.ruleTags.size &&
            ra_fitsU32 (ra_nodeBytes node) &&
              ra_parentsEncodable node.parents

private def ra_pushHeaderFields
    (encodedBytes nodeCount root : Nat) (blob : Blob) : Blob :=
  let blob := Builder.pushU32LE blob ra_magic
  let blob := Builder.pushU16LE blob ra_version
  let blob := Builder.pushU16LE blob (UInt16.ofNat ra_headerBytes)
  let blob := Builder.pushU32LE blob (UInt32.ofNat encodedBytes)
  let blob := Builder.pushU32LE blob (UInt32.ofNat nodeCount)
  Builder.pushU32LE blob (UInt32.ofNat root)

private def ra_pushParents (blob : Blob) (parents : @& Array NodeId) : Blob :=
  parents.foldl (fun out parent =>
    Builder.pushU32LE out (UInt32.ofNat parent)) blob

private def ra_pushNode (blob : Blob) (node : @& Node σ) : Blob :=
  let blob := Builder.pushU32LE blob (UInt32.ofNat (ra_nodeBytes node))
  let blob := Builder.pushU32LE blob (UInt32.ofNat node.id)
  let blob := Builder.pushU32LE blob (UInt32.ofNat node.parents.size)
  let blob := Builder.pushU32LE blob (UInt32.ofNat node.guards.size)
  let blob :=
    Builder.pushU32LE blob (UInt32.ofNat node.conclusion.literals.size)
  let blob := Builder.pushU32LE blob (UInt32.ofNat node.ruleTags.size)
  let blob := Builder.pushU8 blob (ra_payloadTag node.payload)
  let blob := Builder.pushU8 blob 0
  let blob := Builder.pushU8 blob 0
  let blob := Builder.pushU8 blob 0
  ra_pushParents blob node.parents

/--
增量 Arena 编码器。

调用者先给出精确总字节数、节点数和稠密根编号，随后在材料化节点的同一循环中顺序
写入节点记录。状态只拥有唯一字节块、三个自然数标量与有效位，不保留节点副本。
-/
structure Encoder where
  blob : Blob
  expectedBytes : Nat
  expectedNodes : Nat
  emittedNodes : Nat
  valid : Bool

namespace Encoder

def start? (expectedBytes expectedNodes root : Nat) : Option Encoder :=
  if ra_fitsU32 expectedBytes &&
      ra_fitsU32 expectedNodes &&
        ra_fitsU32 root then
    if ra_headerBytes <= expectedBytes then
      let blob :=
        ra_pushHeaderFields expectedBytes expectedNodes root
          (Builder.empty expectedBytes)
      some {
        blob := blob
        expectedBytes := expectedBytes
        expectedNodes := expectedNodes
        emittedNodes := 0
        valid := true
      }
    else
      none
  else
    none

def push (encoder : Encoder) (node : @& Node σ) : Encoder :=
  if !encoder.valid then
    encoder
  else if encoder.emittedNodes < encoder.expectedNodes then
    if ra_nodeEncodable node then
      if encoder.blob.size + ra_nodeBytes node <= encoder.expectedBytes then
        {
          encoder with
          blob := ra_pushNode encoder.blob node
          emittedNodes := encoder.emittedNodes + 1
        }
      else
        { encoder with valid := false }
    else
      { encoder with valid := false }
  else
    { encoder with valid := false }

def finish? (encoder : Encoder) : Option Blob :=
  if encoder.valid &&
      encoder.emittedNodes == encoder.expectedNodes &&
      encoder.blob.size == encoder.expectedBytes then
    some encoder.blob
  else
    none

end Encoder

private def ra_readU16Nat (blob : @& Blob) (offset : Nat)
    (hRead : offset + 2 <= blob.size) : UInt16 :=
  let b0 := blob.get offset (by omega)
  let b1 := blob.get (offset + 1) (by omega)
  b0.toUInt16 ||| (b1.toUInt16 <<< 8)

private def ra_readU32Nat (blob : @& Blob) (offset : Nat)
    (hRead : offset + 4 <= blob.size) : UInt32 :=
  let b0 := blob.get offset (by omega)
  let b1 := blob.get (offset + 1) (by omega)
  let b2 := blob.get (offset + 2) (by omega)
  let b3 := blob.get (offset + 3) (by omega)
  b0.toUInt32 |||
    (b1.toUInt32 <<< 8) |||
      (b2.toUInt32 <<< 16) |||
        (b3.toUInt32 <<< 24)

private def ra_headerCheck (dag : @& DAG σ) (blob : @& Blob) : Bool :=
  if hRead : ra_headerBytes <= blob.size then
    have hHeader : 20 <= blob.size := by
      simpa [ra_headerBytes] using hRead
    ra_readU32Nat blob 0 (by omega) == ra_magic &&
      ra_readU16Nat blob 4 (by omega) == ra_version &&
        ra_readU16Nat blob 6 (by omega) == UInt16.ofNat ra_headerBytes &&
          (ra_readU32Nat blob 8 (by omega)).toNat == blob.size &&
            (ra_readU32Nat blob 12 (by omega)).toNat == dag.nodes.size &&
              (ra_readU32Nat blob 16 (by omega)).toNat == dag.root
  else
    false

private def ra_parentRecordsCheck
    (blob : @& Blob) (parents : @& Array NodeId) :
    Nat → Nat → Bool
  | _, 0 => true
  | offset, remaining + 1 =>
      let slot := parents.size - (remaining + 1)
      if hSlot : slot < parents.size then
        if hRead : offset + 4 <= blob.size then
          let parent := parents[slot]
          ra_fitsU32 parent &&
            (ra_readU32Nat blob offset hRead).toNat == parent &&
              ra_parentRecordsCheck blob parents (offset + 4) remaining
        else
          false
      else
        false

private def ra_nodeRecordCheck
    (blob : @& Blob) (offset : Nat) (node : @& Node σ) : Bool :=
  if hRead : offset + ra_nodeFixedBytes <= blob.size then
    have hFixed : offset + 28 <= blob.size := by
      simpa [ra_nodeFixedBytes] using hRead
    ra_parentRecordsCheck blob node.parents
        (offset + ra_nodeFixedBytes) node.parents.size &&
      (ra_nodeEncodable node &&
        (ra_readU32Nat blob offset (by omega)).toNat ==
            ra_nodeBytes node &&
          (ra_readU32Nat blob (offset + 4) (by omega)).toNat ==
              node.id &&
            (ra_readU32Nat blob (offset + 8) (by omega)).toNat ==
                node.parents.size &&
              (ra_readU32Nat blob (offset + 12) (by omega)).toNat ==
                  node.guards.size &&
                (ra_readU32Nat blob (offset + 16) (by omega)).toNat ==
                    node.conclusion.literals.size &&
                  (ra_readU32Nat blob (offset + 20) (by omega)).toNat ==
                      node.ruleTags.size &&
                    blob.get (offset + 24) (by omega) ==
                        ra_payloadTag node.payload &&
                      blob.get (offset + 25) (by omega) == 0 &&
                        blob.get (offset + 26) (by omega) == 0 &&
                          blob.get (offset + 27) (by omega) == 0)
  else
    false

private def ra_recordsCheck
    (dag : @& DAG σ) (blob : @& Blob) :
    Nat → Nat → Nat → Bool
  | offset, index, 0 =>
      offset == blob.size && index == dag.nodes.size
  | offset, index, remaining + 1 =>
      if hIndex : index < dag.nodes.size then
        let node := dag.nodes[index]
        ra_nodeRecordCheck blob offset node &&
          ra_recordsCheck dag blob (offset + ra_nodeBytes node)
            (index + 1) remaining
      else
        false

/--
连续内存的安全布局边界。

内核侧只重放固定头和总长度燃料；逐节点定宽记录由生成 C 的游标 checker 完整解析，
rich 节点语义则由 `LinearReplay.arenaNodesChecked` 的融合扫描负责。
-/
@[noinline]
def layoutCheck (dag : @& DAG σ) (blob : @& Blob) : Bool :=
  ra_headerCheck dag blob &&
    blob.size == ra_encodedBytes dag

/--
连续竞技场的安全参考 checker。

生成代码随后由等型 `USize` 实现承接；本定义保留给内核归约和 soundness 证明。
-/
@[noinline]
def checkFor
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (includeAvatar : Bool)
    (dag : @& DAG σ) (blob : @& Blob) : Bool :=
  layoutCheck dag blob &&
    dag.rootExists &&
      dag.rootClosed &&
        dag.denseIds &&
          dag.parentsBefore &&
            LinearReplay.arenaNodesChecked includeAvatar dag

/-- 连续竞技场的完整宿主审计，额外拒绝 source 键非规范的证书。 -/
@[noinline]
def audit
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (dag : @& DAG σ) (blob : @& Blob) : Bool :=
  checkFor dag.avatarSoundnessSupported dag blob &&
    dag.sourceIndicesUnique

/-!
运行时实现只借用 DAG 与唯一字节块。安全定义中的 `List` 递归保留为证明参考语义；
生成代码则直接以 `USize` 游标扫描原数组，避免节点和父边脊柱的物化及其 RC 流量。
-/

@[inline]
private unsafe def ra_headerCheckImpl
    (dag : @& DAG σ) (blob : @& Blob) : Bool :=
  if blob.usize < 20 then
    false
  else
    ra_fitsU32 blob.size &&
      ra_fitsU32 dag.nodes.size &&
        ra_fitsU32 dag.root &&
          readU32LE blob 0 lcProof == ra_magic &&
            readU16LE blob 4 lcProof == ra_version &&
              readU16LE blob 6 lcProof == UInt16.ofNat ra_headerBytes &&
                readU32LE blob 8 lcProof == UInt32.ofNat blob.size &&
                  readU32LE blob 12 lcProof ==
                      UInt32.ofNat dag.nodes.size &&
                    readU32LE blob 16 lcProof == UInt32.ofNat dag.root

@[inline]
private unsafe def ra_parentRecordsCheckImpl
    (blob : @& Blob) (offset index : USize)
    (parents : @& Array NodeId) : Bool :=
  let stop := parents.size.toUSize
  let blobStop := blob.usize
  let rec loop (cursor slot : USize) : Bool :=
    if slot == stop then
      true
    else if cursor <= blobStop && 4 <= blobStop - cursor then
      let parent := parents.uget slot lcProof
      ra_fitsU32 parent &&
        readU32LE blob cursor lcProof == UInt32.ofNat parent &&
          parent.toUSize < index &&
            loop (cursor + 4) (slot + 1)
    else
      false
  loop offset 0

@[inline]
private unsafe def ra_nodeRecordCheckImpl
    (blob : @& Blob) (offset index : USize)
    (node : @& Node σ) : Bool :=
  let blobStop := blob.usize
  if offset <= blobStop && 28 <= blobStop - offset then
    let parentCount := node.parents.size
    let guardCount := node.guards.size
    let literalCount := node.conclusion.literals.size
    let ruleTagCount := node.ruleTags.size
    let recordBytes := ra_nodeFixedBytes + 4 * parentCount
    ra_fitsU32 node.id &&
      node.id.toUSize == index &&
        ra_parentRecordsCheckImpl blob (offset + 28) index node.parents &&
          ra_fitsU32 parentCount &&
            ra_fitsU32 guardCount &&
              ra_fitsU32 literalCount &&
                ra_fitsU32 ruleTagCount &&
                  ra_fitsU32 recordBytes &&
                    readU32LE blob offset lcProof ==
                        UInt32.ofNat recordBytes &&
                      readU32LE blob (offset + 4) lcProof ==
                          UInt32.ofNat node.id &&
                        readU32LE blob (offset + 8) lcProof ==
                            UInt32.ofNat parentCount &&
                          readU32LE blob (offset + 12) lcProof ==
                              UInt32.ofNat guardCount &&
                            readU32LE blob (offset + 16) lcProof ==
                                UInt32.ofNat literalCount &&
                              readU32LE blob (offset + 20) lcProof ==
                                  UInt32.ofNat ruleTagCount &&
                                readU8 blob (offset + 24) lcProof ==
                                    ra_payloadTag node.payload &&
                                  readU8 blob (offset + 25) lcProof == 0 &&
                                    readU8 blob (offset + 26) lcProof == 0 &&
                                      readU8 blob (offset + 27) lcProof == 0
  else
    false

@[noinline]
private unsafe def ra_recordsCheckImpl
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (includeAvatar : Bool)
    (dag : @& DAG σ) (blob : @& Blob) : Bool :=
  let nodes := dag.nodes
  let stop := nodes.size.toUSize
  let rec loop (offset index : USize) : Bool :=
    if index == stop then
      offset == blob.usize
    else
      let node := nodes.uget index lcProof
      let nextOffset :=
        offset + (ra_nodeFixedBytes + 4 * node.parents.size).toUSize
      ra_nodeRecordCheckImpl blob offset index node &&
        LinearReplay.arenaNodeCheck includeAvatar dag node &&
          loop nextOffset (index + 1)
  loop ra_headerBytes.toUSize 0

/--
显式模式的 native Arena checker。

`native_decide`/`nativeEqTrue` 必须对 `checkFor` 本身运行，才能让默认回放直接得到
后续 AVATAR 字段恢复所需的同一条真值。安全定义仍由 Lean 完整证明；本实现只承担
生成代码中的连续游标扫描。
-/
@[noinline]
private unsafe def checkForImpl
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (includeAvatar : Bool)
    (dag : @& DAG σ) (blob : @& Blob) : Bool :=
  ra_headerCheckImpl dag blob &&
    dag.rootExists &&
      dag.rootClosed &&
        ra_recordsCheckImpl includeAvatar dag blob

attribute [implemented_by checkForImpl] checkFor

@[noinline]
unsafe def auditImpl
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (dag : @& DAG σ) (blob : @& Blob) : Bool :=
  checkForImpl dag.avatarSoundnessSupported dag blob &&
    dag.sourceIndicesUnique

attribute [implemented_by auditImpl] audit

private theorem ra_checkFor_fields
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {includeAvatar : Bool}
    {dag : DAG σ} {blob : Blob}
    (hCheck : checkFor includeAvatar dag blob = true) :
    (((((layoutCheck dag blob = true ∧ dag.rootExists = true) ∧
          dag.rootClosed = true) ∧ dag.denseIds = true) ∧
      dag.parentsBefore = true) ∧
      LinearReplay.arenaNodesChecked includeAvatar dag = true) := by
  simpa [checkFor] using hCheck

/-!
固定数量的阶段真值组合为连续竞技场 checker 真值。
`includeAvatar` 已在宿主阶段决定，避免每个节点重复规约整张 DAG 的能力标记。
-/
theorem checkFor_eq_true_of_components
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (includeAvatar : Bool)
    (dag : DAG σ) (blob : Blob)
    (hLayout : layoutCheck dag blob = true)
    (hRootExists : dag.rootExists = true)
    (hRootClosed : dag.rootClosed = true)
    (hDenseIds : dag.denseIds = true)
    (hParentsBefore : dag.parentsBefore = true)
    (hNodes : LinearReplay.arenaNodesChecked includeAvatar dag = true) :
    checkFor includeAvatar dag blob = true := by
  simp [checkFor, hLayout, hRootExists, hRootClosed, hDenseIds,
    hParentsBefore, hNodes]

/- 固定模式位的 checker 真值直接产生完整 DAG 合同。 -/
theorem contract_of_checkFor
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {dag : DAG σ} {blob : Blob}
    {includeAvatar : Bool}
    (hCheck : checkFor includeAvatar dag blob = true) :
    DAG.Contract dag := by
  have hFields := ra_checkFor_fields hCheck
  rcases hFields with
    ⟨⟨⟨⟨⟨hLayout, hRootExists⟩, hRootClosed⟩, hDenseIds⟩,
      hParentsBefore⟩, hNodes⟩
  have hCoreNodes :=
    LinearReplay.nodesChecked_eq_true_of_arenaNodesChecked hNodes
  exact LinearReplay.contract_of_coreCheck <|
    LinearReplay.coreCheck_eq_true_of_components dag
      hRootExists hRootClosed hDenseIds hParentsBefore hCoreNodes

/-- AVATAR 模式的 Arena 真值同时恢复融合节点检查的 AVATAR 字段。 -/
theorem avatarNodesChecked_of_checkFor
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {dag : DAG σ} {blob : Blob}
    (hCheck : checkFor true dag blob = true) :
    LinearReplay.avatarNodesChecked dag = true := by
  exact LinearReplay.avatarNodesChecked_eq_true_of_arenaNodesChecked
    (ra_checkFor_fields hCheck).2

end ReplayArena
end DAG
end DAGCertificate
end Automation
end YesMetaZFC
