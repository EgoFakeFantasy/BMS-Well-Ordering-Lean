import YesMetaZFC.Automation.AvatarSoundness
import Std.Data.HashSet.Lemmas
/-!
# AVATAR selector registry 的全局语义闭合
本模块在通用 `CheckedDAG` 之上增加一个 AVATAR 专用可信边界。checker 会复算每个
split 的 literal 覆盖、component 自由变量支持不交和 selector 正性，并检查整张图中
同一个 selector 变量始终指向同一个对象层 component。
通过这层边界后，AVATAR fixed-bound-stack soundness 所需的命题 valuation 与
component/split selector 语义合同都可从 DAG 自动构造，不再由调用者外部提供。
-/
namespace YesMetaZFC
namespace Automation
namespace PropResolution
namespace Clause
theorem satisfies_canonicalClause_iff (valuation : Valuation) (clause : Clause) :
    Satisfies valuation (canonicalClause clause) ↔ Satisfies valuation clause := by
  constructor
  · rintro ⟨literal, hMem, hHolds⟩
    exact
      ⟨literal,
        Guards.mem_of_mem_canonical hMem,
        hHolds⟩
  · rintro ⟨literal, hMem, hHolds⟩
    exact ⟨literal, mem_canonicalClause_of_mem hMem, hHolds⟩
end Clause
end PropResolution
namespace DAGCertificate
universe x
open _root_.YesMetaZFC.Automation
open _root_.YesMetaZFC.Automation.LogicSoundness
namespace Clause
private def partitionIndices (partitions : Array (Array Nat)) : List Nat :=
  partitions.toList.flatMap Array.toList

/--
只按 partition 索引检查 source 覆盖。透明参考定义供内核归约和 soundness 使用；
`atIndices` 自身保证 component 不会产生 source 之外的 literal。
-/
def partitionCoversCheck
    (sourceSize : Nat) (partitions : @& Array (Array Nat)) : Bool :=
  let indices := partitionIndices partitions
  (List.range sourceSize).all indices.contains

private def partitionCoversHashCheck
    (sourceSize : Nat) (partitions : Array (Array Nat)) : Bool :=
  let covered := Std.HashSet.ofList (partitionIndices partitions)
  (List.range sourceSize).all covered.contains

private theorem partitionCoversHashCheck_eq
    (sourceSize : Nat) (partitions : Array (Array Nat)) :
    partitionCoversHashCheck sourceSize partitions =
      partitionCoversCheck sourceSize partitions := by
  unfold partitionCoversHashCheck partitionCoversCheck
  apply List.all_congr rfl
  intro index
  exact Std.HashSet.contains_ofList

/--
生成 C 使用一次建表、逐槽查询的线性期望实现。上面的等价定理把该实现与透明参考
定义闭合在同一布尔语义上；`implemented_by` 只切换运行时代码，不改变内核归约。
-/
@[noinline]
unsafe def partitionCoversCheckImpl
    (sourceSize : Nat) (partitions : @& Array (Array Nat)) : Bool :=
  partitionCoversHashCheck sourceSize partitions

attribute [implemented_by partitionCoversCheckImpl] partitionCoversCheck

theorem partitionCoversCheck_sound {σ : Signature}
    {source : Clause σ} {partitions : Array (Array Nat)}
    (hCheck :
      partitionCoversCheck source.literals.size partitions = true) :
    Covers source
      (partitions.toList.map (Clause.atIndices source)) := by
  let indices := partitionIndices partitions
  have hAll :
      (List.range source.literals.size).all indices.contains = true := by
    simpa [partitionCoversCheck, indices] using hCheck
  constructor
  · intro literal hLiteral
    have hArray : literal ∈ source.literals :=
      Array.mem_def.mpr hLiteral
    rcases Array.mem_iff_getElem?.mp hArray with ⟨index, hGet⟩
    have hIndex : index < source.literals.size :=
      (Array.getElem?_eq_some_iff.mp hGet).1
    have hContains : indices.contains index = true :=
      List.all_eq_true.mp hAll index (List.mem_range.mpr hIndex)
    have hFlat : index ∈ indices :=
      List.contains_iff_mem.mp (by simpa using hContains)
    rcases List.mem_flatMap.mp hFlat with
      ⟨partition, hPartition, hIndexPartition⟩
    refine
      ⟨Clause.atIndices source partition,
        List.mem_map.mpr ⟨partition, hPartition, rfl⟩, ?_⟩
    change
      literal ∈
        (partition.filterMap fun i => source.literals[i]?).toList
    apply Array.mem_def.mp
    exact
      Array.mem_filterMap.mpr
        ⟨index, Array.mem_def.mpr hIndexPartition, hGet⟩
  · intro component hComponent literal hLiteral
    rcases List.mem_map.mp hComponent with
      ⟨partition, _hPartition, rfl⟩
    have hArray :
        literal ∈
          partition.filterMap fun i => source.literals[i]? := by
      exact Array.mem_def.mpr hLiteral
    rcases Array.mem_filterMap.mp hArray with
      ⟨_index, _hIndex, hGet⟩
    exact Array.mem_def.mp (Array.mem_of_getElem? hGet)

def supportsDisjointCheck {σ : Signature}
    [DecidableEq σ.SortSymbol]
    (left right : Logic.FirstOrder.FreeVariable.Support σ) : Bool :=
  left.all fun fv => !right.contains fv

private def pairwiseSupportDisjointReference {σ : Signature}
    [DecidableEq σ.SortSymbol] : List (Clause σ) → Bool
  | [] => true
  | head :: rest =>
      rest.all (fun other =>
          supportsDisjointCheck head.freeSupport other.freeSupport) &&
        pairwiseSupportDisjointReference rest

/--
透明定义只表达数学上的两两支持不交，供内核归约和 soundness 使用。生成 C 会由后面的
单遍 owner registry 实现承接。
-/
@[noinline]
def pairwiseSupportDisjointCheck {σ : Signature}
    [DecidableEq σ.SortSymbol]
    (components : @& List (Clause σ)) : Bool :=
  pairwiseSupportDisjointReference components

theorem supportsDisjointCheck_sound {σ : Signature}
    [DecidableEq σ.SortSymbol]
    {left right : Logic.FirstOrder.FreeVariable.Support σ}
    (hCheck : supportsDisjointCheck left right = true) :
    Logic.FirstOrder.FreeVariable.Support.Disjoint left right := by
  intro fv hLeft hRight
  have hNotMem : ¬fv ∈ right := by
    simpa [supportsDisjointCheck] using
      List.all_eq_true.mp hCheck fv hLeft
  exact hNotMem hRight

private theorem supportsDisjointCheck_complete {σ : Signature}
    [DecidableEq σ.SortSymbol]
    {left right : Logic.FirstOrder.FreeVariable.Support σ}
    (hDisjoint :
      Logic.FirstOrder.FreeVariable.Support.Disjoint left right) :
    supportsDisjointCheck left right = true := by
  apply List.all_eq_true.mpr
  intro fv hLeft
  have hNotMem : ¬fv ∈ right :=
    fun hRight => hDisjoint fv hLeft hRight
  have hContains : right.contains fv = false := by
    exact Bool.eq_false_iff.mpr fun hTrue =>
      hNotMem (List.contains_iff_mem.mp hTrue)
  simpa [hContains]

private theorem pairwiseSupportDisjointReference_sound {σ : Signature}
    [DecidableEq σ.SortSymbol] {components : List (Clause σ)}
    (hCheck : pairwiseSupportDisjointReference components = true) :
    PairwiseSupportDisjoint components := by
  induction components with
  | nil =>
      trivial
  | cons head rest ih =>
      rcases Bool.and_eq_true_iff.mp hCheck with ⟨hHead, hRest⟩
      constructor
      · intro other hOther
        exact supportsDisjointCheck_sound
          (List.all_eq_true.mp hHead other hOther)
      · exact ih hRest

private theorem pairwiseSupportDisjointReference_complete {σ : Signature}
    [DecidableEq σ.SortSymbol] {components : List (Clause σ)}
    (hDisjoint : PairwiseSupportDisjoint components) :
    pairwiseSupportDisjointReference components = true := by
  induction components with
  | nil =>
      rfl
  | cons head rest ih =>
      rcases hDisjoint with ⟨hHead, hRest⟩
      apply Bool.and_eq_true_iff.mpr
      constructor
      · apply List.all_eq_true.mpr
        intro other hOther
        exact supportsDisjointCheck_complete (hHead other hOther)
      · exact ih hRest

private abbrev FreeVariableKey (σ : Signature) :=
  σ.SortSymbol × Logic.FirstOrder.FreeVarId

private instance : Hashable (FreeVariableKey σ) where
  hash key := hash key.2

private def freeVariableKey
    (fv : Logic.FirstOrder.FreeVariable σ) : FreeVariableKey σ :=
  fv

private def insertSupport
    [DecidableEq σ.SortSymbol]
    (owners : Std.HashSet (FreeVariableKey σ)) :
    Logic.FirstOrder.FreeVariable.Support σ →
      Std.HashSet (FreeVariableKey σ)
  | [] => owners
  | fv :: rest =>
      insertSupport (owners.insert (freeVariableKey fv)) rest

private theorem mem_insertSupport_iff
    [DecidableEq σ.SortSymbol]
    {owners : Std.HashSet (FreeVariableKey σ)}
    {support : Logic.FirstOrder.FreeVariable.Support σ}
    {key : FreeVariableKey σ} :
    key ∈ insertSupport owners support ↔
      key ∈ support ∨ key ∈ owners := by
  induction support generalizing owners with
  | nil =>
      simp [insertSupport]
  | cons fv rest ih =>
      rw [insertSupport, ih]
      by_cases hEq : key = fv
      · subst key
        simp [freeVariableKey]
      · have hNe : fv ≠ key :=
          fun h => hEq h.symm
        simp [freeVariableKey, hEq, hNe]

private def supportCount (components : List (Clause σ)) : Nat :=
  components.foldl (fun count component =>
    count + component.freeSupport.length) 0

private def supportOwnersAux?
    [DecidableEq σ.SortSymbol] (capacity : Nat) :
    List (Clause σ) →
      Option (Std.HashSet (FreeVariableKey σ))
  | [] => some (Std.HashSet.emptyWithCapacity capacity)
  | head :: rest =>
      match supportOwnersAux? capacity rest with
      | none => none
      | some owners =>
          if head.freeSupport.all fun fv =>
              !owners.contains (freeVariableKey fv) then
            some (insertSupport owners head.freeSupport)
          else
            none

private def pairwiseSupportDisjointHashCheck {σ : Signature}
    [DecidableEq σ.SortSymbol] (components : List (Clause σ)) : Bool :=
  (supportOwnersAux? (supportCount components) components).isSome

private theorem supportOwnersAux?_sound
    [DecidableEq σ.SortSymbol]
    {capacity : Nat} {components : List (Clause σ)}
    {owners : Std.HashSet (FreeVariableKey σ)}
    (hBuild : supportOwnersAux? capacity components = some owners) :
    PairwiseSupportDisjoint components ∧
      ∀ component, component ∈ components →
        ∀ fv, fv ∈ component.freeSupport →
          freeVariableKey fv ∈ owners := by
  induction components generalizing owners with
  | nil =>
      simp [supportOwnersAux?] at hBuild
      subst owners
      exact ⟨trivial, by simp⟩
  | cons head rest ih =>
      simp only [supportOwnersAux?] at hBuild
      cases hRest : supportOwnersAux? capacity rest with
      | none =>
          simp [hRest] at hBuild
      | some restOwners =>
          by_cases hFresh :
              head.freeSupport.all fun fv =>
                !restOwners.contains (freeVariableKey fv)
          · simp [hRest, hFresh] at hBuild
            subst owners
            have hRestSound := ih hRest
            constructor
            · constructor
              · intro other hOther fv hHeadFv hOtherFv
                have hNotContains :
                    restOwners.contains (freeVariableKey fv) = false := by
                  simpa using
                    List.all_eq_true.mp hFresh fv hHeadFv
                have hOwned :
                    freeVariableKey fv ∈ restOwners :=
                  hRestSound.2 other hOther fv hOtherFv
                have hContains :
                    restOwners.contains (freeVariableKey fv) = true := by
                  simpa using
                    (Std.HashSet.mem_iff_contains.mp hOwned)
                simp [hNotContains] at hContains
              · exact hRestSound.1
            · intro component hComponent fv hFv
              rcases List.mem_cons.mp hComponent with rfl | hComponent
              · exact mem_insertSupport_iff.mpr (Or.inl hFv)
              · exact mem_insertSupport_iff.mpr
                  (Or.inr (hRestSound.2 component hComponent fv hFv))
          · simp [hRest, hFresh] at hBuild

private theorem supportOwnersAux?_membership
    [DecidableEq σ.SortSymbol]
    {capacity : Nat} {components : List (Clause σ)}
    {owners : Std.HashSet (FreeVariableKey σ)}
    (hBuild : supportOwnersAux? capacity components = some owners) :
    ∀ key, key ∈ owners ↔
      ∃ component, component ∈ components ∧
        key ∈ component.freeSupport := by
  induction components generalizing owners with
  | nil =>
      simp [supportOwnersAux?] at hBuild
      subst owners
      intro key
      simp
  | cons head rest ih =>
      simp only [supportOwnersAux?] at hBuild
      cases hRest : supportOwnersAux? capacity rest with
      | none =>
          simp [hRest] at hBuild
      | some restOwners =>
          by_cases hFresh :
              head.freeSupport.all fun fv =>
                !restOwners.contains (freeVariableKey fv)
          · simp [hRest, hFresh] at hBuild
            subst owners
            intro key
            rw [mem_insertSupport_iff]
            constructor
            · rintro (hHead | hRestOwned)
              · exact ⟨head, by simp, hHead⟩
              · rcases (ih hRest key).mp hRestOwned with
                  ⟨component, hComponent, hKey⟩
                exact
                  ⟨component, List.mem_cons_of_mem head hComponent, hKey⟩
            · rintro ⟨component, hComponent, hKey⟩
              rcases List.mem_cons.mp hComponent with rfl | hComponent
              · exact Or.inl hKey
              · exact Or.inr ((ih hRest key).mpr
                  ⟨component, hComponent, hKey⟩)
          · simp [hRest, hFresh] at hBuild

private theorem supportOwnersAux?_complete
    [DecidableEq σ.SortSymbol]
    {capacity : Nat} {components : List (Clause σ)}
    (hDisjoint : PairwiseSupportDisjoint components) :
    ∃ owners, supportOwnersAux? capacity components = some owners := by
  induction components with
  | nil =>
      exact
        ⟨Std.HashSet.emptyWithCapacity capacity, by
          simp [supportOwnersAux?]⟩
  | cons head rest ih =>
      rcases hDisjoint with ⟨hHead, hRest⟩
      rcases ih hRest with ⟨restOwners, hBuild⟩
      have hFresh :
          head.freeSupport.all (fun fv =>
            !restOwners.contains (freeVariableKey fv)) = true := by
        apply List.all_eq_true.mpr
        intro fv hFv
        have hNotMem :
            ¬freeVariableKey fv ∈ restOwners := by
          intro hOwned
          rcases (supportOwnersAux?_membership hBuild
              (freeVariableKey fv)).mp hOwned with
            ⟨other, hOther, hOtherFv⟩
          exact hHead other hOther fv hFv hOtherFv
        have hContains :
            restOwners.contains (freeVariableKey fv) = false := by
          exact Bool.eq_false_iff.mpr fun hTrue =>
            hNotMem (Std.HashSet.mem_iff_contains.mpr hTrue)
        simp [hContains]
      exact
        ⟨insertSupport restOwners head.freeSupport, by
          simp [supportOwnersAux?, hBuild, hFresh]⟩

private theorem pairwiseSupportDisjointHashCheck_eq {σ : Signature}
    [DecidableEq σ.SortSymbol] (components : List (Clause σ)) :
    pairwiseSupportDisjointHashCheck components =
      pairwiseSupportDisjointCheck components := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hCheck
    unfold pairwiseSupportDisjointHashCheck at hCheck
    cases hBuild :
        supportOwnersAux? (supportCount components) components with
    | none =>
        simp [hBuild] at hCheck
    | some owners =>
        exact pairwiseSupportDisjointReference_complete
          (supportOwnersAux?_sound hBuild).1
  · intro hCheck
    have hDisjoint :=
      pairwiseSupportDisjointReference_sound hCheck
    rcases supportOwnersAux?_complete
        (capacity := supportCount components) hDisjoint with
      ⟨owners, hBuild⟩
    simp [pairwiseSupportDisjointHashCheck, hBuild]

/--
运行时实现为单遍 owner registry：每个支持成员只做一次查询和一次插入，期望复杂度
`O(S)`，其中 `S` 是全部 component 支持长度之和。
-/
@[noinline]
unsafe def pairwiseSupportDisjointCheckImpl {σ : Signature}
    [DecidableEq σ.SortSymbol]
    (components : @& List (Clause σ)) : Bool :=
  pairwiseSupportDisjointHashCheck components

attribute [implemented_by pairwiseSupportDisjointCheckImpl]
  pairwiseSupportDisjointCheck

theorem pairwiseSupportDisjointCheck_sound {σ : Signature}
    [DecidableEq σ.SortSymbol] {components : List (Clause σ)}
    (hCheck : pairwiseSupportDisjointCheck components = true) :
    PairwiseSupportDisjoint components := by
  exact pairwiseSupportDisjointReference_sound hCheck
end Clause
namespace AvatarSelectorComponent
/-- 连续 selector 槽位表。槽位按 selector 变量保存唯一 component。 -/
structure Registry (σ : Signature) where
  slots : Array (Option (Clause σ)) := #[]
  deriving Inhabited

namespace Registry

def maxVarSucc {σ : Signature} :
    List (AvatarSelectorComponent σ) → Nat
  | [] => 0
  | entry :: rest => Nat.max (entry.selector.var + 1) (maxVarSucc rest)

/--
宿主材料化时构造的连续 registry witness。

重复变量只保留第一次出现的 component；随后 `check` 会逐项比较，故冲突项必然被拒绝。
-/
def build {σ : Signature} (entries : List (AvatarSelectorComponent σ)) :
    Registry σ := Id.run do
  let mut slots : Array (Option (Clause σ)) :=
    Array.replicate (maxVarSucc entries) none
  for entry in entries do
    let index := entry.selector.var
    match slots[index]? with
    | some none =>
        slots := slots.setIfInBounds index (some entry.component)
    | _ =>
        pure ()
  return { slots := slots }

def entryCheck {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (registry : Registry σ) (entry : AvatarSelectorComponent σ) : Bool :=
  match registry.slots[entry.selector.var]? with
  | some (some component) => component.eq entry.component
  | _ => false

def entriesCheck {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (registry : Registry σ) : List (AvatarSelectorComponent σ) → Bool
  | [] => true
  | entry :: rest =>
      registry.entryCheck entry && registry.entriesCheck rest

def check {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (registry : Registry σ) (entries : List (AvatarSelectorComponent σ)) : Bool :=
  registry.entriesCheck entries

private theorem entryCheck_of_check {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {registry : Registry σ}
    {entries : List (AvatarSelectorComponent σ)}
    (hCheck : registry.check entries = true) {entry : AvatarSelectorComponent σ}
    (hEntry : entry ∈ entries) :
    registry.entryCheck entry = true := by
  induction entries with
  | nil =>
      simp at hEntry
  | cons head rest ih =>
      rcases Bool.and_eq_true_iff.mp hCheck with ⟨hHead, hRest⟩
      rcases List.mem_cons.mp hEntry with hEntry | hEntry
      · simpa [check, entriesCheck, hEntry] using hHead
      · exact ih (by simpa [check, entriesCheck] using hRest) hEntry

theorem check_sound {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {registry : Registry σ} {entries : List (AvatarSelectorComponent σ)}
    (hCheck : registry.check entries = true) :
    Compatible entries := by
  intro left hLeft right hRight hVariable
  have hLeftCheck := entryCheck_of_check hCheck hLeft
  have hRightCheck := entryCheck_of_check hCheck hRight
  have hSlotRight :
      registry.slots[right.selector.var]? =
        registry.slots[left.selector.var]? := by
    simp [hVariable]
  cases hSlot : registry.slots[left.selector.var]? with
  | none =>
      simp [entryCheck, hSlot] at hLeftCheck hRightCheck
  | some slot =>
      cases slot with
      | none =>
          simp [entryCheck, hSlot] at hLeftCheck hRightCheck
      | some component =>
          have hLeftComponent : component.eq left.component = true := by
            simpa [entryCheck, hSlot] using hLeftCheck
          have hRightComponent : component.eq right.component = true := by
            simpa [entryCheck, hSlot, hSlotRight] using hRightCheck
          exact
            (Clause.eq_sound component left.component hLeftComponent).symm.trans
              (Clause.eq_sound component right.component hRightComponent)

end Registry
/--
局部 selector skeleton 在全局 registry valuation 下的精确语义。
局部 entries 只需是 registry 的子列表；selector 的解释由全局正性和全局一致性唯一
确定。
-/
theorem selectorClause_satisfies_iff_exists_valid_in_registry
    {σ : Signature} [DecidableEq σ.SortSymbol]
    {M : SetLevel.StructureAt.{x} σ} (base : SetLevel.EnvAt.{x} M) (registry entries : List (AvatarSelectorComponent σ)) (hPositive :
      ∀ entry, entry ∈ registry → entry.selector.positive = true) (hCompatible : Compatible registry) (hSubset : ∀ entry, entry ∈ entries → entry ∈ registry) :
    PropResolution.Clause.Satisfies (valuation base registry) (selectorClause entries) ↔
      ∃ entry, entry ∈ entries ∧
        Clause.ValidOnBoundStack base entry.component := by
  constructor
  · rintro ⟨selector, hSelectorMem, hSelector⟩
    have hSelectorMem' :
        selector ∈ entries.map AvatarSelectorComponent.selector := by
      simpa [selectorClause] using hSelectorMem
    rcases List.mem_map.mp hSelectorMem' with
      ⟨entry, hEntry, hSelectorEq⟩
    subst selector
    have hEntryRegistry := hSubset entry hEntry
    exact
      ⟨entry, hEntry, (holds_valuation_iff_component_valid
          base registry hPositive hCompatible hEntryRegistry).mp hSelector⟩
  · rintro ⟨entry, hEntry, hValid⟩
    have hEntryRegistry := hSubset entry hEntry
    refine ⟨entry.selector, ?_, ?_⟩
    · have hMapped :
          entry.selector ∈
            entries.map AvatarSelectorComponent.selector :=
        List.mem_map.mpr ⟨entry, hEntry, rfl⟩
      simpa [selectorClause] using hMapped
    · exact (holds_valuation_iff_component_valid
          base registry hPositive hCompatible hEntryRegistry).mpr hValid
end AvatarSelectorComponent
namespace AvatarSplitPayload
/--
单个 split 可由 checker 独立复算出的 registry 合同。
selector 的跨 split 一致性是全图性质，因此不放在这里，而由全局 registry checker
统一提供。
-/
structure RegistryContract {σ : Signature} (payload : AvatarSplitPayload σ) : Prop where
  aligned :
    payload.selectors.toList.length = payload.componentClauses.length
  covers :
    Clause.Covers payload.source.clause payload.componentClauses
  pairwiseDisjoint :
    Clause.PairwiseSupportDisjoint payload.componentClauses
  selectorsPositive :
    ∀ selector, selector ∈ payload.selectors.toList →
      selector.positive = true
def registryCheck {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (payload : AvatarSplitPayload σ) : Bool :=
  payload.selectors.size == payload.partitions.size &&
    Clause.partitionCoversCheck payload.source.clause.literals.size
        payload.partitions &&
      Clause.pairwiseSupportDisjointCheck payload.componentClauses &&
        payload.selectors.all fun selector => selector.positive
theorem registryCheck_sound {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {payload : AvatarSplitPayload σ} (hCheck : registryCheck payload = true) : RegistryContract payload := by
  simp only [registryCheck, Bool.and_eq_true_iff] at hCheck
  rcases hCheck with
    ⟨⟨⟨hAligned, hCovers⟩, hDisjoint⟩, hPositive⟩
  exact {
    aligned := by
      simpa [componentClauses] using hAligned
    covers := Clause.partitionCoversCheck_sound hCovers
    pairwiseDisjoint :=
      Clause.pairwiseSupportDisjointCheck_sound hDisjoint
    selectorsPositive := by
      intro selector hSelector
      have hArray : selector ∈ payload.selectors :=
        Array.mem_def.mpr hSelector
      rcases Array.mem_iff_getElem.mp hArray with
        ⟨index, hIndex, hGet⟩
      have hAt := Array.all_eq_true.mp hPositive index hIndex
      simpa [hGet] using hAt
  }
theorem RegistryContract.selectorComponentsPositive {σ : Signature}
    {payload : AvatarSplitPayload σ} (hContract : RegistryContract payload) :
    ∀ entry, entry ∈ payload.selectorComponents →
      entry.selector.positive = true := by
  intro entry hEntry
  apply hContract.selectorsPositive
  have hMapped :
      entry.selector ∈
        payload.selectorComponents.map AvatarSelectorComponent.selector :=
    List.mem_map.mpr ⟨entry, hEntry, rfl⟩
  have hProjection :
      payload.selectorComponents.map AvatarSelectorComponent.selector =
        payload.selectors.toList := by
    simpa [selectorComponents] using
      AvatarSelectorComponent.selectors_ofLists hContract.aligned
  rw [hProjection] at hMapped
  exact hMapped
theorem selectorComponent_mem {σ : Signature}
    {payload : AvatarSplitPayload σ}
    {index : Nat} {indices : Array Nat} {selector : GuardLit} (hIndices : payload.partitions[index]? = some indices) (hSelector :
      AvatarSplit.selectorAt? payload.selectors index = some selector) :
    ⟨selector, Clause.atIndices payload.source.clause indices⟩ ∈
      payload.selectorComponents := by
  have hSelectorList :
      payload.selectors.toList[index]? = some selector := by
    simpa [AvatarSplit.selectorAt?] using hSelector
  have hComponentList :
      payload.componentClauses[index]? =
        some (Clause.atIndices payload.source.clause indices) := by
    have hPartitionList :
        payload.partitions.toList[index]? = some indices := by
      simpa using hIndices
    simp [componentClauses, hPartitionList]
  have hEntryGet :
      payload.selectorComponents[index]? =
        some ⟨selector, Clause.atIndices payload.source.clause indices⟩ :=
    AvatarSelectorComponent.getElem?_ofLists
      hSelectorList hComponentList
  rcases List.getElem?_eq_some_iff.mp hEntryGet with
    ⟨hIndex, hGet⟩
  rw [← hGet]
  exact List.getElem_mem hIndex
theorem source_valid_iff_selectors_satisfy_in_registry {σ : Signature}
    [DecidableEq σ.SortSymbol] {M : SetLevel.StructureAt.{x} σ} (base : SetLevel.EnvAt.{x} M) (payload : AvatarSplitPayload σ)
    (hContract : RegistryContract payload) (registry : List (AvatarSelectorComponent σ)) (hPositive :
      ∀ entry, entry ∈ registry → entry.selector.positive = true) (hCompatible : AvatarSelectorComponent.Compatible registry) (hSubset :
      ∀ entry, entry ∈ payload.selectorComponents → entry ∈ registry) :
    Clause.ValidOnBoundStack base payload.source.clause ↔
      PropResolution.Clause.Satisfies (AvatarSelectorComponent.valuation base registry)
        payload.selectors := by
  have hComponents :=
    components_selectorComponents (payload := payload) hContract.aligned
  have hSelectors :=
    selectorClause_selectorComponents (payload := payload) hContract.aligned
  rw [← hSelectors]
  constructor
  · intro hSource
    rcases (Clause.validOnBoundStack_iff_exists_component
          base payload.source.clause payload.componentClauses
          hContract.covers hContract.pairwiseDisjoint).mp hSource with
      ⟨component, hComponentMem, hValid⟩
    have hEntryComponents :
        component ∈
          payload.selectorComponents.map
            AvatarSelectorComponent.component := by
      simpa [hComponents] using hComponentMem
    rcases List.mem_map.mp hEntryComponents with
      ⟨entry, hEntry, hComponentEq⟩
    cases hComponentEq
    exact (AvatarSelectorComponent.selectorClause_satisfies_iff_exists_valid_in_registry
          base registry payload.selectorComponents
          hPositive hCompatible hSubset).mpr
        ⟨entry, hEntry, hValid⟩
  · intro hSkeleton
    rcases (AvatarSelectorComponent.selectorClause_satisfies_iff_exists_valid_in_registry
            base registry payload.selectorComponents
            hPositive hCompatible hSubset).mp hSkeleton with
      ⟨entry, hEntry, hValid⟩
    apply (Clause.validOnBoundStack_iff_exists_component
        base payload.source.clause payload.componentClauses
        hContract.covers hContract.pairwiseDisjoint).mpr
    exact
      ⟨entry.component,
        by
          rw [← hComponents]
          exact List.mem_map.mpr ⟨entry, hEntry, rfl⟩,
        hValid⟩
end AvatarSplitPayload
namespace Payload
def avatarSelectorComponents {σ : Signature} :
    Payload σ → List (AvatarSelectorComponent σ)
  | .avatarSplit payload => payload.selectorComponents
  | _ => []
def avatarRegistryLocalCheck {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] : Payload σ → Bool
  | .avatarSplit payload => payload.registryCheck
  | _ => true
end Payload
namespace DAG
def avatarSelectorRegistry {σ : Signature} (dag : DAG σ) :
    List (AvatarSelectorComponent σ) :=
  dag.nodes.toList.flatMap fun node =>
    node.payload.avatarSelectorComponents
def nodeAvatarRegistryLocalCheck {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (node : Node σ) : Bool :=
  node.payload.avatarRegistryLocalCheck
/- AVATAR selector registry 的整图可信边界。 -/
def avatarRegistryCheckWith {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (dag : DAG σ)
    (registry : AvatarSelectorComponent.Registry σ) : Bool :=
  dag.nodes.all nodeAvatarRegistryLocalCheck &&
    AvatarSelectorComponent.Registry.check
      registry dag.avatarSelectorRegistry
/--
逐节点局部证明与经等式审计的全局 registry 合成 AVATAR registry checker。
-/
theorem avatarRegistryCheck_eq_true_of_nodes_and_registry {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (dag : DAG σ)
    (registry : AvatarSelectorComponent.Registry σ)
    (checked : CheckedList nodeAvatarRegistryLocalCheck dag.nodes.toList)
    (hCompatible :
      AvatarSelectorComponent.Registry.check registry dag.avatarSelectorRegistry = true) :
    avatarRegistryCheckWith dag registry = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · rw [← Array.all_toList]
    exact checked.all_eq_true
  · exact hCompatible
def avatarSelectorValuation {σ : Signature} [DecidableEq σ.SortSymbol]
    {M : SetLevel.StructureAt.{x} σ} (dag : DAG σ) (base : SetLevel.EnvAt.{x} M) :
    PropResolution.Valuation :=
  AvatarSelectorComponent.valuation base dag.avatarSelectorRegistry
theorem mem_avatarSelectorRegistry_of_split {σ : Signature}
    {dag : DAG σ} {splitId : Nat} {splitNode : Node σ}
    {payload : AvatarSplitPayload σ}
    {entry : AvatarSelectorComponent σ} (hNode : dag.node? splitId = some splitNode) (hPayload : splitNode.payload = .avatarSplit payload)
    (hEntry : entry ∈ payload.selectorComponents) :
    entry ∈ dag.avatarSelectorRegistry := by
  have hNodeMem : splitNode ∈ dag.nodes.toList := by
    rcases getElem?_eq_some_iff.mp hNode with ⟨hIndex, hGet⟩
    have hArray : splitNode ∈ dag.nodes := by
      rw [← hGet]
      exact Array.getElem_mem hIndex
    exact Array.mem_def.mp hArray
  unfold avatarSelectorRegistry
  apply List.mem_flatMap.mpr
  exact
    ⟨splitNode, hNodeMem,
      by
        simpa [Payload.avatarSelectorComponents, hPayload] using hEntry⟩
theorem avatarSplitRegistryCheck_of_eq_true {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {dag : DAG σ}
    {registry : AvatarSelectorComponent.Registry σ}
    (hCheck : avatarRegistryCheckWith dag registry = true)
    {splitId : Nat} {splitNode : Node σ}
    {payload : AvatarSplitPayload σ} (hNode : dag.node? splitId = some splitNode) (hPayload : splitNode.payload = .avatarSplit payload) :
    payload.registryCheck = true := by
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hNodes, _hCompatible⟩
  rcases getElem?_eq_some_iff.mp hNode with ⟨hIndex, hGet⟩
  have hAt := Array.all_eq_true.mp hNodes splitId hIndex
  have hGet' : dag.nodes[splitId] = splitNode := by
    simpa [graphView] using hGet
  rw [hGet'] at hAt
  simpa [hPayload, nodeAvatarRegistryLocalCheck,
    Payload.avatarRegistryLocalCheck] using hAt
theorem avatarSplitRegistryContract {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {dag : DAG σ}
    {registry : AvatarSelectorComponent.Registry σ}
    (hCheck : avatarRegistryCheckWith dag registry = true)
    {splitId : Nat} {splitNode : Node σ}
    {payload : AvatarSplitPayload σ} (hNode : dag.node? splitId = some splitNode) (hPayload : splitNode.payload = .avatarSplit payload) :
    AvatarSplitPayload.RegistryContract payload :=
  AvatarSplitPayload.registryCheck_sound (avatarSplitRegistryCheck_of_eq_true hCheck hNode hPayload)
theorem avatarSelectorRegistry_positive {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {dag : DAG σ}
    {registry : AvatarSelectorComponent.Registry σ}
    (hCheck : avatarRegistryCheckWith dag registry = true) :
    ∀ entry, entry ∈ dag.avatarSelectorRegistry →
      entry.selector.positive = true := by
  intro entry hEntry
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hNodes, _hCompatible⟩
  rcases List.mem_flatMap.mp hEntry with
    ⟨node, hNodeMem, hPayloadEntry⟩
  have hNodeLocal : node.payload.avatarRegistryLocalCheck = true := by
    have hArray : node ∈ dag.nodes := Array.mem_def.mpr hNodeMem
    rcases Array.mem_iff_getElem.mp hArray with
      ⟨index, hIndex, hGet⟩
    have hAt := Array.all_eq_true.mp hNodes index hIndex
    simpa [hGet, nodeAvatarRegistryLocalCheck] using hAt
  cases hPayload : node.payload with
  | avatarSplit payload =>
      have hLocal : payload.registryCheck = true := by
        simpa [Payload.avatarRegistryLocalCheck, hPayload] using hNodeLocal
      have hEntryLocal : entry ∈ payload.selectorComponents := by
        simpa [Payload.avatarSelectorComponents, hPayload] using hPayloadEntry
      exact
        AvatarSplitPayload.RegistryContract.selectorComponentsPositive (AvatarSplitPayload.registryCheck_sound hLocal) entry hEntryLocal
  | source _ =>
      simp [Payload.avatarSelectorComponents, hPayload] at hPayloadEntry
  | avatarComponent _ =>
      simp [Payload.avatarSelectorComponents, hPayload] at hPayloadEntry
  | localRule _ =>
      simp [Payload.avatarSelectorComponents, hPayload] at hPayloadEntry
  | theoryConflict _ =>
      simp [Payload.avatarSelectorComponents, hPayload] at hPayloadEntry
  | propositionalLearnedClause _ =>
      simp [Payload.avatarSelectorComponents, hPayload] at hPayloadEntry
  | residualCdcl _ =>
      simp [Payload.avatarSelectorComponents, hPayload] at hPayloadEntry
theorem avatarSelectorRegistry_compatible {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {dag : DAG σ}
    {registry : AvatarSelectorComponent.Registry σ}
    (hCheck : avatarRegistryCheckWith dag registry = true) :
    AvatarSelectorComponent.Compatible dag.avatarSelectorRegistry :=
  AvatarSelectorComponent.Registry.check_sound (Bool.and_eq_true_iff.mp hCheck).2
end DAG
structure CheckedAvatarDAG {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] where
  checked : CheckedDAG (σ := σ)
  registry : AvatarSelectorComponent.Registry σ
  registryChecked : DAG.avatarRegistryCheckWith checked.dag registry = true
namespace CheckedAvatarDAG
def mk? {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (checked : CheckedDAG (σ := σ)) (registry : AvatarSelectorComponent.Registry σ) :
    Option (CheckedAvatarDAG (σ := σ)) :=
  if h : DAG.avatarRegistryCheckWith checked.dag registry = true then
    some { checked := checked, registry := registry, registryChecked := h }
  else
    none
def selectorValuation {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedAvatarDAG (σ := σ))
    {M : SetLevel.StructureAt.{x} σ} (base : SetLevel.EnvAt.{x} M) :
    PropResolution.Valuation :=
  cert.checked.dag.avatarSelectorValuation base
theorem componentSelectorSemantics {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedAvatarDAG (σ := σ))
    {M : SetLevel.StructureAt.{x} σ} (base : SetLevel.EnvAt.{x} M) :
    AvatarComponentSelectorSemantics cert.checked.dag base (cert.selectorValuation base) := by
  intro splitId splitNode splitPayload componentIndex indices selector
    hNode hPayload hIndices hSelector
  let entry : AvatarSelectorComponent σ :=
    ⟨selector, Clause.atIndices splitPayload.source.clause indices⟩
  have hEntryLocal : entry ∈ splitPayload.selectorComponents := by
    exact AvatarSplitPayload.selectorComponent_mem hIndices hSelector
  have hEntryGlobal :
      entry ∈ cert.checked.dag.avatarSelectorRegistry :=
    DAG.mem_avatarSelectorRegistry_of_split
      hNode hPayload hEntryLocal
  exact
    AvatarSelectorComponent.holds_valuation_iff_component_valid
      base cert.checked.dag.avatarSelectorRegistry (DAG.avatarSelectorRegistry_positive cert.registryChecked)
      (DAG.avatarSelectorRegistry_compatible cert.registryChecked)
      hEntryGlobal
theorem splitSelectorSemantics {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedAvatarDAG (σ := σ))
    {M : SetLevel.StructureAt.{x} σ} (base : SetLevel.EnvAt.{x} M) :
    AvatarSplitSelectorSemantics cert.checked.dag base (cert.selectorValuation base) := by
  intro splitId splitNode splitPayload hNode hPayload
  have hContract :=
    DAG.avatarSplitRegistryContract cert.registryChecked hNode hPayload
  have hSubset :
      ∀ entry, entry ∈ splitPayload.selectorComponents →
        entry ∈ cert.checked.dag.avatarSelectorRegistry := by
    intro entry hEntry
    exact DAG.mem_avatarSelectorRegistry_of_split
      hNode hPayload hEntry
  have hRaw :=
    AvatarSplitPayload.source_valid_iff_selectors_satisfy_in_registry
      base splitPayload hContract
      cert.checked.dag.avatarSelectorRegistry (DAG.avatarSelectorRegistry_positive cert.registryChecked)
      (DAG.avatarSelectorRegistry_compatible cert.registryChecked)
      hSubset
  exact hRaw.trans (PropResolution.Clause.satisfies_canonicalClause_iff (cert.selectorValuation base) splitPayload.selectors).symm
/--
AVATAR root contradiction 的自动 registry 版本。
调用者只需给出对象层 ClauseProblem.Valid 与 soundness-supported 检查；selector valuation
和 component/split 语义合同都由 checked registry 自动生成。
-/
theorem rootEmptyContradiction_of_avatarSoundnessSupported
    {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedAvatarDAG (σ := σ))
    {M : SetLevel.StructureAt.{x} σ} (base : SetLevel.EnvAt.{x} M) (hProblem : cert.checked.dag.problem.Valid base)
    (hSupported : cert.checked.dag.avatarSoundnessSupported = true) :
    False :=
  cert.checked.rootEmptyContradiction_of_avatarSoundnessSupported
    base (cert.selectorValuation base) hProblem (cert.componentSelectorSemantics base) (cert.splitSelectorSemantics base) hSupported
/--
显式 validity bridge 驱动的 AVATAR universe-polymorphic 语义结论。
该接口供整问题预处理主线消费：反模型经 preprocessing bridge 扩张为 DAG clause
problem 的模型后，checked AVATAR root 自动导出矛盾。
-/
theorem semanticallyEntails_of_avatarSoundnessSupported_of_valid
    {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedAvatarDAG (σ := σ)) (problem : DeepProblem σ)
    (hSupported : cert.checked.dag.avatarSoundnessSupported = true) (hValid :
      ∀ {M : SetLevel.StructureAt.{x} σ} (env : SetLevel.EnvAt.{x} M),
        Logic.FirstOrder.Theory.Models problem.theory env →
          ¬ Logic.FirstOrder.Formula.satisfies env problem.target →
            ∃ (target : SetLevel.StructureAt.{x} σ),
              ∃ (targetEnv : SetLevel.EnvAt.{x} target),
                cert.checked.dag.problem.Valid targetEnv) :
    SetLevel.SemanticallyEntailsAt.{x} problem.theory problem.target := by
  intro M env hModels
  by_cases hTarget :
      Logic.FirstOrder.Formula.satisfies env problem.target
  · exact hTarget
  · rcases hValid env hModels hTarget with
      ⟨target, targetEnv, hClauseProblem⟩
    exact False.elim (cert.rootEmptyContradiction_of_avatarSoundnessSupported
        targetEnv hClauseProblem hSupported)
def semanticCertificate_of_avatarSoundnessSupported_of_valid
    {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedAvatarDAG (σ := σ)) (problem : DeepProblem σ)
    (hSupported : cert.checked.dag.avatarSoundnessSupported = true) (hValid :
      ∀ {M : SetLevel.StructureAt.{x} σ} (env : SetLevel.EnvAt.{x} M),
        Logic.FirstOrder.Theory.Models problem.theory env →
          ¬ Logic.FirstOrder.Formula.satisfies env problem.target →
            ∃ (target : SetLevel.StructureAt.{x} σ),
              ∃ (targetEnv : SetLevel.EnvAt.{x} target),
                cert.checked.dag.problem.Valid targetEnv) :
    SetLevel.SemanticCertificateAt.{x} problem.theory problem.target where
  entails :=
    cert.semanticallyEntails_of_avatarSoundnessSupported_of_valid
      problem hSupported hValid
def backendSuccess_of_avatarSoundnessSupported_of_valid
    {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedAvatarDAG (σ := σ)) (problem : DeepProblem σ)
    (hAdmissible : SetLevel.DeepProblem.Admissible problem) (hSupported : cert.checked.dag.avatarSoundnessSupported = true) (hValid :
      ∀ {M : SetLevel.StructureAt.{x} σ} (env : SetLevel.EnvAt.{x} M),
        Logic.FirstOrder.Theory.Models problem.theory env →
          ¬ Logic.FirstOrder.Formula.satisfies env problem.target →
            ∃ (target : SetLevel.StructureAt.{x} σ),
              ∃ (targetEnv : SetLevel.EnvAt.{x} target),
                cert.checked.dag.problem.Valid targetEnv) :
    SetLevel.BackendSuccessAt.{x} problem where
  admissible := hAdmissible
  backend := .dagReflection
  phase := .dagCheck
  cert :=
    cert.semanticCertificate_of_avatarSoundnessSupported_of_valid
      problem hSupported hValid
  audit? := some cert.checked.toComposite
  note := "DAG AVATAR soundness-supported fragment via checked preprocessing"
end CheckedAvatarDAG
end DAGCertificate
end Automation
end YesMetaZFC
