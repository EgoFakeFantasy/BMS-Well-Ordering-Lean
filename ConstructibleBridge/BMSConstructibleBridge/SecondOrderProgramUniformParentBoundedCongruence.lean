import BMSConstructibleBridge.SecondOrderProgramUniformParentCandidate
import BMSConstructibleBridge.SecondOrderProgramUniformAncestorRows
import BMSConstructibleBridge.SecondOrderProgramUniformParentComparison
import BMSConstructibleBridge.SecondOrderProgramAncestorNone

/-!
# 有界父搜索结果的目标搬运

若两次父搜索的实际结果都落在同一前缀内，而且此前缀中的候选在本行的条目比较
及全部低行的祖先测试一致，则两次查询逐输出相同。只要求实际结果有界，
不要求前缀之外的候选逐个对应；适用于不同数组和不同目标列。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformParentBoundedCongruence

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramUniformParentComparison (entry_order_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 某条实际父边在另一目标仍合格时，另一搜索必返回不早于它的父列。 -/
private theorem transfer_l (hℳ : Theory.Models ℳ theory_m) {P M J L : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hL : graph_semantics_l (graph_m length_m) L)
    {x y n row target other found : num_l ℳ}
    (hn : relation_l L y n)
    (hother : SecondOrderOrder.lt_l other n)
    (hfound : SecondOrderOrder.lt_l found other)
    (hentries : entry_order_l J x row found target → entry_order_l J y row found other)
    (hbelow : ∀ s, SecondOrderOrder.lt_l s row →
      (¬relation_l M (value_l (value_l (value_l x s) target) found) (zero_l ℳ)) →
      ¬relation_l M (value_l (value_l (value_l y s) other) found) (zero_l ℳ))
    (hparent : relation_l P (value_l (value_l x row) target) (succ_l found)) :
    ∃ next, relation_l P (value_l (value_l y row) other) (succ_l next) ∧
      (found = next ∨ SecondOrderOrder.lt_l found next) := by
  obtain ⟨a, b, ha, hb, hab⟩ := hentries
    (SecondOrderProgramUniformParentSpecification.parent_entries_lt_l hℳ hP hJ hparent)
  exact SecondOrderProgramUniformParentCandidate.parent_at_or_after_l
    hℳ hP hM hJ hL hn hother hfound ha hb hab
    (fun s hs => hbelow s hs
      (SecondOrderProgramUniformAncestorRows.row_le_l hℳ hM (Or.inr hs)
        (SecondOrderProgramUniformAncestorStructure.parent_l hℳ hP hM hparent)))

/-- 两次父查询的实际正结果都在同一界内时，界内候选一致即给出全部输出一致。 -/
theorem query_congr_l (hℳ : Theory.Models ℳ theory_m) {P M J L : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hL : graph_semantics_l (graph_m length_m) L)
    {x y nx ny row left right bound : num_l ℳ}
    (hx : relation_l L x nx) (hy : relation_l L y ny)
    (hleft : SecondOrderOrder.lt_l left nx)
    (hright : SecondOrderOrder.lt_l right ny)
    (hboundLeft : bound = left ∨ SecondOrderOrder.lt_l bound left)
    (hboundRight : bound = right ∨ SecondOrderOrder.lt_l bound right)
    (hparentsLeft : ∀ found,
      relation_l P (value_l (value_l x row) left) (succ_l found) →
      SecondOrderOrder.lt_l found bound)
    (hparentsRight : ∀ found,
      relation_l P (value_l (value_l y row) right) (succ_l found) →
      SecondOrderOrder.lt_l found bound)
    (hentries : ∀ found, SecondOrderOrder.lt_l found bound →
      (entry_order_l J x row found left ↔ entry_order_l J y row found right))
    (hbelow : ∀ s, SecondOrderOrder.lt_l s row →
      ∀ found, SecondOrderOrder.lt_l found bound →
      ((¬relation_l M (value_l (value_l (value_l x s) left) found) (zero_l ℳ)) ↔
        ¬relation_l M (value_l (value_l (value_l y s) right) found) (zero_l ℳ))) :
    ∀ q, relation_l P (value_l (value_l x row) left) q ↔
      relation_l P (value_l (value_l y row) right) q := by
  letI := order_l hℳ
  have hPf := function_of_semantics_l hℳ parent_m hP
  have forward (found : num_l ℳ)
      (hp : relation_l P (value_l (value_l x row) left) (succ_l found)) :
      ∃ next, relation_l P (value_l (value_l y row) right) (succ_l next) ∧
        (found = next ∨ SecondOrderOrder.lt_l found next) := by
    have hb := hparentsLeft found hp
    have hft : found < right := lt_of_lt_of_le hb (show bound ≤ right from hboundRight)
    exact transfer_l hℳ hP hM hJ hL hy hright hft (hentries found hb).mp
      (fun s hs => (hbelow s hs found hb).mp) hp
  have backward (found : num_l ℳ)
      (hp : relation_l P (value_l (value_l y row) right) (succ_l found)) :
      ∃ next, relation_l P (value_l (value_l x row) left) (succ_l next) ∧
        (found = next ∨ SecondOrderOrder.lt_l found next) := by
    have hb := hparentsRight found hp
    have hft : found < left := lt_of_lt_of_le hb (show bound ≤ left from hboundLeft)
    exact transfer_l hℳ hP hM hJ hL hx hleft hft (hentries found hb).mpr
      (fun s hs => (hbelow s hs found hb).mpr) hp
  obtain ⟨a, ha, _⟩ := hPf (value_l (value_l x row) left)
  obtain ⟨b, hb, _⟩ := hPf (value_l (value_l y row) right)
  have hab : a = b := by
    rcases predecessor_l hℳ a with rfl | ⟨a, rfl⟩
    · rcases predecessor_l hℳ b with rfl | ⟨b, rfl⟩
      · rfl
      · obtain ⟨c, hc, _⟩ := backward b hb
        exact False.elim ((nonzero_l hℳ c).symm (function_value_unique_l hPf ha hc))
    · rcases predecessor_l hℳ b with rfl | ⟨b, rfl⟩
      · obtain ⟨c, hc, _⟩ := forward a ha
        exact False.elim ((nonzero_l hℳ c).symm (function_value_unique_l hPf hb hc))
      · obtain ⟨b', hb', hab'⟩ := forward a ha
        obtain ⟨a', ha', hba'⟩ := backward b hb
        have haEq : a' = a := injective_l hℳ (function_value_unique_l hPf ha' ha)
        have hbEq : b' = b := injective_l hℳ (function_value_unique_l hPf hb' hb)
        have habLe : a ≤ b := hbEq ▸ hab'
        have hbaLe : b ≤ a := haEq ▸ hba'
        exact congrArg succ_l (le_antisymm habLe hbaLe)
  intro q
  constructor
  · intro hq
    rw [function_value_unique_l hPf hq ha, hab]
    exact hb
  · intro hq
    rw [function_value_unique_l hPf hq hb, ← hab]
    exact ha

/-- 同一数组同一行中，目标的父查询相同就给出全部祖先查询的真假相同。
父之后的链完全相同；不能无条件推广到两个不同数组。 -/
theorem member_congr_of_query_l (hℳ : Theory.Models ℳ theory_m) {P M : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {x row left right : num_l ℳ}
    (hquery : ∀ q, relation_l P (value_l (value_l x row) left) q ↔
      relation_l P (value_l (value_l x row) right) q) (found : num_l ℳ) :
    (¬relation_l M (value_l (value_l (value_l x row) left) found) (zero_l ℳ)) ↔
      ¬relation_l M (value_l (value_l (value_l x row) right) found) (zero_l ℳ) := by
  obtain ⟨q, hq, _⟩ := function_of_semantics_l hℳ parent_m hP
    (value_l (value_l x row) left)
  have hr := (hquery q).mp hq
  rcases predecessor_l hℳ q with rfl | ⟨parent, rfl⟩
  · exact iff_of_false
      (fun h => h (SecondOrderProgramAncestorNone.member_none_l hℳ parent_m hM hP hq found))
      (fun h => h (SecondOrderProgramAncestorNone.member_none_l hℳ parent_m hM hP hr found))
  · exact (SecondOrderProgramUniformAncestorStructure.member_some_l hℳ hP hM hq).trans
      (SecondOrderProgramUniformAncestorStructure.member_some_l hℳ hP hM hr).symm

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformParentBoundedCongruence
