import BMSConstructibleBridge.SecondOrderCanonicalMemberDefSemantics
import BMSConstructibleBridge.SecondOrderPredecessorUnionSemantics

/-! # 相对层次的唯一原图阶段操作

最小阶段返回指定基图；有最大前驱的阶段取该前驱行的 Def；其余阶段取所有
前驱行的并集。这里只要求关系反对称来保证最大前驱唯一，不假定模型外良基。
完整历史和最终递归句另行组装，本文件不宣称 BMS 最终定理成立。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeHierarchyStep

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def minimal_l (R : set_l ℳ) (n : num_l ℳ) : Prop := ∀ i, ¬relation_l R i n

def immediate_l (R : set_l ℳ) (m n : num_l ℳ) : Prop :=
  relation_l R m n ∧ ∀ i, relation_l R i n → i = m ∨ relation_l R i m

def limit_l (R : set_l ℳ) (n : num_l ℳ) : Prop :=
  ¬minimal_l R n ∧ ¬∃ m, immediate_l R m n

theorem immediate_unique_l {R : set_l ℳ} {m k n : num_l ℳ}
    (hAsymm : ∀ a b, relation_l R a b → ¬relation_l R b a)
    (hm : immediate_l R m n) (hk : immediate_l R k n) : m = k := by
  rcases hk.2 m hm.1 with h | h
  · exact h
  · rcases hm.2 k hk.1 with h' | h'
    · exact h'.symm
    · exact False.elim (hAsymm m k h h')

def successor_l (R H : set_l ℳ) (n : num_l ℳ) (W : set_l ℳ) : Prop :=
  ∃ m Y, immediate_l R m n ∧ SecondOrderSections.spec_l H m Y ∧
    SecondOrderCanonicalMemberDefGraph.canonical_l Y (zero_l ℳ) W

def spec_l (B R H : set_l ℳ) (n : num_l ℳ) (W : set_l ℳ) : Prop :=
  (minimal_l R n ∧ W = B) ∨ successor_l R H n W ∨
    (limit_l R n ∧ SecondOrderPredecessorUnion.output_l R H n W)

theorem unique_l (hℳ : Theory.Models ℳ theory_m) {B R H W W' : set_l ℳ} {n : num_l ℳ}
    (hAsymm : ∀ a b, relation_l R a b → ¬relation_l R b a)
    (hW : spec_l B R H n W) (hW' : spec_l B R H n W') : W = W' := by
  rcases hW with ⟨hMin, rfl⟩ | ⟨m, Y, hm, hY, hDef⟩ | ⟨hLimit, hUnion⟩
  · rcases hW' with ⟨_, rfl⟩ | ⟨m, _, hm, _, _⟩ | ⟨hLimit, _⟩
    · rfl
    · exact False.elim (hMin m hm.1)
    · exact False.elim (hLimit.1 hMin)
  · rcases hW' with ⟨hMin, _⟩ | ⟨k, Y', hk, hY', hDef'⟩ | ⟨hLimit, _⟩
    · exact False.elim (hMin m hm.1)
    · have hmk := immediate_unique_l hAsymm hm hk
      subst k
      have hYY := SecondOrderSections.unique_l hℳ hY hY'
      subst Y'
      obtain ⟨Z, _, hUnique⟩ := SecondOrderCanonicalMemberDefGraph.canonical_exists_l hℳ Y (zero_l ℳ)
      exact (hUnique W hDef).trans (hUnique W' hDef').symm
    · exact False.elim (hLimit.2 ⟨m, hm⟩)
  · rcases hW' with ⟨hMin, _⟩ | ⟨m, _, hm, _, _⟩ | ⟨_, hUnion'⟩
    · exact False.elim (hLimit.1 hMin)
    · exact False.elim (hLimit.2 ⟨m, hm⟩)
    · obtain ⟨G, P, hG⟩ := hUnion
      obtain ⟨G', P', hG'⟩ := hUnion'
      exact SecondOrderPredecessorUnion.local_l hℳ hG hG' (fun _ _ _ => Iff.rfl)

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (B R H : set_l ℳ) (n : num_l ℳ)
    (hAsymm : ∀ a b, relation_l R a b → ¬relation_l R b a) :
    ∃! W : set_l ℳ, spec_l B R H n W := by
  classical
  suffices h : ∃ W, spec_l B R H n W from
    let ⟨W, hW⟩ := h
    ⟨W, hW, fun W' hW' => unique_l hℳ hAsymm hW' hW⟩
  by_cases hMin : minimal_l R n
  · exact ⟨B, Or.inl ⟨hMin, rfl⟩⟩
  · by_cases hSucc : ∃ m, immediate_l R m n
    · obtain ⟨m, hm⟩ := hSucc
      obtain ⟨Y, hY⟩ := SecondOrderSections.exists_l hℳ H m
      obtain ⟨W, hW, _⟩ := SecondOrderCanonicalMemberDefGraph.canonical_exists_l hℳ Y (zero_l ℳ)
      exact ⟨W, Or.inr (Or.inl ⟨m, Y, hm, hY, hW⟩)⟩
    · obtain ⟨W, hW, _⟩ := SecondOrderPredecessorUnion.output_exists_l hℳ R H n
      exact ⟨W, Or.inr (Or.inr ⟨⟨hMin, hSucc⟩, hW⟩)⟩

theorem transfer_l (hℳ : Theory.Models ℳ theory_m) {B R H K W : set_l ℳ} {n : num_l ℳ}
    (h : ∀ i, relation_l R i n → ∀ t, relation_l H i t ↔ relation_l K i t)
    (hW : spec_l B R H n W) : spec_l B R K n W := by
  rcases hW with hMin | ⟨m, Y, hm, hY, hDef⟩ | ⟨hLimit, G, P, hUnion⟩
  · exact Or.inl hMin
  · have hY' : SecondOrderSections.spec_l K m Y := fun t => (hY t).trans (h m hm.1 t)
    exact Or.inr (Or.inl ⟨m, Y, hm, hY', hDef⟩)
  · obtain ⟨W', G', P', hUnion'⟩ : ∃ W' G' P', SecondOrderPredecessorUnion.spec_l R K n G' P' W' := by
      obtain ⟨G', P', W', hW'⟩ := SecondOrderPredecessorUnion.exists_l hℳ R K n
      exact ⟨W', G', P', hW'⟩
    have hEq := SecondOrderPredecessorUnion.local_l hℳ hUnion hUnion' h
    subst W'
    exact Or.inr (Or.inr ⟨hLimit, G', P', hUnion'⟩)

theorem root_l (hℳ : Theory.Models ℳ theory_m) {B R H W : set_l ℳ} {n : num_l ℳ}
    (hB : SecondOrderDomain.wf_l B (zero_l ℳ))
    (hRows : SecondOrderPredecessorUnionSemantics.rows_wf_l R H n)
    (hW : spec_l B R H n W) : SecondOrderDomain.wf_l W (zero_l ℳ) := by
  rcases hW with ⟨_, rfl⟩ | ⟨m, Y, hm, hY, a, hDefault, V, E, D, Q, S, T, F, G, P, hDef⟩ |
    ⟨_, G, P, hUnion⟩
  · exact hB
  · exact SecondOrderCanonicalMemberDefSemantics.root_l hℳ
      ⟨Y, zero_l ℳ, hRows m hm.1 Y hY⟩ hDef
  · exact SecondOrderPredecessorUnionSemantics.root_l hℳ hUnion hRows

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeHierarchyStep
