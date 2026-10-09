import BMSConstructibleBridge.PowerlessRelativeClassSource
import BMSConstructibleBridge.PowerlessRelativeClassFunctionAbsolute
import BMSConstructibleBridge.PowerlessRelativeClassBasicClosure
import BMSConstructibleBridge.PowerlessClassFiniteElementarity
import BMSConstructibleBridge.PowerlessWholeCollapseClosure

/-! # 原配对和二元并见证请求的真实虚拟闭包

两项原存在式加入同一有限族。直接捕获 Class 中满足原矩阵的见证，
不先把弱子域内的配对规格当作真实配对。实际 Class 的传递性读回
完整 raw 规格，外延性识别任意候选输出。程序请求闭包在消费模块取得。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassOperationRequests

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessSourceClass.structure_l PowerlessSourceClass.type_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

def pair_matrix_m (Δ : SortContext ℒ) : Formula ℒ [.set, .set, .set] Δ :=
  SecondOrderObjectSyntax.pair_m (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)

def binary_matrix_m (Δ : SortContext ℒ) : Formula ℒ [.set, .set, .set] Δ :=
  PowerlessRelativeFiniteHullAssignments.binary_m
    (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)

def family_m (Δ : SortContext ℒ) : PowerlessClassFiniteElementarity.family_m Δ :=
  [Sigma.mk ([.set, .set] : SortContext ℒ) (.existsE .set (pair_matrix_m Δ)),
    Sigma.mk ([.set, .set] : SortContext ℒ) (.existsE .set (binary_matrix_m Δ))]

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ z, SecondOrderQuotient.mem_l hℳ z B →
    ∀ t, SecondOrderQuotient.mem_l hℳ t z → SecondOrderQuotient.mem_l hℳ t B}
  {hP : ∃ z, PowerlessRelativeClassCorrespondence.member_l hℳ B z}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "ε" => SecondOrderQuotient.mem_l hℳ
local notation "𝒩₀" => PowerlessRelativeClassStructure.structure_l hℳ B hBase
local notation "𝒫" => PowerlessSourceClass.structure_l (ℳ := 𝒱)
  (PowerlessRelativeClassCorrespondence.member_l hℳ B) hP

include hBase

private theorem binary_class_l {a b p : Raw}
    (ha : PowerlessRelativeClassCorrespondence.member_l hℳ B a)
    (hb : PowerlessRelativeClassCorrespondence.member_l hℳ B b)
    (hp : PowerlessRelativeFiniteHullAssignments.binary_l (𝒩 := 𝒱) a b p) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B p := by
  obtain ⟨q, hq⟩ := SecondOrderPairObjects.pair_exists_l hℳ a b
  apply PowerlessRelativeClassBasicClosure.union_l hℳ hBase
    (PowerlessRelativeClassPair.pair_l hℳ hBase ha hb hq)
  intro z
  have hp₀ : ε z p ↔ ε z a ∨ ε z b := hp z
  rw [hp₀]
  constructor
  · rintro (hza | hzb)
    · exact ⟨a, (hq a).mpr (Or.inl rfl), hza⟩
    · exact ⟨b, (hq b).mpr (Or.inr rfl), hzb⟩
  · rintro ⟨w, hwq, hzw⟩
    rcases (hq w).mp hwq with hwa | hwb
    · exact Or.inl (hwa ▸ hzw)
    · exact Or.inr (hwb ▸ hzw)

private theorem binary_raw_l (a b p : PowerlessRelativeClassStructure.type_l hℳ B)
    (hp : PowerlessRelativeFiniteHullAssignments.binary_l (𝒩 := 𝒩₀) a b p) :
    PowerlessRelativeFiniteHullAssignments.binary_l (𝒩 := 𝒱) a.val b.val p.val := by
  intro z
  constructor
  · intro hz
    exact (hp ⟨z, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase p.property hz⟩).mp hz
  · rintro (hz | hz)
    · exact (hp ⟨z, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase a.property hz⟩).mpr
        (Or.inl hz)
    · exact (hp ⟨z, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase b.property hz⟩).mpr
        (Or.inr hz)

theorem closed_l (I : Raw → Prop)
    (hIP : ∀ x, I x → PowerlessRelativeClassCorrespondence.member_l hℳ B x)
    (h : ∀ p ∈ family_m ([] : SortContext ℒ), PowerlessSourcePredicateRequests.closed_l
      (PowerlessSourceRequests.requests_m .truth p.2) (Env.empty : Env 𝒫 [] []) (fun x => I x.val)) :
    (∀ a b p, I a → I b → ThirdOrderSemantics.pair_l (ℳ := 𝒱) a b p → I p) ∧
      (∀ a b p, I a → I b →
        PowerlessRelativeFiniteHullAssignments.binary_l (𝒩 := 𝒱) a b p → I p) := by
  constructor
  · intro a b p ha hb hp
    let a₀ : carrier_l 𝒫 := ⟨a, hIP a ha⟩
    let b₀ : carrier_l 𝒫 := ⟨b, hIP b hb⟩
    let p₀ : carrier_l 𝒫 := ⟨p, PowerlessRelativeClassPair.pair_l hℳ hBase (hIP a ha) (hIP b hb) hp⟩
    let η : Env 𝒫 [.set, .set] [] := (Env.empty : Env 𝒫 [] [])
      |>.pushBound (sort := SetTheory.SetSort.set) a₀ |>.pushBound (sort := SetTheory.SetSort.set) b₀
    have hFree : PowerlessSourceClass.free_l η = Env.empty := by
      apply Env.ext <;> intro _ v <;> nomatch v
    have hClosed := h (Sigma.mk ([.set, .set] : SortContext ℒ)
      (.existsE .set (pair_matrix_m []))) List.mem_cons_self
    have hSome : ∃ y, (pair_matrix_m []).satisfies (η.pushBound y) := by
      refine ⟨p₀, (PowerlessRelativeClassSource.formula_l (hBase := hBase)
        (pair_matrix_m []) (η.pushBound p₀)).mp ?_⟩
      exact (PowerlessRelativeClassFunctionAbsolute.pair_l (hBase := hBase) _ _ _).mpr hp
    obtain ⟨q, hqI, hq⟩ := PowerlessSourcePredicateRequests.witness_l
      (pair_matrix_m []) η (fun x => I x.val) List.mem_cons_self
      (fun v => by cases v with
        | here => exact hb
        | there v => cases v with | here => exact ha | there v => nomatch v)
      (by simpa only [hFree, PowerlessSourceRequests.requests_m] using hClosed) hSome
    have hqNative := (PowerlessRelativeClassSource.formula_l (hBase := hBase)
      (pair_matrix_m []) (η.pushBound q)).mpr hq
    have hqRaw := (PowerlessRelativeClassFunctionAbsolute.pair_l (hBase := hBase) _ _ _).mp hqNative
    have hEq : p = q.val := SecondOrderQuotient.ext_l hℳ _ _ (fun z => (hp z).trans (hqRaw z).symm)
    exact hEq.symm ▸ hqI
  · intro a b p ha hb hp
    let a₀ : carrier_l 𝒫 := ⟨a, hIP a ha⟩
    let b₀ : carrier_l 𝒫 := ⟨b, hIP b hb⟩
    let p₀ : carrier_l 𝒫 := ⟨p, binary_class_l (hBase := hBase) (hIP a ha) (hIP b hb) hp⟩
    let η : Env 𝒫 [.set, .set] [] := (Env.empty : Env 𝒫 [] [])
      |>.pushBound (sort := SetTheory.SetSort.set) a₀ |>.pushBound (sort := SetTheory.SetSort.set) b₀
    have hFree : PowerlessSourceClass.free_l η = Env.empty := by
      apply Env.ext <;> intro _ v <;> nomatch v
    have hClosed := h (Sigma.mk ([.set, .set] : SortContext ℒ)
      (.existsE .set (binary_matrix_m [])))
      (List.mem_cons_of_mem _ List.mem_cons_self)
    have hSome : ∃ y, (binary_matrix_m []).satisfies (η.pushBound y) := by
      refine ⟨p₀, (PowerlessRelativeClassSource.formula_l (hBase := hBase)
        (binary_matrix_m []) (η.pushBound p₀)).mp ?_⟩
      change ∀ z : PowerlessRelativeClassStructure.type_l hℳ B,
        ε z.val p ↔ ε z.val a ∨ ε z.val b
      exact fun z => hp z.val
    obtain ⟨q, hqI, hq⟩ := PowerlessSourcePredicateRequests.witness_l
      (binary_matrix_m []) η (fun x => I x.val) List.mem_cons_self
      (fun v => by cases v with
        | here => exact hb
        | there v => cases v with | here => exact ha | there v => nomatch v)
      (by simpa only [hFree, PowerlessSourceRequests.requests_m] using hClosed) hSome
    have hqNative := (PowerlessRelativeClassSource.formula_l (hBase := hBase)
      (binary_matrix_m []) (η.pushBound q)).mpr hq
    have hqRaw := binary_raw_l (hBase := hBase) _ _ _ hqNative
    have hEq : p = q.val := SecondOrderQuotient.ext_l hℳ _ _ (fun z => (hp z).trans (hqRaw z).symm)
    exact hEq.symm ▸ hqI

#print axioms closed_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassOperationRequests
