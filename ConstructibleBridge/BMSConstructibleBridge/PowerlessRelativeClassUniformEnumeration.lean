import BMSConstructibleBridge.PowerlessRelativeClassProductEnumeration
import BMSConstructibleBridge.PowerlessRelativeClassOntoCountability

/-! # 实际类内枚举族的可数合并

对象语言为纯隶属 ℒ，背景为原 SecondOrderArithmetic.theory_m。索引函数
J 和其值域 R 都须为实际 Class 对象，每个 J(i) 须为实际集合函数。已有
覆盖见证才给出合并后的类内满射；不从逐个存在枚举推出 J 的存在。

这是对象推导的语义辅助接口。首个不可数序数的后续使用仍须构造统一
枚举族；本文件没有证明任意 ω→Ω 共尾函数能取得这样的族。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassUniformEnumeration

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

/-- 用有序对的两个编号依次读取枚举族和族成员；所有量词均有实际母界。 -/
def entry_m {Γ Δ : SortContext ℒ} (ω R J p x : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <|
    membershipLevyBound.boundedExists (up ω) <|
      membershipLevyBound.boundedExists (up (up R)) <|
        let i : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
        let k : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
        let j : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar .here
        let lift (t : Term ℒ Γ Δ .set) := up (up (up t))
        .conj (PowerlessPairBounded.ordered_m i k (lift p)) <|
          .conj (PowerlessValueBounded.formula_m (lift J) i j)
            (PowerlessValueBounded.formula_m j k (lift x))

theorem entry_delta_l {Γ Δ : SortContext ℒ} (ω R J p x : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (entry_m ω R J p x) :=
  .bounded_exists ω (.bounded_exists (up ω) (.bounded_exists (up (up R))
    (.conj (PowerlessPairBounded.ordered_delta_l _ _ _)
      (.conj (PowerlessValueBounded.delta_l _ _ _) (PowerlessValueBounded.delta_l _ _ _)))))

def entry_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω R J p x : carrier_l 𝒩) : Prop :=
  ∃ i, member_l 𝒩 i ω ∧ ∃ k, member_l 𝒩 k ω ∧ ∃ j, member_l 𝒩 j R ∧
    ordered_l (ℳ := 𝒩) i k p ∧ value_l (ℳ := 𝒩) J i j ∧ value_l (ℳ := 𝒩) j k x

theorem entry_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ) (ω R J p x : Term ℒ Γ Δ .set) :
    (entry_m ω R J p x).satisfies η ↔
      entry_l (ω.eval η) (R.eval η) (J.eval η) (p.eval η) (x.eval η) := by
  simp only [entry_m, entry_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessPairBounded.ordered_formula_l, PowerlessValueBounded.formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "ClassModel" => structure_l hℳ B hBase

private theorem identity_l (ω : type_l hℳ B) :
    ∃ I : type_l hℳ B, map_l (ℳ := ClassModel) I ω ω ∧
      ∀ i : type_l hℳ B, mem_l hℳ i.val ω.val → value_l (ℳ := ClassModel) I i i := by
  let φ : Formula ℒ [] [.set, .set] := .equal (.fvar (.there .here)) (.fvar .here)
  obtain ⟨I, hI, hRead⟩ := PowerlessRelativeClassFunctionRelation.exists_l
    (hBase := hBase) (φ := φ) (.equal _ _) Env.empty ω ω (by
      intro i hi
      exact ⟨i, ⟨hi, rfl⟩, fun j hj => hj.2⟩)
  exact ⟨I, hI, fun i hi => (hRead i i).mpr ⟨hi, hi, rfl⟩⟩

theorem entry_unique_l {ω R J X p x y : type_l hℳ B}
    (hJ : map_l (ℳ := ClassModel) J ω R)
    (hEach : ∀ i j : type_l hℳ B, mem_l hℳ i.val ω.val → mem_l hℳ j.val R.val →
      value_l (ℳ := ClassModel) J i j → map_l (ℳ := ClassModel) j ω X)
    (hx : entry_l («𝒩» := ClassModel) ω R J p x)
    (hy : entry_l («𝒩» := ClassModel) ω R J p y) : x = y := by
  obtain ⟨i, hi, k, _, j, hj, hp, hij, hkx⟩ := hx
  obtain ⟨i', _, k', _, j', _, hp', hij', hky⟩ := hy
  have hCoords := (SecondOrderPairObjects.ordered_eq_l hℳ
    ((PowerlessRelativeClassFunctionAbsolute.ordered_l i' k' p).mp hp')
    ((PowerlessRelativeClassFunctionAbsolute.ordered_l i k p).mp hp)).mp rfl
  have hiEq : i' = i := Subtype.ext hCoords.1
  have hkEq : k' = k := Subtype.ext hCoords.2
  subst i'
  subst k'
  have hjEq := PowerlessRelativeClassFunctionComposition.value_unique_l hJ hij' hij
  subst j'
  exact PowerlessRelativeClassFunctionComposition.value_unique_l (hEach i j hi hj hij) hkx hky

/-- 合并一个已实际存在的内部 ω 枚举族；覆盖前提不包含任何选择函数。 -/
theorem exists_l {ω R J X : type_l hℳ B}
    (hω : omega_l (ℳ := ClassModel) ω) (hJ : map_l (ℳ := ClassModel) J ω R)
    (hEach : ∀ i j : type_l hℳ B, mem_l hℳ i.val ω.val → mem_l hℳ j.val R.val →
      value_l (ℳ := ClassModel) J i j → map_l (ℳ := ClassModel) j ω X)
    (hCover : ∀ x : type_l hℳ B, mem_l hℳ x.val X.val →
      ∃ i : type_l hℳ B, mem_l hℳ i.val ω.val ∧ ∃ j : type_l hℳ B,
        mem_l hℳ j.val R.val ∧ value_l (ℳ := ClassModel) J i j ∧
          ∃ k : type_l hℳ B, mem_l hℳ k.val ω.val ∧ value_l (ℳ := ClassModel) j k x) :
    ∃ U : type_l hℳ B, map_l (ℳ := ClassModel) U ω X ∧
      ∀ x : type_l hℳ B, mem_l hℳ x.val X.val →
        ∃ n : type_l hℳ B, mem_l hℳ n.val ω.val ∧ value_l (ℳ := ClassModel) U n x := by
  obtain ⟨P, hP⟩ := PowerlessRelativeClassProduct.exists_l hBase ω ω
  let η : Env ClassModel [] [.set, .set, .set] :=
    ((Env.empty.pushFree J).pushFree R).pushFree ω
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] :=
    entry_m (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here))))) (.fvar .here) (.fvar (.there .here))
  have hφ (p x : type_l hℳ B) : φ.satisfies ((η.pushFree x).pushFree p) ↔
      entry_l («𝒩» := ClassModel) ω R J p x :=
    entry_formula_l ((η.pushFree x).pushFree p) _ _ _ _ _
  obtain ⟨H, hH, hRead⟩ := PowerlessRelativeClassFunctionRelation.exists_l
    (hBase := hBase) (φ := φ) (entry_delta_l _ _ _ _ _) η P X (by
      intro p hp
      obtain ⟨i, k, hi, hk, hPair⟩ := (hP p).mp hp
      obtain ⟨j, ⟨hj, hij⟩, _⟩ := hJ.2 i hi
      obtain ⟨x, ⟨hx, hkx⟩, _⟩ := (hEach i j hi hj hij).2 k hk
      have hEntry : entry_l («𝒩» := ClassModel) ω R J p x :=
        ⟨i, hi, k, hk, j, hj, hPair, hij, hkx⟩
      exact ⟨x, ⟨hx, (hφ p x).mpr hEntry⟩,
        fun y hy => entry_unique_l hJ hEach ((hφ p y).mp hy.2) hEntry⟩)
  obtain ⟨I, hI, hId⟩ := identity_l (hBase := hBase) ω
  have hIdOnto : ∀ i : type_l hℳ B, mem_l hℳ i.val ω.val →
      ∃ n : type_l hℳ B, mem_l hℳ n.val ω.val ∧ value_l (ℳ := ClassModel) I n i :=
    fun i hi => ⟨i, hi, hId i hi⟩
  obtain ⟨E, hE, hOnto⟩ := PowerlessRelativeClassProductEnumeration.exists_l
    hω hI hI hIdOnto hIdOnto hP
  obtain ⟨U, hU, hURead⟩ := PowerlessRelativeClassFunctionComposition.exists_l hE hH
  refine ⟨U, hU, ?_⟩
  intro x hx
  obtain ⟨i, hi, j, hj, hij, k, hk, hkx⟩ := hCover x hx
  obtain ⟨p₀, hp₀⟩ := SecondOrderPairObjects.ordered_exists_l hℳ i.val k.val
  let p : type_l hℳ B := ⟨p₀,
    PowerlessRelativeClassPair.ordered_l hℳ hBase i.property k.property hp₀⟩
  have hpPair : ordered_l (ℳ := ClassModel) i k p :=
    (PowerlessRelativeClassFunctionAbsolute.ordered_l i k p).mpr hp₀
  have hp := (hP p).mpr ⟨i, k, hi, hk, hpPair⟩
  have hpx := (hRead p x).mpr
    ⟨hp, hx, (hφ p x).mpr ⟨i, hi, k, hk, j, hj, hpPair, hij, hkx⟩⟩
  obtain ⟨n, hn, hnp⟩ := hOnto p hp
  exact ⟨n, hn, (hURead n x).mpr ⟨hn, hx, p, hp, hnp, hpx⟩⟩

/-- 首个类内不可数序数不可能由一个已实际存在的这样的枚举族覆盖。 -/
theorem cutoff_l (K : source_coding_l hℳ) {ω R J Ω : type_l hℳ B}
    (hω : omega_l (ℳ := ClassModel) ω)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B ω.val Ω.val)
    (hJ : map_l (ℳ := ClassModel) J ω R)
    (hEach : ∀ i j : type_l hℳ B, mem_l hℳ i.val ω.val → mem_l hℳ j.val R.val →
      value_l (ℳ := ClassModel) J i j → map_l (ℳ := ClassModel) j ω Ω)
    (hCover : ∀ x : type_l hℳ B, mem_l hℳ x.val Ω.val →
      ∃ i : type_l hℳ B, mem_l hℳ i.val ω.val ∧ ∃ j : type_l hℳ B,
        mem_l hℳ j.val R.val ∧ value_l (ℳ := ClassModel) J i j ∧
          ∃ k : type_l hℳ B, mem_l hℳ k.val ω.val ∧ value_l (ℳ := ClassModel) j k x) :
    False := by
  obtain ⟨U, hU, hOnto⟩ := exists_l hω hJ hEach hCover
  exact PowerlessRelativeClassOntoCountability.cutoff_l (hBase := hBase) K
    ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mp hω) hΩ U.property
    ((PowerlessRelativeClassFunctionAbsolute.map_l U ω Ω).mp hU)
    ((PowerlessRelativeClassFunctionAbsolute.onto_l U ω Ω).mp hOnto)

#print axioms entry_delta_l
#print axioms entry_unique_l
#print axioms exists_l
#print axioms cutoff_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassUniformEnumeration
