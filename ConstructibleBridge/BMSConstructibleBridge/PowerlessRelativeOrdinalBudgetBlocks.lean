import BMSConstructibleBridge.PowerlessRelativeOrdinalBudgetReading
import BMSConstructibleBridge.PowerlessFunctionHistoryClass
import BMSConstructibleBridge.PowerlessRelativeClassNextLimitGraph
import BMSConstructibleBridge.PowerlessRelativeClassRelationalGraph
import BMSConstructibleBridge.SecondOrderCodedOrdinalFamilyBound

/-! # 规范序数预算块首的真实递归与类内图

原指标仍用规范最小数代表，块首零尾的方程则在原纯隶属商中读取：
零指标为 ξ，后继为下一非零极限，非零极限为此前块首的精确并。
这将实际 raw 预算图连接到单值算子的历史入类接口，而非给任意预算
证书附加可数性前提。共同序数／层允许高于 Ω，只作 Class 资格见证。
本模块不声称二维尾枚举、Class 可数性或严格截断界已经完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeOrdinalBudgetBlocks

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l mk_l)
open SecondOrderModel (num_l set_l zero_l succ_l)
open SecondOrderOrdinalBudgetGraph (spec_l)
open SecondOrderOrdinalBudgetOrder (base_l tail_l)
open SecondOrderOrdinalBudgetFunction (index_l index_covers_l index_injective_l)
open PowerlessRelativeOrdinalBudgetReading (index_member_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Ordinal" => SetTheory.Structure.IsOrdinal
  (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱)

variable (A : SecondOrderGraph.code_l ℳ) {Q N R S G : set_l ℳ} {r : num_l ℳ}
  (hQ : ∀ i j, SecondOrderPairing.relation_l Q i j ↔ SecondOrderBisimulation.eq_l A.real A.real i j)
  (hN : SecondOrderRootRepresentatives.spec_l A.real Q N A.root)
  (hRel : SecondOrderRootOrdinalRelation.spec_l A.real Q N R)
  (hG : spec_l S r R G) (hS : ∀ n, SecondOrderDomain.wf_l S n)

private abbrev hR := SecondOrderRootOrdinalRelation.wf_l hℳ A hQ hN hRel

private theorem irrefl_l (x : type_l hℳ) : ¬mem_l hℳ x x := by
  obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
  exact SecondOrderFoundation.irrefl_l hℳ X

/-- 原序数的后继指标恰增加一个完整内部 ω 块。 -/
theorem next_l (hA : Ordinal (mk_l hℳ A)) (hξ : Ordinal (base_l hℳ hS r))
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ (base_l hℳ hS r))
    (i n : num_l ℳ) (hi : SecondOrderModel.mem_l i N) (hn : SecondOrderModel.mem_l n N)
    (hSucc : PowerlessRelativeHierarchySemantics.successor_l hℳ
      (index_l hℳ A hN i hi) (index_l hℳ A hN n hn)) :
    PowerlessRelativeClassNextLimitGraph.next_l
      (tail_l hℳ hG hS (hR hℳ A hQ hN hRel) i (zero_l ℳ))
      (tail_l hℳ hG hS (hR hℳ A hQ hN hRel) n (zero_l ℳ)) := by
  let T (j k : num_l ℳ) := tail_l hℳ hG hS (hR hℳ A hQ hN hRel) j k
  have hT (j k : num_l ℳ) (hj : SecondOrderModel.mem_l j N) : Ordinal (T j k) :=
    PowerlessRelativeOrdinalBudgetReading.ordinal_l hℳ A hQ hN hRel hG hS hA hξ j k hj
  have hin : SecondOrderPairing.relation_l R i n :=
    (index_member_l hℳ A hQ hN hRel i n hi hn).mp ((hSucc _).mpr (Or.inr rfl))
  refine ⟨SecondOrderOrdinalBudgetOrder.earlier_l hℳ hG hS (hR hℳ A hQ hN hRel)
    hin (zero_l ℳ) (zero_l ℳ),
    SecondOrderOrdinalBudgetFinite.limit_l hℳ hG hS (hR hℳ A hQ hN hRel) hLimit n, ?_⟩
  intro z hz hiz hzLimit
  rcases (SecondOrderOrdinalBudgetFinite.zero_reading_l hℳ hG hS
    (hR hℳ A hQ hN hRel) n z).mp hz with hz | ⟨j, k, hjn, rfl⟩
  · have hzi := SecondOrderOrdinalBudgetFinite.base_subset_l hℳ hG hS
      (hR hℳ A hQ hN hRel) i (zero_l ℳ) z hz
    exact irrefl_l hℳ (T i (zero_l ℳ))
      ((hT i (zero_l ℳ) hi).transitive z hzi (T i (zero_l ℳ)) hiz)
  · have hj : SecondOrderModel.mem_l j N := ((hRel j n).mp hjn).1
    have hjn' := (index_member_l hℳ A hQ hN hRel j n hj hn).mpr hjn
    rcases (hSucc _).mp hjn' with hji | hji
    · have hEdge := (index_member_l hℳ A hQ hN hRel j i hj hi).mp hji
      have hzi := SecondOrderOrdinalBudgetOrder.earlier_l hℳ hG hS
        (hR hℳ A hQ hN hRel) hEdge k (zero_l ℳ)
      exact irrefl_l hℳ (T i (zero_l ℳ))
        ((hT i (zero_l ℳ) hi).transitive (T j k) hzi (T i (zero_l ℳ)) hiz)
    · have hji' := index_injective_l hℳ A hQ hN hj hi hji
      subst j
      rcases SecondOrderModel.predecessor_l hℳ k with rfl | ⟨k', rfl⟩
      · exact irrefl_l hℳ _ hiz
      · have hSucc' := SecondOrderOrdinalBudgetFinite.successor_l hℳ hG hS
          (hR hℳ A hQ hN hRel) i k'
        have hk : mem_l hℳ (T i k') (T i (succ_l k')) := (hSucc' _).mpr (Or.inr rfl)
        obtain ⟨w, hw, hkw⟩ := hzLimit.2 _ hk
        rcases (hSucc' w).mp hw with hw | hw
        · exact irrefl_l hℳ (T i k') ((hT i k' hi).transitive w hw (T i k') hkw)
        · exact irrefl_l hℳ _ (hw ▸ hkw)

/-- 非零极限指标的块首是所有此前块首的精确并；量词覆盖全部 raw 对象。 -/
theorem union_l (hA : Ordinal (mk_l hℳ A)) (hξ : Ordinal (base_l hℳ hS r))
    {F : type_l hℳ}
    (hRead : ∀ x y, value_l (ℳ := 𝒱) F x y ↔ ∃ i, ∃ hi : SecondOrderModel.mem_l i N,
      x = index_l hℳ A hN i hi ∧ y = tail_l hℳ hG hS (hR hℳ A hQ hN hRel) i (zero_l ℳ))
    (n : num_l ℳ) (hn : SecondOrderModel.mem_l n N)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ (index_l hℳ A hN n hn)) :
    PowerlessRelativeHierarchySemantics.union_l hℳ F (index_l hℳ A hN n hn)
      (tail_l hℳ hG hS (hR hℳ A hQ hN hRel) n (zero_l ℳ)) := by
  let T (i j : num_l ℳ) := tail_l hℳ hG hS (hR hℳ A hQ hN hRel) i j
  have hnA : mem_l hℳ (index_l hℳ A hN n hn) (mk_l hℳ A) :=
    (index_covers_l hℳ A hQ hN _).mpr ⟨n, hn, rfl⟩
  intro x
  constructor
  · intro hx
    rcases (SecondOrderOrdinalBudgetFinite.zero_reading_l hℳ hG hS
      (hR hℳ A hQ hN hRel) n x).mp hx with hx | ⟨i, j, hin, rfl⟩
    · obtain ⟨b, hb⟩ := hLimit.1
      obtain ⟨i, hi, hbi⟩ := (index_covers_l hℳ A hQ hN b).mp
        (hA.transitive (index_l hℳ A hN n hn) hnA b hb)
      exact ⟨b, T i (zero_l ℳ), hb, (hRead _ _).mpr ⟨i, hi, hbi, rfl⟩,
        SecondOrderOrdinalBudgetFinite.base_subset_l hℳ hG hS
          (hR hℳ A hQ hN hRel) i (zero_l ℳ) x hx⟩
    · have hi : SecondOrderModel.mem_l i N := ((hRel i n).mp hin).1
      have hin' := (index_member_l hℳ A hQ hN hRel i n hi hn).mpr hin
      obtain ⟨b, hb, hib⟩ := hLimit.2 _ hin'
      obtain ⟨k, hk, hbk⟩ := (index_covers_l hℳ A hQ hN b).mp
        (hA.transitive (index_l hℳ A hN n hn) hnA b hb)
      have hik := (index_member_l hℳ A hQ hN hRel i k hi hk).mp (hbk ▸ hib)
      exact ⟨b, T k (zero_l ℳ), hb, (hRead _ _).mpr ⟨k, hk, hbk, rfl⟩,
        SecondOrderOrdinalBudgetOrder.earlier_l hℳ hG hS
          (hR hℳ A hQ hN hRel) hik j (zero_l ℳ)⟩
  · rintro ⟨b, d, hb, hFd, hxd⟩
    obtain ⟨i, hi, rfl, rfl⟩ := (hRead b d).mp hFd
    have hin := (index_member_l hℳ A hQ hN hRel i n hi hn).mp hb
    have hdn := SecondOrderOrdinalBudgetOrder.earlier_l hℳ hG hS
      (hR hℳ A hQ hN hRel) hin (zero_l ℳ) (zero_l ℳ)
    exact (PowerlessRelativeOrdinalBudgetReading.ordinal_l hℳ A hQ hN hRel hG hS
      hA hξ n (zero_l ℳ) hn).transitive (T i (zero_l ℳ)) hdn x hxd

variable {B : type_l hℳ}

/-- 两个 raw 序数的真正共同严格界，不要求界可数或低于截断。 -/
private theorem bounds_l {ξ δ : type_l hℳ} (hξ : Ordinal ξ) (hδ : Ordinal δ) :
    ∃ γ, Ordinal γ ∧ mem_l hℳ ξ γ ∧ mem_l hℳ δ γ := by
  rcases SecondOrderOrdinalComparison.compare_l hℳ hξ hδ with h | h | h
  · obtain ⟨γ, hγ, hδγ, _⟩ := SecondOrderOrdinalLimitDerives.exists_l hℳ δ hδ
    exact ⟨γ, hγ, h.symm ▸ hδγ, hδγ⟩
  · obtain ⟨γ, hγ, hδγ, _⟩ := SecondOrderOrdinalLimitDerives.exists_l hℳ δ hδ
    exact ⟨γ, hγ, hγ.transitive δ hδγ ξ h, hδγ⟩
  · obtain ⟨γ, hγ, hξγ, _⟩ := SecondOrderOrdinalLimitDerives.exists_l hℳ ξ hξ
    exact ⟨γ, hγ, hξγ, hγ.transitive ξ hξγ δ h⟩

/-- 同一完整 raw 块首图实际进入 Class；不存在预供的类内预算图。 -/
theorem class_l (K : source_coding_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hA : Ordinal (mk_l hℳ A)) (hξ : Ordinal (base_l hℳ hS r))
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ (base_l hℳ hS r))
    {F Y : type_l hℳ} (hF : map_l (ℳ := 𝒱) F (mk_l hℳ A) Y)
    (hRead : ∀ x y, value_l (ℳ := 𝒱) F x y ↔ ∃ i, ∃ hi : SecondOrderModel.mem_l i N,
      x = index_l hℳ A hN i hi ∧ y = tail_l hℳ hG hS (hR hℳ A hQ hN hRel) i (zero_l ℳ)) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B F := by
  let ξ := base_l hℳ hS r
  let T (i j : num_l ℳ) := tail_l hℳ hG hS (hR hℳ A hQ hN hRel) i j
  let φ : Formula ℒ [] [.set, .set] := .existsE .set <|
    SecondOrderObjectSyntax.value_m (.fvar (.there .here)) (.bvar .here) (.fvar .here)
  let η : Env 𝒱 [] [.set] := Env.empty.pushFree F
  have hφ (y : type_l hℳ) : φ.satisfies (η.pushFree y) ↔
      ∃ x, value_l (ℳ := 𝒱) F x y := by
    simp only [φ, Formula.satisfies, value_formula_l, Term.eval]
    rfl
  obtain ⟨C, hC⟩ := (SecondOrderSeparationAxiom.schema_l hℳ φ η).mp
    (SecondOrderSeparationAxiom.models_l hℳ φ η) Y
  have hRange (y : type_l hℳ) : mem_l hℳ y C ↔ ∃ x, value_l (ℳ := 𝒱) F x y := by
    constructor
    · exact fun hy => (hφ y).mp ((hC y).mp hy).2
    · rintro ⟨x, hxy⟩
      exact (hC y).mpr ⟨(SecondOrderFunctionProperties.value_mem_l hℳ hF hxy).2,
        (hφ y).mpr ⟨x, hxy⟩⟩
  have hCOrd (y : type_l hℳ) (hy : mem_l hℳ y C) : Ordinal y := by
    obtain ⟨x, hxy⟩ := (hRange y).mp hy
    obtain ⟨i, hi, _, rfl⟩ := (hRead x y).mp hxy
    exact PowerlessRelativeOrdinalBudgetReading.ordinal_l hℳ A hQ hN hRel hG hS
      hA hξ i (zero_l ℳ) hi
  obtain ⟨δ, hδ, hBound⟩ := SecondOrderCodedOrdinalFamilyBound.set_bound_l hCOrd
  obtain ⟨γ, hγ, hξγ, hδγ⟩ := bounds_l hℳ hξ hδ
  have hValues (x y : type_l hℳ) (hxy : value_l (ℳ := 𝒱) F x y) : mem_l hℳ y γ :=
    hγ.transitive δ hδγ y (hBound y ((hRange y).mpr ⟨x, hxy⟩))
  obtain ⟨W, hW⟩ := PowerlessRelativeOrdinalCoverage.level_exists_l hℳ hBase hγ
  have hValuesW (x y : type_l hℳ) (hxy : value_l (ℳ := 𝒱) F x y) : mem_l hℳ y W :=
    PowerlessRelativeOrdinalCoverage.covered_l hℳ K hBase γ W hW y (hValues x y hxy)
  have hξW : mem_l hℳ ξ W :=
    PowerlessRelativeOrdinalCoverage.covered_l hℳ K hBase γ W hW ξ hξγ
  have hFW : map_l (ℳ := 𝒱) F (mk_l hℳ A) W := by
    constructor
    · intro p hp
      obtain ⟨x, y, hx, _, hxy⟩ := hF.1 p hp
      exact ⟨x, y, hx, hValuesW x y ⟨p, hp, hxy⟩, hxy⟩
    · intro x hx
      obtain ⟨y, ⟨_, hxy⟩, _⟩ := hF.2 x hx
      exact ⟨y, ⟨hValuesW x y hxy, hxy⟩, fun z hz =>
        SecondOrderFunctionProperties.value_unique_l hℳ hF hz.2 hxy⟩
  let Γ : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨γ, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase hγ⟩
  let ψ : Formula ℒ [] [.set, .set] :=
    PowerlessRelativeClassNextLimitGraph.formula_m (.fvar .here) (.fvar (.there .here))
  obtain ⟨D, hD⟩ := PowerlessRelativeClassRelationalGraph.exists_ambient_l
    (hBase := hBase) (φ := ψ) (PowerlessRelativeClassNextLimitGraph.delta_l _ _) Env.empty Γ Γ
  have hDRead (x y : type_l hℳ) : value_l (ℳ := 𝒱) D.val x y ↔
      mem_l hℳ x γ ∧ mem_l hℳ y γ ∧ PowerlessRelativeClassNextLimitGraph.next_l x y :=
    (hD x y).trans (and_congr Iff.rfl (and_congr Iff.rfl
      (PowerlessRelativeClassNextLimitGraph.formula_l _ _ _)))
  have hFunctional : PowerlessFunctionHistoryAgreement.functional_l hℳ D.val := by
    intro x y z hxy hxz
    obtain ⟨_, hy, hxy⟩ := (hDRead x y).mp hxy
    obtain ⟨_, hz, hxz⟩ := (hDRead x z).mp hxz
    exact PowerlessRelativeClassNextLimitGraph.unique_l
      (SetTheory.Structure.IsOrdinal.mem hγ hy) (SetTheory.Structure.IsOrdinal.mem hγ hz) hxy hxz
  have hHistory : PowerlessHierarchyLightHistory.history_l hℳ ξ D.val (mk_l hℳ A) W F := by
    refine ⟨hFW, ?_⟩
    rintro a y ⟨ha, hxy⟩
    obtain ⟨n, hn, rfl, rfl⟩ := (hRead a y).mp hxy
    have haOrd : Ordinal (index_l hℳ A hN n hn) := SetTheory.Structure.IsOrdinal.mem hA ha
    rcases PowerlessHierarchyLightHistoryBudgetInduction.cases_l hℳ haOrd with
      hZero | ⟨b, hSucc⟩ | hLimitA
    · exact Or.inl ⟨hZero, PowerlessRelativeOrdinalBudgetReading.empty_eq_base_l
        hℳ A hQ hN hRel hG hS n hn hZero⟩
    · have hb : mem_l hℳ b (index_l hℳ A hN n hn) := (hSucc b).mpr (Or.inr rfl)
      obtain ⟨i, hi, hbi⟩ := (index_covers_l hℳ A hQ hN b).mp
        (hA.transitive (index_l hℳ A hN n hn) ha b hb)
      have hFb : value_l (ℳ := 𝒱) F b (T i (zero_l ℳ)) :=
        (hRead _ _).mpr ⟨i, hi, hbi, rfl⟩
      exact Or.inr (Or.inl ⟨b, T i (zero_l ℳ), hSucc, hFb,
        (hDRead _ _).mpr ⟨hValues b _ hFb, hValues _ _ hxy,
          next_l hℳ A hQ hN hRel hG hS hA hξ hLimit i n hi hn (hbi ▸ hSucc)⟩⟩)
    · exact Or.inr (Or.inr ⟨hLimitA,
        union_l hℳ A hQ hN hRel hG hS hA hξ hRead n hn hLimitA⟩)
  exact PowerlessFunctionHistoryClass.class_l hℳ K hBase D hFunctional hξW hW hA hHistory

/-- 原理解真正给出同一块首函数，其 Class 资格不再是调用端前提。 -/
theorem exists_l (K : source_coding_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hA : Ordinal (mk_l hℳ A)) (hξ : Ordinal (base_l hℳ hS r))
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ (base_l hℳ hS r)) :
    ∃ Y F : type_l hℳ, map_l (ℳ := 𝒱) F (mk_l hℳ A) Y ∧
      PowerlessRelativeClassCorrespondence.member_l hℳ B F ∧
        ∀ x y, value_l (ℳ := 𝒱) F x y ↔ ∃ i, ∃ hi : SecondOrderModel.mem_l i N,
          x = index_l hℳ A hN i hi ∧
            y = tail_l hℳ hG hS (hR hℳ A hQ hN hRel) i (zero_l ℳ) := by
  obtain ⟨Y, F, hF, hRead⟩ := SecondOrderOrdinalBudgetFunction.from_spec_l
    hℳ hS A hQ hN hRel hG (zero_l ℳ)
  change map_l (ℳ := 𝒱) F (mk_l hℳ A) Y at hF
  exact ⟨Y, F, hF, class_l hℳ A hQ hN hRel hG hS K hBase hA hξ hLimit hF hRead, hRead⟩

#print axioms next_l
#print axioms union_l
#print axioms class_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeOrdinalBudgetBlocks
