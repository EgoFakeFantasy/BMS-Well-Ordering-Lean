import BMSConstructibleBridge.PowerlessRelativeClassNextLimitGraph
import BMSConstructibleBridge.PowerlessRelativeClassLimitSuccessorGraph
import BMSConstructibleBridge.PowerlessRelativeClassFunctionIteration
import BMSConstructibleBridge.PowerlessRelativeClassLimitParameterBounds
import BMSConstructibleBridge.PowerlessRelativeClassProduct
import BMSConstructibleBridge.SecondOrderOrdinalDoubleTailCofinal
import BMSConstructibleBridge.SecondOrderRootedNumericFunction
import BMSConstructibleBridge.SecondOrderFiniteFunctionRestriction
import BMSConstructibleBridge.SecondOrderFiniteFunctionAgreement

/-! # 实际双尾的块首迭代与类内二维值图

对象背景为原 Z₂，所有自然数指标都是模型内部数。最终序数先由
OrdinalCoverage 取得 Class 资格；块首按下一非零极限迭代，块内按后继
迭代。共同母层只界定有限图，不假定其低于任何截断或最终序数可数。
二维检查式为纯隶属 Δ₀，实际 Class 图读取原 double-tail 的全部节点。

本文件给数学辅助和具体检查式 AST；双尾存在／可数闭句的普通 Derives
须由调用端连接原 double-tail 守卫，不能把宿主 hG 当成对象公式。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassDoubleTailFunction

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l mk_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open SecondOrderModel (num_l zero_l succ_l)
open SecondOrderOrdinalDoubleTailOrder (base_l tail_l reading_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}
  {S G : SecondOrderModel.set_l ℳ} {r : num_l ℳ}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₁" => structure_l hℳ B hBase
local notation "Ordinal" => SetTheory.Structure.IsOrdinal
  (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱)

private theorem irrefl_l (x : SecondOrderQuotient.type_l hℳ) : ¬mem_l hℳ x x := by
  obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
  exact SecondOrderFoundation.irrefl_l hℳ X

theorem successor_l (hG : SecondOrderOrdinalDoubleTailGraph.spec_l S r G)
    (hS : ∀ a, SecondOrderDomain.wf_l S a) (n m : num_l ℳ) :
    PowerlessRelativeHierarchySemantics.successor_l hℳ
      (tail_l hℳ hG hS n m) (tail_l hℳ hG hS n (succ_l m)) := by
  intro x
  rw [reading_l hℳ hG hS n (succ_l m) x]
  constructor
  · rintro (hx | hx | ⟨i, j, hij, hx⟩)
    · exact Or.inl ((reading_l hℳ hG hS n m x).mpr (Or.inl hx))
    · exact Or.inl ((reading_l hℳ hG hS n m x).mpr (Or.inr (Or.inl hx)))
    · rcases hij with hi | ⟨hin, hj⟩
      · exact Or.inl ((reading_l hℳ hG hS n m x).mpr (Or.inr (Or.inr ⟨i, j, Or.inl hi, hx⟩)))
      · subst i
        rcases (SecondOrderOrdinalTailMembers.lt_succ_l hℳ j m).mp hj with hj | hEq
        · exact Or.inl ((reading_l hℳ hG hS n m x).mpr
            (Or.inr (Or.inr ⟨n, j, Or.inr ⟨rfl, hj⟩, hx⟩)))
        · subst j
          exact Or.inr hx
  · rintro (hx | hx)
    · rcases (reading_l hℳ hG hS n m x).mp hx with hx | hx | ⟨i, j, hij, hx⟩
      · exact Or.inl hx
      · exact Or.inr (Or.inl hx)
      · rcases hij with hi | ⟨hin, hj⟩
        · exact Or.inr (Or.inr ⟨i, j, Or.inl hi, hx⟩)
        · subst i
          exact Or.inr (Or.inr ⟨n, j, Or.inr ⟨rfl,
            (SecondOrderOrdinalTailMembers.lt_succ_l hℳ j m).mpr (Or.inl hj)⟩, hx⟩)
    · exact Or.inr (Or.inr ⟨n, m, Or.inr ⟨rfl,
        (SecondOrderOrdinalTailMembers.lt_succ_l hℳ m m).mpr (Or.inr rfl)⟩, hx⟩)

theorem block_next_l (hG : SecondOrderOrdinalDoubleTailGraph.spec_l S r G)
    (hS : ∀ a, SecondOrderDomain.wf_l S a) (hα : Ordinal (base_l hℳ hS r))
    (n : num_l ℳ) : PowerlessRelativeClassNextLimitGraph.next_l
      (tail_l hℳ hG hS n (zero_l ℳ)) (tail_l hℳ hG hS (succ_l n) (zero_l ℳ)) := by
  have hT (i j : num_l ℳ) : Ordinal (tail_l hℳ hG hS i j) :=
    SecondOrderOrdinalDoubleTailOrder.ordinal_l hℳ hG hS hα i j
  have hSelf := irrefl_l (hℳ := hℳ)
  refine ⟨(reading_l hℳ hG hS _ _ _).mpr (Or.inr (Or.inr ⟨n, zero_l ℳ,
    Or.inl ((SecondOrderOrdinalTailMembers.lt_succ_l hℳ n n).mpr (Or.inr rfl)), rfl⟩)),
    SecondOrderOrdinalDoubleTailCofinal.block_limit_l hℳ hG hS n, ?_⟩
  intro z hz hx hLimit
  rcases (reading_l hℳ hG hS (succ_l n) (zero_l ℳ) z).mp hz with hz | rfl | ⟨i, j, hij, rfl⟩
  · have hzT := (reading_l hℳ hG hS n (zero_l ℳ) z).mpr (Or.inl hz)
    exact hSelf (tail_l hℳ hG hS n (zero_l ℳ))
      ((hT n (zero_l ℳ)).transitive z hzT (tail_l hℳ hG hS n (zero_l ℳ)) hx)
  · have hαT := (reading_l hℳ hG hS n (zero_l ℳ) _).mpr (Or.inr (Or.inl rfl))
    exact hSelf (tail_l hℳ hG hS n (zero_l ℳ)) ((hT n (zero_l ℳ)).transitive (base_l hℳ hS r) hαT
      (tail_l hℳ hG hS n (zero_l ℳ)) hx)
  · have hi : SecondOrderOrder.lt_l i (succ_l n) := by
      rcases hij with hi | ⟨_, hj⟩
      · exact hi
      · exact (SecondOrderTriangularMonotone.zero_bound_l hℳ j hj).elim
    rcases (SecondOrderOrdinalTailMembers.lt_succ_l hℳ i n).mp hi with hi | hin
    · have hzT := (reading_l hℳ hG hS n (zero_l ℳ) _).mpr (Or.inr (Or.inr ⟨i, j, Or.inl hi, rfl⟩))
      exact hSelf (tail_l hℳ hG hS n (zero_l ℳ)) ((hT n (zero_l ℳ)).transitive (tail_l hℳ hG hS i j) hzT
        (tail_l hℳ hG hS n (zero_l ℳ)) hx)
    · subst i
      rcases SecondOrderModel.predecessor_l hℳ j with rfl | ⟨k, rfl⟩
      · exact hSelf _ hx
      · have hSucc := successor_l (hℳ := hℳ) hG hS n k
        have hk : mem_l hℳ (tail_l hℳ hG hS n k) (tail_l hℳ hG hS n (succ_l k)) :=
          (hSucc _).mpr (Or.inr rfl)
        obtain ⟨w, hw, hkw⟩ := hLimit.2 _ hk
        rcases (hSucc w).mp hw with hw | hw
        · exact hSelf (tail_l hℳ hG hS n k) ((hT n k).transitive w hw (tail_l hℳ hG hS n k) hkw)
        · exact hSelf _ (hw ▸ hkw)

private theorem numeric_function_l (K : source_coding_l hℳ)
    (hG : SecondOrderOrdinalDoubleTailGraph.spec_l S r G)
    (hS : ∀ a, SecondOrderDomain.wf_l S a)
    {E : SecondOrderModel.set_l ℳ} (hE : SecondOrderFunctions.function_l E)
    (t : num_l ℳ → num_l ℳ → Prop)
    (hRead : ∀ n m, SecondOrderPairing.relation_l E n m ↔ t n m)
    (C : SecondOrderQuotient.type_l hℳ)
    (hRange : ∀ n m, t n m → mem_l hℳ (mk_l hℳ ⟨G, m,
      SecondOrderOrdinalDoubleTailGraph.wf_l hℳ hG hS m⟩) C) :
    ∃ F : SecondOrderQuotient.type_l hℳ, map_l (ℳ := 𝒱) F K.omega C ∧
      ∀ x y, value_l (ℳ := 𝒱) F x y ↔ ∃ n m, t n m ∧
        x = (numberCode_l K n).val ∧ y = mk_l hℳ ⟨G, m,
          SecondOrderOrdinalDoubleTailGraph.wf_l hℳ hG hS m⟩ := by
  obtain ⟨F, hF, hValue⟩ := SecondOrderRootedNumericFunction.exists_l K G
    (SecondOrderOrdinalDoubleTailGraph.wf_l hℳ hG hS) hE C
    (fun n m hnm => hRange n m ((hRead n m).mp hnm))
  exact ⟨F, hF, fun x y => (hValue x y).trans
    (exists_congr fun n => exists_congr fun m => and_congr (hRead n m) Iff.rfl)⟩

theorem blocks_exists_l (K : source_coding_l hℳ)
    (hG : SecondOrderOrdinalDoubleTailGraph.spec_l S r G)
    (hS : ∀ a, SecondOrderDomain.wf_l S a) (C : SecondOrderQuotient.type_l hℳ)
    (hC : ∀ n m, mem_l hℳ (tail_l hℳ hG hS n m) C) :
    ∃ F : SecondOrderQuotient.type_l hℳ, map_l (ℳ := 𝒱) F K.omega C ∧
      ∀ n y, value_l (ℳ := 𝒱) F (numberCode_l K n).val y ↔
        y = tail_l hℳ hG hS n (zero_l ℳ) := by
  let z : Term SecondOrderSyntax.signature_m [] [.num, .num] .num :=
    .app (σ := SecondOrderSyntax.signature_m) .zero .nil
  let φ : Formula SecondOrderSyntax.signature_m [] [.num, .num] :=
    SecondOrderOrdinalDoubleTailGraph.root_m (.fvar .here) z (.fvar (.there .here))
  obtain ⟨E, hE⟩ := SecondOrderRelations.comprehension_l hℳ φ
    (SecondOrderOrdinalDoubleTailGraph.root_language_m _ _ _ rfl rfl rfl) Env.empty
  have hRead (n m : num_l ℳ) : SecondOrderPairing.relation_l E n m ↔
      SecondOrderOrdinalDoubleTailGraph.root_l n (zero_l ℳ) = m := by
    exact (hE n m).trans (SecondOrderOrdinalDoubleTailGraph.root_formula_l _ _ _ _)
  have hFunction : SecondOrderFunctions.function_l E := fun n =>
    ⟨_, (hRead n _).mpr rfl, fun m hm => ((hRead n m).mp hm).symm⟩
  obtain ⟨F, hF, hValue⟩ := numeric_function_l K hG hS hFunction
    (fun n m => SecondOrderOrdinalDoubleTailGraph.root_l n (zero_l ℳ) = m) hRead C
    (fun n m hm => hm ▸ hC n (zero_l ℳ))
  refine ⟨F, hF, fun n y => ?_⟩
  rw [hValue]
  constructor
  · rintro ⟨i, j, hij, hni, hyj⟩
    have hin : i = n := numberCode_injective_l K (Subtype.ext hni.symm)
    subst i
    change y = mk_l hℳ ⟨G, SecondOrderOrdinalDoubleTailGraph.root_l n (zero_l ℳ),
      SecondOrderOrdinalDoubleTailGraph.wf_l hℳ hG hS _⟩
    exact hij.symm ▸ hyj
  · intro hy
    exact ⟨n, _, rfl, rfl, hy⟩

theorem slice_exists_l (K : source_coding_l hℳ)
    (hG : SecondOrderOrdinalDoubleTailGraph.spec_l S r G)
    (hS : ∀ a, SecondOrderDomain.wf_l S a) (C : SecondOrderQuotient.type_l hℳ)
    (hC : ∀ n m, mem_l hℳ (tail_l hℳ hG hS n m) C) (n : num_l ℳ) :
    ∃ F : SecondOrderQuotient.type_l hℳ, map_l (ℳ := 𝒱) F K.omega C ∧
      ∀ m y, value_l (ℳ := 𝒱) F (numberCode_l K m).val y ↔ y = tail_l hℳ hG hS n m := by
  let φ : Formula SecondOrderSyntax.signature_m [] [.num, .num, .num] :=
    SecondOrderOrdinalDoubleTailGraph.root_m (.fvar (.there (.there .here)))
      (.fvar .here) (.fvar (.there .here))
  obtain ⟨E, hE⟩ := SecondOrderRelations.comprehension_l hℳ φ
    (SecondOrderOrdinalDoubleTailGraph.root_language_m _ _ _ rfl rfl rfl) (Env.empty.pushFree n)
  have hRead (m k : num_l ℳ) : SecondOrderPairing.relation_l E m k ↔
      SecondOrderOrdinalDoubleTailGraph.root_l n m = k := by
    exact (hE m k).trans (SecondOrderOrdinalDoubleTailGraph.root_formula_l _ _ _ _)
  have hFunction : SecondOrderFunctions.function_l E := fun m =>
    ⟨_, (hRead m _).mpr rfl, fun k hk => ((hRead m k).mp hk).symm⟩
  obtain ⟨F, hF, hValue⟩ := numeric_function_l K hG hS hFunction
    (fun m k => SecondOrderOrdinalDoubleTailGraph.root_l n m = k) hRead C
    (fun m k hmk => hmk ▸ hC n m)
  refine ⟨F, hF, fun m y => ?_⟩
  rw [hValue]
  constructor
  · rintro ⟨i, j, hij, hmi, hyj⟩
    have him : i = m := numberCode_injective_l K (Subtype.ext hmi.symm)
    subst i
    change y = mk_l hℳ ⟨G, SecondOrderOrdinalDoubleTailGraph.root_l n m,
      SecondOrderOrdinalDoubleTailGraph.wf_l hℳ hG hS _⟩
    exact hij.symm ▸ hyj
  · intro hy
    exact ⟨m, _, rfl, rfl, hy⟩

private theorem iteration_l (K : source_coding_l hℳ)
    {C H F : SecondOrderQuotient.type_l hℳ} {T : num_l ℳ → SecondOrderQuotient.type_l hℳ}
    (hF : map_l (ℳ := 𝒱) F K.omega C)
    (hRead : ∀ n y, value_l (ℳ := 𝒱) F (numberCode_l K n).val y ↔ y = T n)
    (hStep : ∀ i, value_l (ℳ := 𝒱) H (T i) (T (succ_l i))) :
    PowerlessFunctionIteration.iteration_l (ℳ := 𝒱) K.omega
      (numberCode_l K (zero_l ℳ)).val C H (T (zero_l ℳ)) F := by
  refine ⟨hF, (hRead _ _).mpr rfl, ?_⟩
  intro n m x y hn hnm hx hy
  obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨n, hn⟩
  have hin : (numberCode_l K i).val = n := congrArg Subtype.val hi
  have hm : m = (numberCode_l K (succ_l i)).val :=
    PowerlessBMSQuotientRecursion.successor_unique_l (hM := hℳ) (hin.symm ▸ hnm)
      (PowerlessBMSQuotientSuccessor.successor_l K i)
  have hx' := (hRead i x).mp (hin.symm ▸ hx)
  have hy' := (hRead (succ_l i) y).mp (hm ▸ hy)
  exact hx'.symm ▸ hy'.symm ▸ hStep i

include hBase in
theorem blocks_class_l (K : source_coding_l hℳ)
    (hG : SecondOrderOrdinalDoubleTailGraph.spec_l S r G)
    (hS : ∀ a, SecondOrderDomain.wf_l S a) (hα : Ordinal (base_l hℳ hS r))
    (C : type_l hℳ B) (hOrd : Ordinal C.val)
    (hCofinal : PowerlessRelativeCofinalLimitBounds.cofinal_l C.val)
    (hC : ∀ n m, mem_l hℳ (tail_l hℳ hG hS n m) C.val) :
    ∃ F : type_l hℳ B, map_l (ℳ := 𝒱) F.val K.omega C.val ∧
      ∀ n y, value_l (ℳ := 𝒱) F.val (numberCode_l K n).val y ↔
        y = tail_l hℳ hG hS n (zero_l ℳ) := by
  obtain ⟨H, hH, hHRead⟩ := PowerlessRelativeClassNextLimitGraph.exists_l (hBase := hBase) C hOrd hCofinal
  obtain ⟨F, hF, hRead⟩ := blocks_exists_l K hG hS C.val hC
  have hIter := iteration_l K hF hRead (fun i =>
    (hHRead _ _).mpr ⟨hC _ _, hC _ _, block_next_l hG hS hα i⟩)
  have hHClass := (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) H C C).mpr hH
  exact ⟨⟨F, PowerlessRelativeClassFunctionIteration.member_l (hBase := hBase) K C H
    (hC (zero_l ℳ) (zero_l ℳ)) hHClass hIter⟩, hF, hRead⟩

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)
private abbrev up₄ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₃ t)

/-- 两个内部编号及一份共同母层内有限轨迹；没有未界定的集合量词。 -/
def matrix_m {Γ Δ : SortContext ℒ} (ω e C H F U p y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| membershipLevyBound.boundedExists (up ω) <|
    membershipLevyBound.boundedExists (up₂ C) <|
      let n : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
      let m : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
      let a : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar .here
      .conj (PowerlessPairBounded.ordered_m n m (up₃ p)) <|
        .conj (PowerlessValueBounded.formula_m (up₃ F) n a) <|
          membershipLevyBound.boundedExists (up₃ U) <| .conj
            (PowerlessFunctionTraceBounded.formula_m (up₄ ω) (up₄ e) (up₄ C) (up₄ H)
              (up a) (up m) (.bvar .here))
            (PowerlessValueBounded.formula_m (.bvar .here) (up m) (up₄ y))

theorem matrix_delta_l {Γ Δ : SortContext ℒ} (ω e C H F U p y : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (matrix_m ω e C H F U p y) :=
  .bounded_exists ω (.bounded_exists (up ω) (.bounded_exists (up₂ C)
    (.conj (PowerlessPairBounded.ordered_delta_l _ _ _) (.conj (PowerlessValueBounded.delta_l _ _ _)
      (.bounded_exists (up₃ U) (.conj (PowerlessFunctionTraceBounded.delta_l _ _ _ _ _ _ _)
        (PowerlessValueBounded.delta_l _ _ _)))))))

def matrix_l {𝒩₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e C H F U p y : carrier_l 𝒩₀) : Prop :=
  ∃ n, member_l 𝒩₀ n ω ∧ ∃ m, member_l 𝒩₀ m ω ∧ ∃ a, member_l 𝒩₀ a C ∧
    ordered_l (ℳ := 𝒩₀) n m p ∧ value_l (ℳ := 𝒩₀) F n a ∧ ∃ g, member_l 𝒩₀ g U ∧
      PowerlessFunctionTraceBounded.trace_l (𝒩 := 𝒩₀) ω e C H a m g ∧ value_l (ℳ := 𝒩₀) g m y

theorem matrix_formula_l {𝒩₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩₀ Γ Δ) (ω e C H F U p y : Term ℒ Γ Δ .set) :
    (matrix_m ω e C H F U p y).satisfies η ↔
      matrix_l (𝒩₀ := 𝒩₀) (ω.eval η) (e.eval η) (C.eval η) (H.eval η)
        (F.eval η) (U.eval η) (p.eval η) (y.eval η) := by
  simp only [matrix_m, matrix_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessPairBounded.ordered_formula_l, PowerlessValueBounded.formula_l,
    PowerlessFunctionTraceBounded.formula_l, Arguments.eval,
    up₄, up₃, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

include hBase in
theorem exists_l (K : source_coding_l hℳ)
    (hG : SecondOrderOrdinalDoubleTailGraph.spec_l S r G)
    (hS : ∀ a, SecondOrderDomain.wf_l S a) (hα : Ordinal (base_l hℳ hS r))
    (C : type_l hℳ B) (hOrd : Ordinal C.val)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ C.val)
    (hCofinal : PowerlessRelativeCofinalLimitBounds.cofinal_l C.val)
    (hC : ∀ n m, mem_l hℳ (tail_l hℳ hG hS n m) C.val) :
    ∃ P R : type_l hℳ B,
      (∀ p : SecondOrderQuotient.type_l hℳ, mem_l hℳ p P.val ↔
        ∃ n m, mem_l hℳ n K.omega ∧ mem_l hℳ m K.omega ∧ ordered_l (ℳ := 𝒱) n m p) ∧
      map_l (ℳ := 𝒱) R.val P.val C.val ∧
      ∀ n m (p y : SecondOrderQuotient.type_l hℳ),
        ordered_l (ℳ := 𝒱) (numberCode_l K n).val (numberCode_l K m).val p →
          (value_l (ℳ := 𝒱) R.val p y ↔ y = tail_l hℳ hG hS n m) := by
  let O : type_l hℳ B := ⟨K.omega, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)⟩
  let e : type_l hℳ B := ⟨(numberCode_l K (zero_l ℳ)).val,
    PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase O.property (numberCode_l K (zero_l ℳ)).property⟩
  obtain ⟨F, hF, hFRead⟩ := blocks_class_l (hBase := hBase) K hG hS hα C hOrd hCofinal hC
  obtain ⟨H, hH, hHRead⟩ := PowerlessRelativeClassLimitSuccessorGraph.exists_l C hOrd hLimit.2
  have hHRaw : map_l (ℳ := 𝒱) H.val C.val C.val :=
    (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) H C C).mp hH
  have hSuccessor (x y : SecondOrderQuotient.type_l hℳ) (hx : mem_l hℳ x C.val)
      (hy : mem_l hℳ y C.val) (hxy : PowerlessRelativeHierarchySemantics.successor_l hℳ x y) :
      value_l (ℳ := 𝒱) H.val x y := by
    let x' : type_l hℳ B := ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase C.property hx⟩
    let y' : type_l hℳ B := ⟨y, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase C.property hy⟩
    exact (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) H x' y').mp
      ((hHRead x' y').mpr ⟨hx, hy, hxy⟩)
  let η₀ : Env 𝒩₁ [] [.set] := Env.empty.pushFree C
  obtain ⟨δ, U, hδ, hU, hωU, hCU⟩ :=
    PowerlessRelativeClassLimitParameterBounds.exists_l (hBase := hBase) η₀ O
  have hCU' : mem_l hℳ C.val U := hCU _ .here
  let U' : type_l hℳ B := ⟨U, PowerlessRelativeLevelClosure.class_l hℳ hBase hU⟩
  obtain ⟨P, hP⟩ := PowerlessRelativeClassProduct.exists_l hBase O O
  have hPRead (p : SecondOrderQuotient.type_l hℳ) : mem_l hℳ p P.val ↔
      ∃ n m, mem_l hℳ n K.omega ∧ mem_l hℳ m K.omega ∧ ordered_l (ℳ := 𝒱) n m p := by
    constructor
    · intro hp
      let p' : type_l hℳ B := ⟨p, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase P.property hp⟩
      obtain ⟨n, m, hn, hm, hnm⟩ := (hP p').mp hp
      exact ⟨n.val, m.val, hn, hm,
        (PowerlessRelativeClassFunctionAbsolute.ordered_l n m p').mp hnm⟩
    · rintro ⟨n, m, hn, hm, hnm⟩
      let n' : type_l hℳ B := ⟨n, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase O.property hn⟩
      let m' : type_l hℳ B := ⟨m, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase O.property hm⟩
      let p' : type_l hℳ B := ⟨p, PowerlessRelativeClassPair.ordered_l hℳ hBase n'.property m'.property hnm⟩
      exact (hP p').mpr ⟨n', m', hn, hm,
        (PowerlessRelativeClassFunctionAbsolute.ordered_l n' m' p').mpr hnm⟩
  have hSliceIter (n : num_l ℳ) {J : SecondOrderQuotient.type_l hℳ}
      (hJ : map_l (ℳ := 𝒱) J K.omega C.val)
      (hJRead : ∀ m y, value_l (ℳ := 𝒱) J (numberCode_l K m).val y ↔
        y = tail_l hℳ hG hS n m) :
      PowerlessFunctionIteration.iteration_l (ℳ := 𝒱) K.omega e.val C.val H.val
        (tail_l hℳ hG hS n (zero_l ℳ)) J :=
    iteration_l K hJ hJRead (fun m => hSuccessor _ _ (hC n m) (hC n (succ_l m))
      (successor_l hG hS n m))
  have hWitness (n m : num_l ℳ) (p : SecondOrderQuotient.type_l hℳ)
      (hp : ordered_l (ℳ := 𝒱) (numberCode_l K n).val (numberCode_l K m).val p) :
      matrix_l (𝒩₀ := 𝒱) K.omega e.val C.val H.val F.val U p (tail_l hℳ hG hS n m) := by
    obtain ⟨J, hJ, hJRead⟩ := slice_exists_l K hG hS C.val hC n
    have hIter := hSliceIter n hJ hJRead
    obtain ⟨g, hgU, hg⟩ := SecondOrderFiniteFunctionRestriction.exists_l K hBase hδ hU hωU hCU' hIter m
    have hTrace := hg
    obtain ⟨t, _, ht, hMap, _, _⟩ := hg
    obtain ⟨y, hy, _⟩ := hMap.2 (numberCode_l K m).val ((ht _).mpr (Or.inr rfl))
    have hmω : mem_l hℳ (numberCode_l K m).val K.omega := (numberCode_l K m).property
    have hJy := SecondOrderFiniteFunctionAgreement.value_l K hHRaw hIter hmω hTrace hy.2
    have hyT := (hJRead m y).mp hJy
    exact ⟨(numberCode_l K n).val, (numberCode_l K n).property,
      (numberCode_l K m).val, (numberCode_l K m).property,
      tail_l hℳ hG hS n (zero_l ℳ), hC n (zero_l ℳ), hp, (hFRead n _).mpr rfl,
      g, hgU, hTrace, hyT ▸ hy.2⟩
  have hDecode (n m : num_l ℳ) (p y : SecondOrderQuotient.type_l hℳ)
      (hp : ordered_l (ℳ := 𝒱) (numberCode_l K n).val (numberCode_l K m).val p)
      (hy : matrix_l (𝒩₀ := 𝒱) K.omega e.val C.val H.val F.val U p y) :
      y = tail_l hℳ hG hS n m := by
    obtain ⟨i, _, j, _, a, _, hij, hFa, g, _, hg, hgy⟩ := hy
    obtain ⟨hi, hj⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hij hp).mp rfl
    subst i
    subst j
    have ha := (hFRead n a).mp hFa
    subst a
    obtain ⟨J, hJ, hJRead⟩ := slice_exists_l K hG hS C.val hC n
    have hmω : mem_l hℳ (numberCode_l K m).val K.omega := (numberCode_l K m).property
    have hJy := SecondOrderFiniteFunctionAgreement.value_l K hHRaw (hSliceIter n hJ hJRead) hmω hg hgy
    exact (hJRead m y).mp hJy
  let η : Env 𝒩₁ [] [.set, .set, .set, .set, .set, .set] :=
    ((((((Env.empty.pushFree O).pushFree e).pushFree C).pushFree H).pushFree F).pushFree U')
  let u : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let f : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let h : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  let c : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there .here)))))
  let z : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there (.there .here))))))
  let w : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] :=
    matrix_m w z c h f u (.fvar .here) (.fvar (.there .here))
  have hφ (p y : SecondOrderQuotient.type_l hℳ) : φ.satisfies
      (((PowerlessRelativeClassRelativization.env_l η).pushFree y).pushFree p) ↔
      matrix_l (𝒩₀ := 𝒱) K.omega e.val C.val H.val F.val U p y :=
    matrix_formula_l _ _ _ _ _ _ _ _ _
  have hTotal (p : SecondOrderQuotient.type_l hℳ) (hp : mem_l hℳ p P.val) :
      ∃! y : SecondOrderQuotient.type_l hℳ, mem_l hℳ y C.val ∧ φ.satisfies
        (((PowerlessRelativeClassRelativization.env_l η).pushFree y).pushFree p) := by
    obtain ⟨i, j, hi, hj, hpPair⟩ := (hPRead p).mp hp
    obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨i, hi⟩
    obtain ⟨m, hm⟩ := numberCode_surjective_l K ⟨j, hj⟩
    have hn' : (numberCode_l K n).val = i := congrArg Subtype.val hn
    have hm' : (numberCode_l K m).val = j := congrArg Subtype.val hm
    have hp' := hn'.symm ▸ hm'.symm ▸ hpPair
    refine ⟨tail_l hℳ hG hS n m, ⟨hC n m, (hφ p _).mpr (hWitness n m p hp')⟩, ?_⟩
    rintro y ⟨_, hy⟩
    exact hDecode n m p y hp' ((hφ p y).mp hy)
  obtain ⟨R, hR, hRead⟩ := PowerlessRelativeClassRawFunction.exists_l (hBase := hBase)
    (φ := φ) (matrix_delta_l _ _ _ _ _ _ _ _) η P C hTotal
  refine ⟨P, R, hPRead, hR, ?_⟩
  intro n m p y hp
  constructor
  · intro hy
    exact hDecode n m p y hp ((hφ p y).mp ((hRead p y).mp hy).2.2)
  · intro hy
    subst y
    exact (hRead p _).mpr ⟨(hPRead p).mpr ⟨(numberCode_l K n).val,
      (numberCode_l K m).val, (numberCode_l K n).property, (numberCode_l K m).property, hp⟩,
      hC n m, (hφ p _).mpr (hWitness n m p hp)⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassDoubleTailFunction
