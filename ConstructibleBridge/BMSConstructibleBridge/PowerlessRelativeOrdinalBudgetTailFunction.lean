import BMSConstructibleBridge.PowerlessRelativeOrdinalBudgetBlocks
import BMSConstructibleBridge.PowerlessRelativeClassIndexedIteration

/-! # 原规范序数预算的实际二维类内函数

从同一原预算图构造全部尾值的 raw 值域和逐行 ω 历史，块首图的 Class
资格由 Blocks 给出；统一有限轨迹检查式把完整指标域 A × ω 的值图放入
Class。共同极限序数只界定真实尾值，不声称它可数或严格低于 Ω。
背景仍为原 Z₂，没有新增行历史、Class 图或 Collection 调用端假设。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeOrdinalBudgetTailFunction

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l mk_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open SecondOrderModel (num_l set_l zero_l succ_l)
open SecondOrderOrdinalBudgetOrder (tail_l base_l)
open SecondOrderOrdinalDoubleTailGraph (root_l root_m root_formula_l)
open SecondOrderOrdinalBudgetFunction (index_l index_covers_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

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
  (hG : SecondOrderOrdinalBudgetGraph.spec_l S r R G) (hS : ∀ n, SecondOrderDomain.wf_l S n)

private abbrev hR := SecondOrderRootOrdinalRelation.wf_l hℳ A hQ hN hRel

/-- 原二阶理解选择全部规范尾根，拼接给出精确 raw 值域。 -/
theorem range_l : ∃ Y : SecondOrderQuotient.type_l hℳ, ∀ y, mem_l hℳ y Y ↔
    ∃ n m, SecondOrderModel.mem_l n N ∧
      y = tail_l hℳ hG hS (hR hℳ A hQ hN hRel) n m := by
  let φ : Formula SecondOrderSyntax.signature_m [] [.num, .set] := .existsE .num <| .existsE .num <|
    .conj (.rel .mem (.cons (.bvar (.there .here)) (.cons (.fvar (.there .here)) .nil)))
      (root_m (.bvar (.there .here)) (.bvar .here) (.fvar .here))
  obtain ⟨P, hP⟩ := SecondOrderModel.comprehension_l hℳ φ
    (SecondOrderArithmetic.pure_language_m _ rfl) (Env.empty.pushFree N)
  have hPRead (k : num_l ℳ) : SecondOrderModel.mem_l k P ↔
      ∃ n m, SecondOrderModel.mem_l n N ∧ root_l n m = k := by
    refine (hP k).trans ?_
    simp only [φ, Formula.satisfies, root_formula_l, Term.eval]
    rfl
  have hGWf := SecondOrderOrdinalBudgetGraph.wf_l hℳ hG hS (hR hℳ A hQ hN hRel)
  obtain ⟨Y, hY⟩ := SecondOrderGraftSemantics.exists_l hℳ G P (fun k _ => hGWf k)
  refine ⟨mk_l hℳ Y, fun y => ?_⟩
  obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ y
  constructor
  · intro hy
    obtain ⟨k, hk, hXk⟩ := (hY X).mp hy
    obtain ⟨n, m, hn, rfl⟩ := (hPRead k).mp hk
    exact ⟨n, m, hn, (SecondOrderQuotient.eq_iff_l hℳ _ _).mpr hXk⟩
  · rintro ⟨n, m, hn, he⟩
    exact (hY X).mpr ⟨root_l n m, (hPRead _).mpr ⟨n, m, hn, rfl⟩,
      (SecondOrderQuotient.eq_iff_l hℳ _ _).mp he⟩

/-- 每一行由原数函数理解给出，不要求行函数先属于 Class。 -/
theorem slice_l (K : source_coding_l hℳ) (C : SecondOrderQuotient.type_l hℳ)
    (n : num_l ℳ) (hC : ∀ m, mem_l hℳ (tail_l hℳ hG hS (hR hℳ A hQ hN hRel) n m) C) :
    ∃ J : SecondOrderQuotient.type_l hℳ, map_l (ℳ := 𝒱) J K.omega C ∧
      ∀ m y, value_l (ℳ := 𝒱) J (numberCode_l K m).val y ↔
        y = tail_l hℳ hG hS (hR hℳ A hQ hN hRel) n m := by
  let φ : Formula SecondOrderSyntax.signature_m [] [.num, .num, .num] :=
    root_m (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there .here))
  obtain ⟨E, hE⟩ := SecondOrderRelations.comprehension_l hℳ φ
    (SecondOrderOrdinalDoubleTailGraph.root_language_m _ _ _ rfl rfl rfl) (Env.empty.pushFree n)
  have hRead (m k : num_l ℳ) : SecondOrderPairing.relation_l E m k ↔ root_l n m = k :=
    (hE m k).trans (root_formula_l _ _ _ _)
  have hFunction : SecondOrderFunctions.function_l E := fun m =>
    ⟨_, (hRead m _).mpr rfl, fun k hk => ((hRead m k).mp hk).symm⟩
  obtain ⟨J, hJ, hValue⟩ := SecondOrderRootedNumericFunction.exists_l K G
    (SecondOrderOrdinalBudgetGraph.wf_l hℳ hG hS (hR hℳ A hQ hN hRel)) hFunction C
    (fun m k hmk => ((hRead m k).mp hmk) ▸ hC m)
  refine ⟨J, hJ, fun m y => ?_⟩
  rw [hValue]
  constructor
  · rintro ⟨i, k, hik, hmi, hyk⟩
    have him : i = m := numberCode_injective_l K (Subtype.ext hmi.symm)
    subst i
    obtain rfl := (hRead m k).mp hik
    exact hyk
  · intro hy
    exact ⟨m, root_l n m, (hRead m _).mpr rfl, rfl, hy⟩

private theorem iteration_l (K : source_coding_l hℳ)
    {C H J : SecondOrderQuotient.type_l hℳ} {T : num_l ℳ → SecondOrderQuotient.type_l hℳ}
    (hJ : map_l (ℳ := 𝒱) J K.omega C)
    (hRead : ∀ n y, value_l (ℳ := 𝒱) J (numberCode_l K n).val y ↔ y = T n)
    (hStep : ∀ i, value_l (ℳ := 𝒱) H (T i) (T (succ_l i))) :
    PowerlessFunctionIteration.iteration_l (ℳ := 𝒱) K.omega
      (numberCode_l K (zero_l ℳ)).val C H (T (zero_l ℳ)) J := by
  refine ⟨hJ, (hRead _ _).mpr rfl, ?_⟩
  intro n m x y hn hnm hx hy
  obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨n, hn⟩
  have hin : (numberCode_l K i).val = n := congrArg Subtype.val hi
  have hm : m = (numberCode_l K (succ_l i)).val :=
    PowerlessBMSQuotientRecursion.successor_unique_l (hM := hℳ) (hin.symm ▸ hnm)
      (PowerlessBMSQuotientSuccessor.successor_l K i)
  have hx' := (hRead i x).mp (hin.symm ▸ hx)
  have hy' := (hRead (succ_l i) y).mp (hm ▸ hy)
  exact hx'.symm ▸ hy'.symm ▸ hStep i

variable {B : SecondOrderQuotient.type_l hℳ}

/-- 同一规范预算的完整二维值图真实属于 Class；严格截断另证。 -/
theorem exists_l (K : source_coding_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hA : Ordinal (mk_l hℳ A)) (hξ : Ordinal (base_l hℳ hS r))
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ (base_l hℳ hS r)) :
    ∃ C P Z : type_l hℳ B, Ordinal C.val ∧
      (∀ p, mem_l hℳ p P.val ↔ ∃ a m, mem_l hℳ a (mk_l hℳ A) ∧ mem_l hℳ m K.omega ∧
        ordered_l (ℳ := 𝒱) a m p) ∧ map_l (ℳ := 𝒱) Z.val P.val C.val ∧
      ∀ n m (hn : SecondOrderModel.mem_l n N) p y,
        ordered_l (ℳ := 𝒱) (index_l hℳ A hN n hn) (numberCode_l K m).val p →
          (value_l (ℳ := 𝒱) Z.val p y ↔ y = tail_l hℳ hG hS (hR hℳ A hQ hN hRel) n m) := by
  let T (n m : num_l ℳ) := tail_l hℳ hG hS (hR hℳ A hQ hN hRel) n m
  obtain ⟨Y, hY⟩ := range_l hℳ A hQ hN hRel hG hS
  have hOrdY y (hy : mem_l hℳ y Y) : Ordinal y := by
    obtain ⟨n, m, hn, rfl⟩ := (hY y).mp hy
    exact PowerlessRelativeOrdinalBudgetReading.ordinal_l hℳ A hQ hN hRel hG hS hA hξ n m hn
  obtain ⟨δ, hδ, hBound⟩ := SecondOrderCodedOrdinalFamilyBound.set_bound_l hOrdY
  obtain ⟨γ, hγ, hδγ, hNoMax⟩ := SecondOrderOrdinalLimitDerives.exists_l hℳ δ hδ
  have hT n m (hn : SecondOrderModel.mem_l n N) : mem_l hℳ (T n m) γ :=
    hγ.transitive δ hδγ (T n m) (hBound (T n m) ((hY _).mpr ⟨n, m, hn, rfl⟩))
  let C : type_l hℳ B := ⟨γ, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase hγ⟩
  let A' : type_l hℳ B := ⟨mk_l hℳ A, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase hA⟩
  obtain ⟨Y₀, F₀, hF₀, hFClass, hFRead⟩ :=
    PowerlessRelativeOrdinalBudgetBlocks.exists_l hℳ A hQ hN hRel hG hS K hBase hA hξ hLimit
  let F : type_l hℳ B := ⟨F₀, hFClass⟩
  have hF : map_l (ℳ := 𝒱) F.val A'.val C.val := by
    constructor
    · intro p hp
      obtain ⟨x, y, hx, _, hxy⟩ := hF₀.1 p hp
      obtain ⟨n, hn, _, rfl⟩ := (hFRead x y).mp ⟨p, hp, hxy⟩
      exact ⟨x, T n (zero_l ℳ), hx, hT n (zero_l ℳ) hn, hxy⟩
    · intro x hx
      obtain ⟨y, ⟨_, hxy⟩, _⟩ := hF₀.2 x hx
      obtain ⟨n, hn, _, hy⟩ := (hFRead x y).mp hxy
      exact ⟨y, ⟨hy.symm ▸ hT n (zero_l ℳ) hn, hxy⟩, fun z hz =>
        SecondOrderFunctionProperties.value_unique_l hℳ hF₀ hz.2 hxy⟩
  obtain ⟨H, hH, hHRead⟩ := PowerlessRelativeClassLimitSuccessorGraph.exists_l
    (hBase := hBase) C hγ hNoMax
  have hHRaw : map_l (ℳ := 𝒱) H.val C.val C.val :=
    (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) H C C).mp hH
  have hStep n m (hn : SecondOrderModel.mem_l n N) :
      value_l (ℳ := 𝒱) H.val (T n m) (T n (succ_l m)) := by
    let x : type_l hℳ B := ⟨T n m, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase C.property (hT n m hn)⟩
    let y : type_l hℳ B := ⟨T n (succ_l m), PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase C.property (hT n (succ_l m) hn)⟩
    exact (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) H x y).mp
      ((hHRead x y).mpr ⟨hT n m hn, hT n (succ_l m) hn,
        SecondOrderOrdinalBudgetFinite.successor_l hℳ hG hS (hR hℳ A hQ hN hRel) n m⟩)
  have hRows a b (_ha : mem_l hℳ a A'.val) (hab : value_l (ℳ := 𝒱) F.val a b) :
      ∃ J, PowerlessFunctionIteration.iteration_l (ℳ := 𝒱) K.omega
        (numberCode_l K (zero_l ℳ)).val C.val H.val b J := by
    obtain ⟨n, hn, _, rfl⟩ := (hFRead a b).mp hab
    obtain ⟨J, hJ, hJRead⟩ := slice_l hℳ A hQ hN hRel hG hS K C.val n (fun m => hT n m hn)
    exact ⟨J, iteration_l hℳ K hJ hJRead (fun m => hStep n m hn)⟩
  obtain ⟨U, P, Z, hP, hZ, hZRead⟩ := PowerlessRelativeClassIndexedIteration.exists_l
    (hBase := hBase) K A' C H F hHRaw hF hRows
  have hDecode n m (hn : SecondOrderModel.mem_l n N) p y
      (hp : ordered_l (ℳ := 𝒱) (index_l hℳ A hN n hn) (numberCode_l K m).val p)
      (hy : value_l (ℳ := 𝒱) Z.val p y) : y = T n m := by
    obtain ⟨_, _, a, _, k, _, b, _, hak, hab, g, _, hg, hgy⟩ := (hZRead p y).mp hy
    obtain ⟨hea, hek⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hak hp).mp rfl
    subst a
    subst k
    have hab₀ : value_l (ℳ := 𝒱) F.val (index_l hℳ A hN n hn) (T n (zero_l ℳ)) :=
      (hFRead _ _).mpr ⟨n, hn, rfl, rfl⟩
    have heb := SecondOrderFunctionProperties.value_unique_l hℳ hF hab hab₀
    subst b
    obtain ⟨J, hJ, hJRead⟩ := slice_l hℳ A hQ hN hRel hG hS K C.val n (fun m => hT n m hn)
    have hIter := iteration_l hℳ K hJ hJRead (fun k => hStep n k hn)
    exact (hJRead m y).mp (SecondOrderFiniteFunctionAgreement.value_l K hHRaw hIter
      (numberCode_l K m).property hg hgy)
  refine ⟨C, P, Z, hγ, hP, hZ, fun n m hn p y hp => ⟨hDecode n m hn p y hp, ?_⟩⟩
  intro hy
  have hpP : mem_l hℳ p P.val := (hP p).mpr ⟨index_l hℳ A hN n hn,
    (numberCode_l K m).val, (index_covers_l hℳ A hQ hN _).mpr ⟨n, hn, rfl⟩,
    (numberCode_l K m).property, hp⟩
  obtain ⟨z, ⟨_, hpz⟩, _⟩ := hZ.2 p hpP
  have hz := hDecode n m hn p z hp hpz
  exact (hz.trans hy.symm) ▸ hpz

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeOrdinalBudgetTailFunction
