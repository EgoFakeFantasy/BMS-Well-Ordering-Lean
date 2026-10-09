import BMSConstructibleBridge.PowerlessRelativeCofinalDefCoding
import BMSConstructibleBridge.PowerlessRelativeClassFunctionGraph
import BMSConstructibleBridge.PowerlessRelativeLimitDeltaSeparation

/-! # 实际极限层内全部 Sat 行的统一调用图

对象语言为纯隶属 ℒ，背景为原 SecondOrderArithmetic.theory_m。输入编码
为 (母集,内部槽行码)，有效输入读取同一 Class Sat 函数，非法输入取指定
缺省对象。查询先用 W 作统一界，再以真实 Seq 和指标集缩回局部参数，
所以每个输出仍属于 W；没有把全局 Sat 图 G 误放入 W。

所得同一图属于 Class 并实际映射 W→W，可供有限程序的调用闭包消费。
局部查询资格由既有共尾编码包直接提供；对象模式明确保留该资格，不把
它当作最终源公理。低层覆盖、层内枚举、完整 Collection 仍需另证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitSatisfactionRowOperator

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)

def index_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω S I : carrier_l 𝒩) : Prop :=
  ∀ p, member_l 𝒩 p I ↔ ∃ c f, member_l 𝒩 c ω ∧ member_l 𝒩 f S ∧ ordered_l c f p

def index_m {Γ Δ : SortContext ℒ} (ω S I : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .iff (SecondOrderObjectSyntax.member_m (.bvar .here) (up I)) <|
    membershipLevyBound.boundedExists (up ω) <|
      membershipLevyBound.boundedExists (up₂ S) <|
        PowerlessPairBounded.ordered_m (.bvar (.there .here)) (.bvar .here)
          (.bvar (.there (.there .here)))

theorem index_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω S I : Term ℒ Γ Δ .set) :
    (index_m ω S I).satisfies η ↔ index_l (ω.eval η) (S.eval η) (I.eval η) := by
  simp only [index_m, index_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    SecondOrderObjectSyntax.member_m, PowerlessPairBounded.ordered_formula_l,
    Arguments.eval, up₂, up, Term.eval_weakenBound, Term.eval]
  exact forall_congr' fun _ => iff_congr Iff.rfl
    ⟨fun ⟨c, hc, f, hf, h⟩ => ⟨c, f, hc, hf, h⟩,
      fun ⟨c, f, hc, hf, h⟩ => ⟨c, hc, f, hf, h⟩⟩

def local_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω W G : carrier_l 𝒩) : Prop :=
  ∀ A R, member_l 𝒩 A W → member_l 𝒩 R W → value_l G A R → ∃ S I,
    member_l 𝒩 S W ∧ member_l 𝒩 I W ∧
      PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒩) ω A S ∧ index_l ω S I

def local_m {Γ Δ : SortContext ℒ} (ω W G : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall W <| membershipLevyBound.boundedForall (up W) <|
    .imp (PowerlessValueBounded.formula_m (up₂ G) (.bvar (.there .here)) (.bvar .here)) <|
      membershipLevyBound.boundedExists (up₂ W) <|
        membershipLevyBound.boundedExists (up₃ W) <|
          .conj (PowerlessFiniteSequencesSyntax.spec_m (up₂ (up₂ ω))
            (.bvar (.there (.there (.there .here)))) (.bvar (.there .here)))
            (index_m (up₂ (up₂ ω)) (.bvar (.there .here)) (.bvar .here))

theorem local_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω W G : Term ℒ Γ Δ .set) :
    (local_m ω W G).satisfies η ↔ local_l (ω.eval η) (W.eval η) (G.eval η) := by
  simp only [local_m, local_l, Formula.LevyBound.boundedForall,
    Formula.LevyBound.boundedExists, Formula.LevyBound.membership, membershipLevyBound,
    Formula.satisfies, PowerlessValueBounded.formula_l, PowerlessFiniteSequencesSyntax.spec_formula_l,
    index_formula_l, Arguments.eval, up₃, up₂, up, Term.eval_weakenBound, Term.eval]
  constructor
  · intro h A R hA hR hValue
    obtain ⟨S, hS, I, hI, h⟩ := h A hA R hR hValue
    exact ⟨S, I, hS, hI, h⟩
  · intro h A hA R hR hValue
    obtain ⟨S, I, hS, hI, h⟩ := h A R hA hR hValue
    exact ⟨S, hS, I, hI, h⟩

def row_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω W A R t Z : carrier_l 𝒩) : Prop :=
  ∀ x, member_l 𝒩 x Z ↔ member_l 𝒩 x A ∧
    PowerlessRelativeClassSatisfactionAllSlots.query_l (ℳ₀ := 𝒩) ω A W W R t x

def row_m {Γ Δ : SortContext ℒ} (ω W A R t Z : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (membershipLevyBound.boundedForall Z <|
    SecondOrderObjectSyntax.member_m (.bvar .here) (up A)) <|
      membershipLevyBound.boundedForall A <|
        .iff (SecondOrderObjectSyntax.member_m (.bvar .here) (up Z)) <|
          PowerlessRelativeClassSatisfactionAllSlots.query_m
            (up ω) (up A) (up W) (up W) (up R) (up t) (.bvar .here)

theorem row_delta_l {Γ Δ : SortContext ℒ} (ω W A R t Z : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (row_m ω W A R t Z) :=
  .conj (.bounded_forall _ (.rel _ _)) (.bounded_forall _
    (.iff (.rel _ _) (PowerlessRelativeClassSatisfactionAllSlots.query_delta_l _ _ _ _ _ _ _)))

theorem row_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω W A R t Z : Term ℒ Γ Δ .set) :
    (row_m ω W A R t Z).satisfies η ↔
      row_l (ω.eval η) (W.eval η) (A.eval η) (R.eval η) (t.eval η) (Z.eval η) := by
  simp only [row_m, row_l, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, SecondOrderObjectSyntax.member_m,
    PowerlessRelativeClassSatisfactionAllSlots.query_formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  constructor
  · rintro ⟨hSubset, hRead⟩ x
    exact ⟨fun hx => ⟨hSubset x hx, (hRead x (hSubset x hx)).mp hx⟩,
      fun hx => (hRead x hx.1).mpr hx.2⟩
  · intro h
    exact ⟨fun x hx => ((h x).mp hx).1, fun x hx =>
      ⟨fun hZ => ((h x).mp hZ).2, fun hQuery => (h x).mpr ⟨hx, hQuery⟩⟩⟩

def decoded_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (W s : carrier_l 𝒩) : Prop :=
  ∃ A t, member_l 𝒩 A W ∧ member_l 𝒩 t W ∧ ordered_l A t s

def decoded_m {Γ Δ : SortContext ℒ} (W s : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists W <| membershipLevyBound.boundedExists (up W) <|
    PowerlessPairBounded.ordered_m (.bvar (.there .here)) (.bvar .here) (up₂ s)

theorem decoded_delta_l {Γ Δ : SortContext ℒ} (W s : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (decoded_m W s) :=
  .bounded_exists _ (.bounded_exists _ (PowerlessPairBounded.ordered_delta_l _ _ _))

theorem decoded_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (W s : Term ℒ Γ Δ .set) :
    (decoded_m W s).satisfies η ↔ decoded_l (W.eval η) (s.eval η) := by
  simp only [decoded_m, decoded_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessPairBounded.ordered_formula_l, Arguments.eval, up₂, up, Term.eval_weakenBound]
  exact ⟨fun ⟨A, hA, t, ht, h⟩ => ⟨A, t, hA, ht, h⟩,
    fun ⟨A, t, hA, ht, h⟩ => ⟨A, hA, t, ht, h⟩⟩

def relation_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω W G s Z : carrier_l 𝒩) : Prop :=
  ∃ A t R, member_l 𝒩 A W ∧ member_l 𝒩 t W ∧ member_l 𝒩 R W ∧
    ordered_l A t s ∧ value_l G A R ∧ row_l ω W A R t Z

def relation_m {Γ Δ : SortContext ℒ} (ω W G s Z : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists W <| membershipLevyBound.boundedExists (up W) <|
    membershipLevyBound.boundedExists (up₂ W) <|
      .conj (PowerlessPairBounded.ordered_m (.bvar (.there (.there .here)))
        (.bvar (.there .here)) (up₃ s)) <|
        .conj (PowerlessValueBounded.formula_m (up₃ G) (.bvar (.there (.there .here))) (.bvar .here))
          (row_m (up₃ ω) (up₃ W) (.bvar (.there (.there .here)))
            (.bvar .here) (.bvar (.there .here)) (up₃ Z))

theorem relation_delta_l {Γ Δ : SortContext ℒ} (ω W G s Z : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (relation_m ω W G s Z) :=
  .bounded_exists _ (.bounded_exists _ (.bounded_exists _
    (.conj (PowerlessPairBounded.ordered_delta_l _ _ _)
      (.conj (PowerlessValueBounded.delta_l _ _ _) (row_delta_l _ _ _ _ _ _)))))

theorem relation_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω W G s Z : Term ℒ Γ Δ .set) :
    (relation_m ω W G s Z).satisfies η ↔
      relation_l (ω.eval η) (W.eval η) (G.eval η) (s.eval η) (Z.eval η) := by
  simp only [relation_m, relation_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessPairBounded.ordered_formula_l, PowerlessValueBounded.formula_l,
    row_formula_l, Arguments.eval, up₃, up₂, up, Term.eval_weakenBound, Term.eval]
  exact ⟨fun ⟨A, hA, t, ht, R, hR, h⟩ => ⟨A, t, R, hA, ht, hR, h⟩,
    fun ⟨A, t, R, hA, ht, hR, h⟩ => ⟨A, hA, t, ht, R, hR, h⟩⟩

def total_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω W G e s Z : carrier_l 𝒩) : Prop :=
  relation_l ω W G s Z ∨ (¬decoded_l W s ∧ Z = e)

def total_m {Γ Δ : SortContext ℒ} (ω W G e s Z : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (relation_m ω W G s Z) (.conj (.neg (decoded_m W s)) (.equal Z e))

theorem total_delta_l {Γ Δ : SortContext ℒ} (ω W G e s Z : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (total_m ω W G e s Z) :=
  .disj (relation_delta_l _ _ _ _ _) (.conj (.neg (decoded_delta_l _ _)) (.equal _ _))

theorem total_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω W G e s Z : Term ℒ Γ Δ .set) :
    (total_m ω W G e s Z).satisfies η ↔
      total_l (ω.eval η) (W.eval η) (G.eval η) (e.eval η) (s.eval η) (Z.eval η) := by
  simp only [total_m, total_l, Formula.satisfies, relation_formula_l, decoded_formula_l]

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ

/-- 更新前后的真实有限映射使 W 查询恰好等于局部 Seq 查询。 -/
theorem query_bound_l {ω W A S I R t x : Raw}
    (hW : ∀ a, mem_l hℳ a W → ∀ b, mem_l hℳ b a → mem_l hℳ b W)
    (hSW : mem_l hℳ S W) (hIW : mem_l hℳ I W)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) ω A S)
    (hI : index_l (𝒩 := 𝒱) ω S I) :
    PowerlessRelativeClassSatisfactionAllSlots.query_l (ℳ₀ := 𝒱) ω A W W R t x ↔
      PowerlessRelativeClassSatisfactionAllSlots.query_l (ℳ₀ := 𝒱) ω A S I R t x := by
  constructor
  · rintro ⟨e, p, he, _hp, ht, c, f, n, g, hc, _hf, hn, _hg, hp, hf, hg, hen, hUpdate, hValue⟩
    have hfS := (hS f).mpr ⟨n, hn, hf⟩
    have hgS := (hS g).mpr ⟨n, hn, hg⟩
    exact ⟨e, p, he, (hI p).mpr ⟨c, f, hc, hfS, hp⟩, ht,
      c, f, n, g, hc, hfS, hn, hgS, hp, hf, hg, hen, hUpdate, hValue⟩
  · rintro ⟨e, p, he, hpI, ht, c, f, n, g, hc, hfS, hn, hgS, hp, hf, hg, hen, hUpdate, hValue⟩
    exact ⟨e, p, he, hW I hIW p hpI, ht, c, f, n, g, hc,
      hW S hSW f hfS, hn, hW S hSW g hgS, hp, hf, hg, hen, hUpdate, hValue⟩

theorem row_exists_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    {β ω W A R t : Raw} (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B β W)
    (hωW : mem_l hℳ ω W) (hAW : mem_l hℳ A W) (hRW : mem_l hℳ R W)
    (htW : mem_l hℳ t W)
    (hLocal : ∃ S I, mem_l hℳ S W ∧ mem_l hℳ I W ∧
      PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) ω A S ∧ index_l (𝒩 := 𝒱) ω S I) :
    ∃ Z, mem_l hℳ Z W ∧ row_l (𝒩 := 𝒱) ω W A R t Z := by
  obtain ⟨S, I, hSW, hIW, hS, hI⟩ := hLocal
  let η : Env 𝒱 [] [.set, .set, .set, .set, .set, .set] :=
    ((((((Env.empty.pushFree R).pushFree I).pushFree S).pushFree A).pushFree ω).pushFree t)
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set] :=
    PowerlessRelativeClassSatisfactionAllSlots.query_m
      (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar (.there .here)) (.fvar .here)
  have hParams : ∀ s (v : Variable [SetTheory.SetSort.set, .set, .set, .set, .set, .set] s),
      mem_l hℳ (η.freeVal v) W := by
    intro s v
    cases s
    match v with
    | .here => exact htW
    | .there .here => exact hωW
    | .there (.there .here) => exact hAW
    | .there (.there (.there .here)) => exact hSW
    | .there (.there (.there (.there .here))) => exact hIW
    | .there (.there (.there (.there (.there .here)))) => exact hRW
  obtain ⟨Z, hZW, hZ⟩ := PowerlessRelativeLimitDeltaSeparation.exists_l
    hBase hLimit hW (φ := φ) (PowerlessRelativeClassSatisfactionAllSlots.query_delta_l _ _ _ _ _ _ _)
      η hAW hParams
  refine ⟨Z, hZW, fun x => (hZ x).trans (and_congr Iff.rfl ?_)⟩
  exact (PowerlessRelativeClassSatisfactionAllSlots.query_formula_l (η.pushFree x) _ _ _ _ _ _ _).trans
    (query_bound_l (PowerlessRelativeLevelClosure.transitive_l hℳ hBase hW) hSW hIW hS hI).symm

theorem unique_l {ω W G e s Y Z : Raw} (hG : map_l (ℳ := 𝒱) G W W)
    (hY : total_l (𝒩 := 𝒱) ω W G e s Y) (hZ : total_l (𝒩 := 𝒱) ω W G e s Z) : Y = Z := by
  rcases hY with ⟨A, t, R, hA, ht, hR, hs, hAR, hY⟩ | ⟨hNone, rfl⟩
  · rcases hZ with ⟨A', t', R', _hA', _ht', _hR', hs', hAR', hZ⟩ | ⟨hNone, _⟩
    · obtain ⟨rfl, rfl⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hs hs').mp rfl
      have hEq := SecondOrderFunctionProperties.value_unique_l hℳ hG hAR hAR'
      subst R'
      exact SecondOrderQuotient.ext_l hℳ _ _ (fun x => (hY x).trans (hZ x).symm)
    · exact (hNone ⟨A, t, hA, ht, hs⟩).elim
  · rcases hZ with ⟨A, t, R, hA, ht, _hR, hs, _hAR, _hZ⟩ | ⟨_, rfl⟩
    · exact (hNone ⟨A, t, hA, ht, hs⟩).elim
    · rfl

/-- 真正构造一张 Class 调用图；不预供行图、行覆盖或 W 的可数性。 -/
theorem exists_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    {β W : Raw} (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B β W)
    (ω G e : type_l hℳ B) (hωW : mem_l hℳ ω.val W) (heW : mem_l hℳ e.val W)
    (hG : map_l (ℳ := 𝒱) G.val W W) (hLocal : local_l (𝒩 := 𝒱) ω.val W G.val) :
    ∃ F : type_l hℳ B, map_l (ℳ := 𝒱) F.val W W ∧ ∀ s Z : Raw,
      value_l (ℳ := 𝒱) F.val s Z ↔ mem_l hℳ s W ∧ mem_l hℳ Z W ∧
        total_l (𝒩 := 𝒱) ω.val W G.val e.val s Z := by
  classical
  let C : type_l hℳ B := ⟨W, PowerlessRelativeLevelClosure.class_l hℳ hBase hW⟩
  let η : Env (structure_l hℳ B hBase) [] [.set, .set, .set, .set] :=
    ((((Env.empty (M := structure_l hℳ B hBase)).pushFree (sort := SetTheory.SetSort.set) G).pushFree
      (sort := SetTheory.SetSort.set) C).pushFree (sort := SetTheory.SetSort.set) ω).pushFree
        (sort := SetTheory.SetSort.set) e
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set] := total_m
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here)))))) (.fvar (.there (.there .here)))
    (.fvar .here) (.fvar (.there .here))
  have hφ : Formula.IsDelta0 membershipLevyBound φ := total_delta_l _ _ _ _ _ _
  have hRead (s Z : Raw) :
      φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree
        (sort := SetTheory.SetSort.set) Z).pushFree (sort := SetTheory.SetSort.set) s) ↔
        total_l (𝒩 := 𝒱) ω.val W G.val e.val s Z := by
    exact total_formula_l (((PowerlessRelativeClassRelativization.env_l η).pushFree
      (sort := SetTheory.SetSort.set) Z).pushFree (sort := SetTheory.SetSort.set) s)
      _ _ _ _ _ _
  have hTotal (s : type_l hℳ B) (_hs : mem_l hℳ s.val C.val) :
      ∃! Z : type_l hℳ B, mem_l hℳ Z.val C.val ∧ φ.satisfies ((η.pushFree Z).pushFree s) := by
    have hRaw : ∃ Z : Raw, mem_l hℳ Z W ∧ total_l (𝒩 := 𝒱) ω.val W G.val e.val s.val Z := by
      by_cases h : decoded_l (𝒩 := 𝒱) W s.val
      · obtain ⟨A, t, hAW, htW, hAt⟩ := h
        obtain ⟨R, ⟨hRW, hAR⟩, _⟩ := hG.2 A hAW
        obtain ⟨Z, hZW, hZ⟩ := row_exists_l hBase hLimit hW hωW hAW hRW htW
          (hLocal A R hAW hRW hAR)
        exact ⟨Z, hZW, Or.inl ⟨A, t, R, hAW, htW, hRW, hAt, hAR, hZ⟩⟩
      · exact ⟨e.val, heW, Or.inr ⟨h, rfl⟩⟩
    obtain ⟨Z, hZW, hZ⟩ := hRaw
    let Z' : type_l hℳ B := ⟨Z,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase C.property hZW⟩
    have hEnv (Y : type_l hℳ B) :
        PowerlessRelativeClassRelativization.env_l ((η.pushFree Y).pushFree s) =
          ((PowerlessRelativeClassRelativization.env_l η).pushFree
            (sort := SetTheory.SetSort.set) Y.val).pushFree (sort := SetTheory.SetSort.set) s.val := by
      apply Env.ext
      · intro _ v; nomatch v
      · intro k v
        cases k
        cases v with
        | here => rfl
        | there v => cases v <;> rfl
    have hReadClass (Y : type_l hℳ B) : φ.satisfies ((η.pushFree Y).pushFree s) ↔
        total_l (𝒩 := 𝒱) ω.val W G.val e.val s.val Y.val := by
      have h := PowerlessRelativeClassBounded.formula_l hφ ((η.pushFree Y).pushFree s)
      rw [hEnv] at h
      exact h.trans (hRead s.val Y.val)
    exact ⟨Z', ⟨hZW, (hReadClass Z').mpr hZ⟩, fun Y hY =>
      Subtype.ext (unique_l hG ((hReadClass Y).mp hY.2) hZ)⟩
  obtain ⟨F, hF, hValue⟩ := PowerlessRelativeClassFunctionGraph.exists_l hφ η C C hTotal
  exact ⟨F, hF, fun s Z => (hValue s Z).trans
    (and_congr Iff.rfl (and_congr Iff.rfl (hRead s Z)))⟩

/-- 原共尾编码包直接消去局部查询前提，始终保留同一个实际 G。 -/
theorem of_coding_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (K : source_coding_l hℳ) {β W : Raw}
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B β W)
    (ω e t₁ t₂ t₃ Pair N Valid Translation G : type_l hℳ B)
    {L : SecondOrderModel.set_l ℳ}
    (hCode : PowerlessRelativeCofinalDefCoding.spec_l (W := W)
      hBase K ω e t₁ t₂ t₃ Pair N Valid Translation G L) (hωW : mem_l hℳ ω.val W) :
    ∃ F : type_l hℳ B, map_l (ℳ := 𝒱) F.val W W ∧ ∀ s Z : Raw,
      value_l (ℳ := 𝒱) F.val s Z ↔ mem_l hℳ s W ∧ mem_l hℳ Z W ∧
        total_l (𝒩 := 𝒱) ω.val W G.val e.val s Z := by
  apply exists_l hBase hLimit hW ω G e hωW hCode.e_mem hCode.sat_map
  intro A R hA _hR hAR
  obtain ⟨_hRW, S, I, _J, _Q, hSW, hIW, _hJW, _hQW, hS, hI, _hJ, _hQ⟩ :=
    hCode.witnesses A R hA hAR
  exact ⟨S.val, I.val, hSW, hIW, hS, hI⟩

#print axioms query_bound_l
#print axioms row_exists_l
#print axioms unique_l
#print axioms exists_l
#print axioms of_coding_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitSatisfactionRowOperator
