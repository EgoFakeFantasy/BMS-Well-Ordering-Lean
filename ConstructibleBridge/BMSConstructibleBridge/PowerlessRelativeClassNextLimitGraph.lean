import BMSConstructibleBridge.PowerlessRelativeClassRawFunction
import BMSConstructibleBridge.PowerlessRelativeCofinalLimitBounds
import BMSConstructibleBridge.PowerlessWeakSetInduction
import BMSConstructibleBridge.SecondOrderOrdinalComparison

/-! # 共尾极限序数上的下一非零极限图

对象语言为纯隶属 ℒ，背景为原 Z₂。固定实际 Class 序数 C；其内部
非零极限共尾守卫保证每个 x∈C 有下一非零极限。检查式只有有界量词，
因此图真正属于 Class，且接口读取全部原商坐标，不要求 C 类内可数。
末尾闭句经原图翻译回传普通 Derives；没有 Collection 或外部良基假设。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassNextLimitGraph

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open SecondOrderObjectSyntax (member_m map_m value_m)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

/-- 序数资格由固定母界给出；这里只检查非空和无最大成员。 -/
def limit_m {Γ Δ : SortContext ℒ} (a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (membershipLevyBound.boundedExists a .truth)
    (membershipLevyBound.boundedForall a <| membershipLevyBound.boundedExists (up a) <|
      member_m (.bvar (.there .here)) (.bvar .here))

theorem limit_delta_l {Γ Δ : SortContext ℒ} (a : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (limit_m a) :=
  .conj (.bounded_exists a .truth)
    (.bounded_forall a (.bounded_exists (up a) (.rel _ _)))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Ordinal" => SetTheory.Structure.IsOrdinal
  (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱)

theorem limit_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (a : Term ℒ Γ Δ .set) : (limit_m a).satisfies η ↔
      PowerlessRelativeHierarchySemantics.limit_l hℳ (a.eval η) := by
  simp only [limit_m, Formula.LevyBound.boundedExists, Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies, member_m,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  exact and_congr ⟨fun ⟨x, hx, _⟩ => ⟨x, hx⟩, fun ⟨x, hx⟩ => ⟨x, hx, trivial⟩⟩ Iff.rfl

def next_l (x y : SecondOrderQuotient.type_l hℳ) : Prop :=
  mem_l hℳ x y ∧ PowerlessRelativeHierarchySemantics.limit_l hℳ y ∧
    ∀ z, mem_l hℳ z y → mem_l hℳ x z →
      ¬PowerlessRelativeHierarchySemantics.limit_l hℳ z

def formula_m {Γ Δ : SortContext ℒ} (x y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (member_m x y) <| .conj (limit_m y) <|
    membershipLevyBound.boundedForall y <|
      .imp (member_m (up x) (.bvar .here)) (.neg (limit_m (.bvar .here)))

theorem delta_l {Γ Δ : SortContext ℒ} (x y : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m x y) :=
  .conj (.rel _ _) (.conj (limit_delta_l y)
    (.bounded_forall y (.imp (.rel _ _) (.neg (limit_delta_l _)))))

theorem formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (x y : Term ℒ Γ Δ .set) : (formula_m x y).satisfies η ↔ next_l (x.eval η) (y.eval η) := by
  simp only [formula_m, next_l, Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies, limit_formula_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem unique_l {x y z : SecondOrderQuotient.type_l hℳ}
    (hy : Ordinal y) (hz : Ordinal z) (hxy : next_l x y) (hxz : next_l x z) : y = z := by
  rcases SecondOrderOrdinalComparison.compare_l hℳ hy hz with h | h | h
  · exact h
  · exact (hxz.2.2 y h hxy.1 hxy.2.1).elim
  · exact (hxy.2.2 z h hxz.1 hxz.2.1).elim

theorem next_exists_l {C x : SecondOrderQuotient.type_l hℳ}
    (hC : Ordinal C) (hCofinal : PowerlessRelativeCofinalLimitBounds.cofinal_l C)
    (hx : mem_l hℳ x C) : ∃! y, mem_l hℳ y C ∧ next_l x y := by
  let φ : Formula ℒ [] [.set, .set, .set] := .conj
    (member_m (.fvar .here) (.fvar (.there (.there .here)))) <| .conj
      (member_m (.fvar (.there .here)) (.fvar .here)) (limit_m (.fvar .here))
  let η : Env 𝒱 [] [.set, .set] := (Env.empty.pushFree C).pushFree x
  have hRead y : φ.satisfies (η.pushFree y) ↔ mem_l hℳ y C ∧
      mem_l hℳ x y ∧ PowerlessRelativeHierarchySemantics.limit_l hℳ y := by
    simp only [φ, Formula.satisfies, limit_formula_l, member_m, Arguments.eval, Term.eval]
    rfl
  obtain ⟨a, haC, hxa, haLimit⟩ := hCofinal x hx
  obtain ⟨y, hy, hMin⟩ := PowerlessWeakSetInduction.minimum_l
    (SecondOrderWeakSetTheory.models_l hℳ) φ η ⟨a, (hRead a).mpr ⟨haC, hxa, haLimit⟩⟩
  obtain ⟨hyC, hxy, hyLimit⟩ := (hRead y).mp hy
  have hNext : next_l x y := ⟨hxy, hyLimit, fun z hzy hxz hz =>
    hMin z hzy ((hRead z).mpr ⟨hC.transitive y hyC z hzy, hxz, hz⟩)⟩
  refine ⟨y, ⟨hyC, hNext⟩, ?_⟩
  rintro z ⟨hzC, hxz⟩
  exact unique_l (SetTheory.Structure.IsOrdinal.mem hC hzC)
    (SetTheory.Structure.IsOrdinal.mem hC hyC) hxz hNext

include hBase in
theorem exists_l (C : type_l hℳ B) (hC : Ordinal C.val)
    (hCofinal : PowerlessRelativeCofinalLimitBounds.cofinal_l C.val) :
    ∃ H : type_l hℳ B, map_l (ℳ := 𝒱) H.val C.val C.val ∧
      ∀ x y : SecondOrderQuotient.type_l hℳ, value_l (ℳ := 𝒱) H.val x y ↔
        mem_l hℳ x C.val ∧ mem_l hℳ y C.val ∧ next_l x y := by
  let φ : Formula ℒ [] [.set, .set] := formula_m (.fvar .here) (.fvar (.there .here))
  obtain ⟨H, hH, hRead⟩ := PowerlessRelativeClassRawFunction.exists_l
    (hBase := hBase) (φ := φ) (delta_l _ _) Env.empty C C (fun x hx => by
      obtain ⟨y, ⟨hyC, hxy⟩, hUnique⟩ := next_exists_l hC hCofinal hx
      refine ⟨y, ⟨hyC, (formula_l _ _ _).mpr hxy⟩, ?_⟩
      rintro z ⟨hzC, hz⟩
      exact hUnique z ⟨hzC, (formula_l _ _ _).mp hz⟩)
  exact ⟨H, hH, fun x y => (hRead x y).trans
    (and_congr Iff.rfl (and_congr Iff.rfl (formula_l _ _ _)))⟩

def specification_m {Γ Δ : SortContext ℒ} (C H : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (map_m H C C) <| .forallE .set <| .forallE .set <|
    .iff (value_m (up (up H)) (.bvar (.there .here)) (.bvar .here)) <|
      .conj (member_m (.bvar (.there .here)) (up (up C))) <|
        .conj (member_m (.bvar .here) (up (up C)))
          (formula_m (.bvar (.there .here)) (.bvar .here))

theorem specification_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (C H : Term ℒ Γ Δ .set) : (specification_m C H).satisfies η ↔
      map_l (ℳ := 𝒱) (H.eval η) (C.eval η) (C.eval η) ∧
        ∀ x y, value_l (ℳ := 𝒱) (H.eval η) x y ↔
          mem_l hℳ x (C.eval η) ∧ mem_l hℳ y (C.eval η) ∧ next_l x y := by
  simp only [specification_m, Formula.satisfies, map_formula_l, value_formula_l,
    formula_l, member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m : Formula ℒ [] [.set, .set] :=
  let C : Term ℒ [] [.set, .set] .set := .fvar .here
  let B := .fvar (.there .here)
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B C) <|
      .imp (PowerlessRelativeHierarchySyntax.ordinal_m C) <|
        .imp (PowerlessRelativeCofinalLimitBounds.cofinal_m C) <|
          .existsE .set <| .conj (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here))
            (specification_m (up C) (.bvar .here))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) : sentence_m.TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeHierarchySemantics.ordinal_formula_l,
    PowerlessRelativeCofinalLimitBounds.cofinal_formula_l,
    specification_formula_l, up, Term.eval_weakenBound, Term.eval]
  intro η hBase hC hOrd hCofinal
  obtain ⟨H, hH, hRead⟩ := exists_l (hBase := hBase) ⟨η.freeVal .here, hC⟩ hOrd hCofinal
  exact ⟨H.val, H.property, hH, hRead⟩

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassNextLimitGraph
