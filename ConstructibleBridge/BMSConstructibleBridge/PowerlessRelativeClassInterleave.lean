import BMSConstructibleBridge.PowerlessRelativeClassFunctionRelation
import BMSConstructibleBridge.PowerlessSuccessorBounded
import BMSConstructibleBridge.PowerlessValueBounded
import BMSConstructibleBridge.SecondOrderFunctionProperties

/-! # 两份类内枚举的有界交错图

奇偶索引的覆盖与唯一性作为明确输入；图由 Δ₀ 关系存在接口构造。
输出仍是实际类内集合图。此条件接口尚需由内部倍数图填满输入。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassInterleave

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

def formula_m : Formula ℒ [] [.set, .set, .set, .set, .set, .set] :=
  let n : Term ℒ [.set] [.set, .set, .set, .set, .set, .set] .set := .fvar .here
  let y : Term ℒ [.set] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let D : Term ℒ [.set] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let G : Term ℒ [.set] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  let H : Term ℒ [.set] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there .here)))))
  let ω : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  .disj
    (membershipLevyBound.boundedExists ω <| .conj
      (PowerlessValueBounded.formula_m D (.bvar .here) n)
      (PowerlessValueBounded.formula_m G (.bvar .here) y))
    (membershipLevyBound.boundedExists ω <| membershipLevyBound.boundedExists (ω.weakenBound SetTheory.SetSort.set) <|
      .conj (PowerlessValueBounded.formula_m (D.weakenBound SetTheory.SetSort.set) (.bvar (.there .here)) (.bvar .here)) <|
        .conj (PowerlessSuccessorBounded.formula_m (.bvar .here) (n.weakenBound SetTheory.SetSort.set))
          (PowerlessValueBounded.formula_m (H.weakenBound SetTheory.SetSort.set) (.bvar (.there .here))
            (y.weakenBound SetTheory.SetSort.set)))

theorem delta_l : Formula.IsDelta0 membershipLevyBound formula_m :=
  .disj (.bounded_exists _ (.conj (PowerlessValueBounded.delta_l _ _ _) (PowerlessValueBounded.delta_l _ _ _)))
    (.bounded_exists _ (.bounded_exists _ (.conj (PowerlessValueBounded.delta_l _ _ _)
      (.conj (PowerlessSuccessorBounded.delta_l _ _) (PowerlessValueBounded.delta_l _ _ _)))))

def branch_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω D G H n y : carrier_l 𝒩) : Prop :=
  (∃ i, member_l 𝒩 i ω ∧ value_l (ℳ := 𝒩) D i n ∧ value_l (ℳ := 𝒩) G i y) ∨
    ∃ i t, member_l 𝒩 i ω ∧ member_l 𝒩 t ω ∧ value_l (ℳ := 𝒩) D i t ∧
      PowerlessNatural.successor_l (ℳ := 𝒩) t n ∧ value_l (ℳ := 𝒩) H i y

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω D G H n y : carrier_l 𝒩) :
    formula_m.satisfies ((((((Env.empty (M := 𝒩)).pushFree H).pushFree G).pushFree D).pushFree ω).pushFree y |>.pushFree n) ↔
      branch_l (𝒩 := 𝒩) ω D G H n y := by
  simp only [formula_m, branch_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessValueBounded.formula_l, PowerlessSuccessorBounded.formula_l,
    Arguments.eval, Term.eval_weakenBound, Term.eval]
  change ((∃ i, member_l 𝒩 i ω ∧ value_l (ℳ := 𝒩) D i n ∧ value_l (ℳ := 𝒩) G i y) ∨
    ∃ i, member_l 𝒩 i ω ∧ ∃ t, member_l 𝒩 t ω ∧ value_l (ℳ := 𝒩) D i t ∧
      PowerlessNatural.successor_l (ℳ := 𝒩) t n ∧ value_l (ℳ := 𝒩) H i y) ↔ _
  apply or_congr Iff.rfl
  exact ⟨fun ⟨i, hi, t, ht, hit, htn, hiy⟩ => ⟨i, t, hi, ht, hit, htn, hiy⟩,
    fun ⟨i, t, hi, ht, hit, htn, hiy⟩ => ⟨i, hi, t, ht, hit, htn, hiy⟩⟩

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem exists_l {ω D G H U V W : type_l hℳ B}
    (hG : map_l (ℳ := structure_l hℳ B hBase) G ω U)
    (hH : map_l (ℳ := structure_l hℳ B hBase) H ω V)
    (hW : ∀ y : type_l hℳ B, mem_l hℳ y.val W.val ↔ mem_l hℳ y.val U.val ∨ mem_l hℳ y.val V.val)
    (hEven : ∀ i j n : type_l hℳ B, mem_l hℳ i.val ω.val → mem_l hℳ j.val ω.val →
      value_l (ℳ := structure_l hℳ B hBase) D i n → value_l (ℳ := structure_l hℳ B hBase) D j n → i = j)
    (hOdd : ∀ i j t v n : type_l hℳ B, mem_l hℳ i.val ω.val → mem_l hℳ j.val ω.val →
      value_l (ℳ := structure_l hℳ B hBase) D i t → value_l (ℳ := structure_l hℳ B hBase) D j v →
      PowerlessNatural.successor_l (ℳ := structure_l hℳ B hBase) t n →
      PowerlessNatural.successor_l (ℳ := structure_l hℳ B hBase) v n → i = j)
    (hDisjoint : ∀ i j t n : type_l hℳ B, mem_l hℳ i.val ω.val → mem_l hℳ j.val ω.val →
      value_l (ℳ := structure_l hℳ B hBase) D i n → value_l (ℳ := structure_l hℳ B hBase) D j t →
      PowerlessNatural.successor_l (ℳ := structure_l hℳ B hBase) t n → False)
    (hCover : ∀ n : type_l hℳ B, mem_l hℳ n.val ω.val →
      (∃ i : type_l hℳ B, mem_l hℳ i.val ω.val ∧ value_l (ℳ := structure_l hℳ B hBase) D i n) ∨
        ∃ i t : type_l hℳ B, mem_l hℳ i.val ω.val ∧ mem_l hℳ t.val ω.val ∧
          value_l (ℳ := structure_l hℳ B hBase) D i t ∧ PowerlessNatural.successor_l (ℳ := structure_l hℳ B hBase) t n) :
    ∃ F : type_l hℳ B, map_l (ℳ := structure_l hℳ B hBase) F ω W ∧
      ∀ n y : type_l hℳ B, value_l (ℳ := structure_l hℳ B hBase) F n y ↔
        mem_l hℳ n.val ω.val ∧ branch_l (𝒩 := structure_l hℳ B hBase) ω D G H n y := by
  let η : Env (structure_l hℳ B hBase) [] [.set, .set, .set, .set] :=
    (((Env.empty.pushFree H).pushFree G).pushFree D).pushFree ω
  have hRead (n y : type_l hℳ B) := formula_l (𝒩 := structure_l hℳ B hBase) ω D G H n y
  have hG' := (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) G ω U).mp hG
  have hH' := (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) H ω V).mp hH
  have hUnique (n y z : type_l hℳ B)
      (hy : branch_l (𝒩 := structure_l hℳ B hBase) ω D G H n y)
      (hz : branch_l (𝒩 := structure_l hℳ B hBase) ω D G H n z) : y = z := by
    rcases hy with ⟨i, hi, hin, hiy⟩ | ⟨i, t, hi, _, hit, htn, hiy⟩
    · rcases hz with ⟨j, hj, hjn, hjz⟩ | ⟨j, v, hj, _, hjv, hvn, hjz⟩
      · obtain rfl := hEven i j n hi hj hin hjn
        exact Subtype.ext (SecondOrderFunctionProperties.value_unique_l hℳ hG'
          ((PowerlessRelativeClassFunctionAbsolute.value_l G i y).mp hiy)
          ((PowerlessRelativeClassFunctionAbsolute.value_l G i z).mp hjz))
      · exact (hDisjoint i j v n hi hj hin hjv hvn).elim
    · rcases hz with ⟨j, hj, hjn, hjz⟩ | ⟨j, v, hj, _, hjv, hvn, hjz⟩
      · exact (hDisjoint j i t n hj hi hjn hit htn).elim
      · obtain rfl := hOdd i j t v n hi hj hit hjv htn hvn
        exact Subtype.ext (SecondOrderFunctionProperties.value_unique_l hℳ hH'
          ((PowerlessRelativeClassFunctionAbsolute.value_l H i y).mp hiy)
          ((PowerlessRelativeClassFunctionAbsolute.value_l H i z).mp hjz))
  have hRange (n y : type_l hℳ B) (hy : branch_l (𝒩 := structure_l hℳ B hBase) ω D G H n y) :
      mem_l hℳ y.val W.val := by
    apply (hW y).mpr
    rcases hy with ⟨i, _, _, hiy⟩ | ⟨i, _, _, _, _, _, hiy⟩
    · exact Or.inl (SecondOrderFunctionProperties.value_mem_l hℳ hG'
        ((PowerlessRelativeClassFunctionAbsolute.value_l G i y).mp hiy)).2
    · exact Or.inr (SecondOrderFunctionProperties.value_mem_l hℳ hH'
        ((PowerlessRelativeClassFunctionAbsolute.value_l H i y).mp hiy)).2
  have hTotal (n : type_l hℳ B) (hn : mem_l hℳ n.val ω.val) :
      ∃! y : type_l hℳ B, mem_l hℳ y.val W.val ∧ formula_m.satisfies ((η.pushFree y).pushFree n) := by
    have hExists : ∃ y : type_l hℳ B, branch_l (𝒩 := structure_l hℳ B hBase) ω D G H n y := by
      rcases hCover n hn with ⟨i, hi, hin⟩ | ⟨i, t, hi, ht, hit, htn⟩
      · obtain ⟨y, hy, _⟩ := hG.2 i hi
        exact ⟨y, Or.inl ⟨i, hi, hin, hy.2⟩⟩
      · obtain ⟨y, hy, _⟩ := hH.2 i hi
        exact ⟨y, Or.inr ⟨i, t, hi, ht, hit, htn, hy.2⟩⟩
    obtain ⟨y, hy⟩ := hExists
    exact ⟨y, ⟨hRange n y hy, (hRead n y).mpr hy⟩,
      fun z hz => hUnique n z y ((hRead n z).mp hz.2) hy⟩
  obtain ⟨F, hF, hValue⟩ := PowerlessRelativeClassFunctionRelation.exists_l delta_l η ω W hTotal
  refine ⟨F, hF, fun n y => (hValue n y).trans ?_⟩
  exact ⟨fun h => ⟨h.1, (hRead n y).mp h.2.2⟩,
    fun h => ⟨h.1, hRange n y h.2, (hRead n y).mpr h.2⟩⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassInterleave
