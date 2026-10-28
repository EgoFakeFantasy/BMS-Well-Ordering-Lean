import BMSConstructibleBridge.PowerlessRelativeClassDoubleTailFunction

/-! # 任意类内指标集上的内部有限迭代图

背景为原 Z₂。指标集 A 不限于 ω，初值图 F 与步进图 H 均是真实 Class
对象。逐行只需实际 raw ω 历史存在；共同母层中的有限限制给出纯 Δ₀
检查式，构造同一 A × ω 上的 Class 图。无需收集全部 raw 行函数。
本辅助模块不证明预算尾可数或低于 Ω，也不代替最终对象良序推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassIndexedIteration

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)
private abbrev up₄ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₃ t)

def matrix_m {Γ Δ : SortContext ℒ} (A ω e C H F U p y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists A <| membershipLevyBound.boundedExists (up ω) <|
    membershipLevyBound.boundedExists (up₂ C) <|
      let a : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
      let m : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
      let b : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar .here
      .conj (PowerlessPairBounded.ordered_m a m (up₃ p)) <|
        .conj (PowerlessValueBounded.formula_m (up₃ F) a b) <|
          membershipLevyBound.boundedExists (up₃ U) <| .conj
            (PowerlessFunctionTraceBounded.formula_m (up₄ ω) (up₄ e) (up₄ C) (up₄ H)
              (up b) (up m) (.bvar .here))
            (PowerlessValueBounded.formula_m (.bvar .here) (up m) (up₄ y))

theorem matrix_delta_l {Γ Δ : SortContext ℒ} (A ω e C H F U p y : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (matrix_m A ω e C H F U p y) :=
  .bounded_exists A (.bounded_exists (up ω) (.bounded_exists (up₂ C)
    (.conj (PowerlessPairBounded.ordered_delta_l _ _ _) (.conj (PowerlessValueBounded.delta_l _ _ _)
      (.bounded_exists (up₃ U) (.conj (PowerlessFunctionTraceBounded.delta_l _ _ _ _ _ _ _)
        (PowerlessValueBounded.delta_l _ _ _)))))))

def matrix_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (A ω e C H F U p y : carrier_l 𝒩) : Prop :=
  ∃ a, member_l 𝒩 a A ∧ ∃ m, member_l 𝒩 m ω ∧ ∃ b, member_l 𝒩 b C ∧
    ordered_l (ℳ := 𝒩) a m p ∧ value_l (ℳ := 𝒩) F a b ∧ ∃ g, member_l 𝒩 g U ∧
      PowerlessFunctionTraceBounded.trace_l (𝒩 := 𝒩) ω e C H b m g ∧ value_l (ℳ := 𝒩) g m y

theorem matrix_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (A ω e C H F U p y : Term ℒ Γ Δ .set) :
    (matrix_m A ω e C H F U p y).satisfies η ↔
      matrix_l (𝒩 := 𝒩) (A.eval η) (ω.eval η) (e.eval η) (C.eval η) (H.eval η)
        (F.eval η) (U.eval η) (p.eval η) (y.eval η) := by
  simp only [matrix_m, matrix_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessPairBounded.ordered_formula_l, PowerlessValueBounded.formula_l,
    PowerlessFunctionTraceBounded.formula_l, Arguments.eval,
    up₄, up₃, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₁" => structure_l hℳ B hBase

include hBase in
theorem exists_l (K : source_coding_l hℳ) (A C H F : type_l hℳ B)
    (hH : map_l (ℳ := 𝒱) H.val C.val C.val)
    (hF : map_l (ℳ := 𝒱) F.val A.val C.val)
    (hRows : ∀ a b, mem_l hℳ a A.val → value_l (ℳ := 𝒱) F.val a b →
      ∃ J, PowerlessFunctionIteration.iteration_l (ℳ := 𝒱) K.omega
        (numberCode_l K (SecondOrderModel.zero_l ℳ)).val C.val H.val b J) :
    ∃ U : SecondOrderQuotient.type_l hℳ, ∃ P R : type_l hℳ B,
      (∀ p, mem_l hℳ p P.val ↔ ∃ a m, mem_l hℳ a A.val ∧ mem_l hℳ m K.omega ∧
        ordered_l (ℳ := 𝒱) a m p) ∧ map_l (ℳ := 𝒱) R.val P.val C.val ∧
      ∀ p y, value_l (ℳ := 𝒱) R.val p y ↔ mem_l hℳ p P.val ∧ mem_l hℳ y C.val ∧
        matrix_l (𝒩 := 𝒱) A.val K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val
          C.val H.val F.val U p y := by
  let O : type_l hℳ B := ⟨K.omega, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)⟩
  let e : type_l hℳ B := ⟨(numberCode_l K (SecondOrderModel.zero_l ℳ)).val,
    PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase O.property
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).property⟩
  let η₀ : Env 𝒩₁ [] [.set] := Env.empty.pushFree C
  obtain ⟨δ, U, hδ, hU, hωU, hCU⟩ :=
    PowerlessRelativeClassLimitParameterBounds.exists_l (hBase := hBase) η₀ O
  have hCU' : mem_l hℳ C.val U := hCU _ .here
  let U' : type_l hℳ B := ⟨U, PowerlessRelativeLevelClosure.class_l hℳ hBase hU⟩
  obtain ⟨P, hP⟩ := PowerlessRelativeClassProduct.exists_l hBase A O
  have hPRead (p : SecondOrderQuotient.type_l hℳ) : mem_l hℳ p P.val ↔
      ∃ a m, mem_l hℳ a A.val ∧ mem_l hℳ m K.omega ∧ ordered_l (ℳ := 𝒱) a m p := by
    constructor
    · intro hp
      let p' : type_l hℳ B := ⟨p, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase P.property hp⟩
      obtain ⟨a, m, ha, hm, ham⟩ := (hP p').mp hp
      exact ⟨a.val, m.val, ha, hm, (PowerlessRelativeClassFunctionAbsolute.ordered_l a m p').mp ham⟩
    · rintro ⟨a, m, ha, hm, ham⟩
      let a' : type_l hℳ B := ⟨a, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase A.property ha⟩
      let m' : type_l hℳ B := ⟨m, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase O.property hm⟩
      let p' : type_l hℳ B := ⟨p, PowerlessRelativeClassPair.ordered_l hℳ hBase a'.property m'.property ham⟩
      exact (hP p').mpr ⟨a', m', ha, hm,
        (PowerlessRelativeClassFunctionAbsolute.ordered_l a' m' p').mpr ham⟩
  let η : Env 𝒩₁ [] [.set, .set, .set, .set, .set, .set, .set] :=
    (((((((Env.empty.pushFree A).pushFree O).pushFree e).pushFree C).pushFree H).pushFree F).pushFree U')
  let u : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let f : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let h : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  let c : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there .here)))))
  let z : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there (.there .here))))))
  let w : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))
  let a : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] :=
    matrix_m a w z c h f u (.fvar .here) (.fvar (.there .here))
  have hφ (p y : SecondOrderQuotient.type_l hℳ) : φ.satisfies
      (((PowerlessRelativeClassRelativization.env_l η).pushFree y).pushFree p) ↔
      matrix_l (𝒩 := 𝒱) A.val K.omega e.val C.val H.val F.val U p y :=
    matrix_formula_l _ _ _ _ _ _ _ _ _ _
  have hTotal (p : SecondOrderQuotient.type_l hℳ) (hp : mem_l hℳ p P.val) :
      ∃! y, mem_l hℳ y C.val ∧ φ.satisfies
        (((PowerlessRelativeClassRelativization.env_l η).pushFree y).pushFree p) := by
    obtain ⟨a, m, ha, hm, ham⟩ := (hPRead p).mp hp
    obtain ⟨b, ⟨hb, hab⟩, _⟩ := hF.2 a ha
    obtain ⟨J, hJ⟩ := hRows a b ha hab
    obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨m, hm⟩
    have hnm : (numberCode_l K n).val = m := congrArg Subtype.val hn
    obtain ⟨g, hgU, hg⟩ := SecondOrderFiniteFunctionRestriction.exists_l K hBase hδ hU hωU hCU' hJ n
    have hTrace := hg
    obtain ⟨t, _, ht, hMap, _, _⟩ := hg
    obtain ⟨y, hy, _⟩ := hMap.2 m ((ht m).mpr (Or.inr hnm.symm))
    refine ⟨y, ⟨hy.1, (hφ p y).mpr ⟨a, ha, m, hm, b, hb, ham, hab, g, hgU,
      hnm ▸ hTrace, hy.2⟩⟩, ?_⟩
    rintro y' ⟨_, hy'⟩
    obtain ⟨a', _, m', _, b', _, ham', hab', g', _, hg', hgy'⟩ := (hφ p y').mp hy'
    obtain ⟨hea, hem⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ ham' ham).mp rfl
    subst a'
    subst m'
    have heb := SecondOrderFunctionProperties.value_unique_l hℳ hF hab' hab
    subst b'
    have hJy := SecondOrderFiniteFunctionAgreement.value_l K hH hJ hm (hnm ▸ hTrace) hy.2
    have hJy' := SecondOrderFiniteFunctionAgreement.value_l K hH hJ hm hg' hgy'
    exact SecondOrderFunctionProperties.value_unique_l hℳ hJ.1 hJy' hJy
  obtain ⟨R, hR, hRead⟩ := PowerlessRelativeClassRawFunction.exists_l (hBase := hBase)
    (φ := φ) (matrix_delta_l _ _ _ _ _ _ _ _ _) η P C hTotal
  exact ⟨U, P, R, hPRead, hR, fun p y =>
    (hRead p y).trans (and_congr Iff.rfl (and_congr Iff.rfl (hφ p y)))⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassIndexedIteration
