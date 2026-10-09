import BMSConstructibleBridge.PowerlessRelativeClassFiniteNumericEnumeration
import BMSConstructibleBridge.PowerlessRelativeClassTwoEntrySequence
import BMSConstructibleBridge.PowerlessRelativeClassFunctionComposition
import BMSConstructibleBridge.PowerlessRelativeClassProduct
import BMSConstructibleBridge.PowerlessBMSQuotientSuccessor

/-! # 两个类内可枚举集合的实际积枚举

全部内部自然数有限序列已有类内枚举。取序列前两项作为两个给定满射的
编号，解码成实际有序对；没有两项时使用明确的默认对。解码图是纯 Δ₀，
最后与有限序列枚举复合。这里不构造超限枚举历史，也不假定完整 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassProductEnumeration

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)
private abbrev up₄ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₃ t)

def entry_m {Γ Δ : SortContext ℒ} (ω X Y E J e one f p : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| membershipLevyBound.boundedExists (up ω) <|
    membershipLevyBound.boundedExists (up₂ X) <| membershipLevyBound.boundedExists (up₃ Y) <|
      let i : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there (.there .here)))
      let j : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
      let x : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
      let y : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar .here
      .conj (PowerlessValueBounded.formula_m (up₄ f) (up₄ e) i) <|
        .conj (PowerlessValueBounded.formula_m (up₄ f) (up₄ one) j) <|
          .conj (PowerlessValueBounded.formula_m (up₄ E) i x) <|
            .conj (PowerlessValueBounded.formula_m (up₄ J) j y)
              (PowerlessPairBounded.ordered_m x y (up₄ p))

theorem entry_delta_l {Γ Δ : SortContext ℒ} (ω X Y E J e one f p : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (entry_m ω X Y E J e one f p) :=
  .bounded_exists ω (.bounded_exists (up ω) (.bounded_exists (up₂ X) (.bounded_exists (up₃ Y)
    (.conj (PowerlessValueBounded.delta_l _ _ _) (.conj (PowerlessValueBounded.delta_l _ _ _)
      (.conj (PowerlessValueBounded.delta_l _ _ _) (.conj (PowerlessValueBounded.delta_l _ _ _)
        (PowerlessPairBounded.ordered_delta_l _ _ _))))))))

def entry_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω X Y E J e one f p : carrier_l 𝒩) : Prop :=
  ∃ i, member_l 𝒩 i ω ∧ ∃ j, member_l 𝒩 j ω ∧
    ∃ x, member_l 𝒩 x X ∧ ∃ y, member_l 𝒩 y Y ∧
      value_l (ℳ := 𝒩) f e i ∧ value_l (ℳ := 𝒩) f one j ∧
        value_l (ℳ := 𝒩) E i x ∧ value_l (ℳ := 𝒩) J j y ∧ ordered_l (ℳ := 𝒩) x y p

theorem entry_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω X Y E J e one f p : Term ℒ Γ Δ .set) :
    (entry_m ω X Y E J e one f p).satisfies η ↔
      entry_l (ω.eval η) (X.eval η) (Y.eval η) (E.eval η) (J.eval η)
        (e.eval η) (one.eval η) (f.eval η) (p.eval η) := by
  simp only [entry_m, entry_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessValueBounded.formula_l,
    PowerlessPairBounded.ordered_formula_l, Arguments.eval,
    up₄, up₃, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

def formula_m {Γ Δ : SortContext ℒ} (ω X Y E J P e one d f p : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (entry_m ω X Y E J e one f p) <| .conj
    (membershipLevyBound.boundedForall P <| .neg
      (entry_m (up ω) (up X) (up Y) (up E) (up J) (up e) (up one) (up f) (.bvar .here)))
    (.equal p d)

theorem delta_l {Γ Δ : SortContext ℒ} (ω X Y E J P e one d f p : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m ω X Y E J P e one d f p) :=
  .disj (entry_delta_l _ _ _ _ _ _ _ _ _)
    (.conj (.bounded_forall P (.neg (entry_delta_l _ _ _ _ _ _ _ _ _))) (.equal _ _))

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω X Y E J P e one d f p : Term ℒ Γ Δ .set) :
    (formula_m ω X Y E J P e one d f p).satisfies η ↔
      entry_l («𝒩» := 𝒩) (ω.eval η) (X.eval η) (Y.eval η) (E.eval η) (J.eval η)
        (e.eval η) (one.eval η) (f.eval η) (p.eval η) ∨
      ((∀ q, member_l 𝒩 q (P.eval η) → ¬entry_l («𝒩» := 𝒩)
        (ω.eval η) (X.eval η) (Y.eval η) (E.eval η) (J.eval η) (e.eval η) (one.eval η) (f.eval η) q) ∧
          p.eval η = d.eval η) := by
  simp only [formula_m, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, entry_formula_l, Arguments.eval,
    up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒩" => structure_l hℳ B hBase

theorem entry_unique_l {A ω X Y E J e one f p q : type_l hℳ B}
    (hf : map_l (ℳ := 𝒩) f A ω) (hE : map_l (ℳ := 𝒩) E ω X) (hJ : map_l (ℳ := 𝒩) J ω Y)
    (hp : entry_l («𝒩» := 𝒩) ω X Y E J e one f p)
    (hq : entry_l («𝒩» := 𝒩) ω X Y E J e one f q) : p = q := by
  obtain ⟨i, _, j, _, x, _, y, _, hfi, hfj, hEx, hJy, hpPair⟩ := hp
  obtain ⟨i', _, j', _, x', _, y', _, hfi', hfj', hEx', hJy', hqPair⟩ := hq
  have hi := PowerlessRelativeClassFunctionComposition.value_unique_l hf hfi' hfi
  have hj := PowerlessRelativeClassFunctionComposition.value_unique_l hf hfj' hfj
  subst i'
  subst j'
  have hx := PowerlessRelativeClassFunctionComposition.value_unique_l hE hEx' hEx
  have hy := PowerlessRelativeClassFunctionComposition.value_unique_l hJ hJy' hJy
  subst x'
  subst y'
  exact Subtype.ext ((SecondOrderPairObjects.ordered_eq_l hℳ
    ((PowerlessRelativeClassFunctionAbsolute.ordered_l x y p).mp hpPair)
    ((PowerlessRelativeClassFunctionAbsolute.ordered_l x y q).mp hqPair)).mpr ⟨rfl, rfl⟩)

private abbrev parameters_m : SortContext ℒ := [.set, .set, .set, .set, .set, .set, .set, .set, .set]

/-- 解码全域图；默认对只处理不能读出两个编号的有限序列。 -/
theorem decoder_l {ω X Y E J P e one d S : type_l hℳ B}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒩) ω ω S)
    (hE : map_l (ℳ := 𝒩) E ω X) (hJ : map_l (ℳ := 𝒩) J ω Y)
    (hd : mem_l hℳ d.val P.val) :
    ∃ R : type_l hℳ B, map_l (ℳ := 𝒩) R S P ∧ ∀ f p : type_l hℳ B,
      entry_l («𝒩» := 𝒩) ω X Y E J e one f p →
        mem_l hℳ f.val S.val → mem_l hℳ p.val P.val → value_l (ℳ := 𝒩) R f p := by
  classical
  let η : Env 𝒩 [] parameters_m :=
    ((((((((Env.empty.pushFree d).pushFree one).pushFree e).pushFree J).pushFree E).pushFree Y).pushFree X).pushFree ω).pushFree P
  let q : Term ℒ [] (.set :: .set :: parameters_m) .set := .fvar (.there (.there .here))
  let w : Term ℒ [] (.set :: .set :: parameters_m) .set := .fvar (.there (.there (.there .here)))
  let x : Term ℒ [] (.set :: .set :: parameters_m) .set := .fvar (.there (.there (.there (.there .here))))
  let y : Term ℒ [] (.set :: .set :: parameters_m) .set := .fvar (.there (.there (.there (.there (.there .here)))))
  let g : Term ℒ [] (.set :: .set :: parameters_m) .set := .fvar (.there (.there (.there (.there (.there (.there .here))))))
  let j : Term ℒ [] (.set :: .set :: parameters_m) .set := .fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))
  let z : Term ℒ [] (.set :: .set :: parameters_m) .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
  let o : Term ℒ [] (.set :: .set :: parameters_m) .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
  let a : Term ℒ [] (.set :: .set :: parameters_m) .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
  let φ : Formula ℒ [] (.set :: .set :: parameters_m) :=
    formula_m w x y g j q z o a (.fvar .here) (.fvar (.there .here))
  have hφ (f p : type_l hℳ B) : φ.satisfies ((η.pushFree p).pushFree f) ↔
      entry_l («𝒩» := 𝒩) ω X Y E J e one f p ∨
        ((∀ q : type_l hℳ B, mem_l hℳ q.val P.val →
          ¬entry_l («𝒩» := 𝒩) ω X Y E J e one f q) ∧ p = d) :=
    formula_l ((η.pushFree p).pushFree f) w x y g j q z o a (.fvar .here) (.fvar (.there .here))
  have hTotal (f : type_l hℳ B) (hf : mem_l hℳ f.val S.val) :
      ∃! p : type_l hℳ B, mem_l hℳ p.val P.val ∧ φ.satisfies ((η.pushFree p).pushFree f) := by
    by_cases h : ∃ p : type_l hℳ B, mem_l hℳ p.val P.val ∧ entry_l («𝒩» := 𝒩) ω X Y E J e one f p
    · obtain ⟨p, hp, hEntry⟩ := h
      refine ⟨p, ⟨hp, (hφ f p).mpr (Or.inl hEntry)⟩, ?_⟩
      rintro r ⟨_, hr⟩
      rcases (hφ f r).mp hr with hr | ⟨hNone, _⟩
      · obtain ⟨_, _, hfMap⟩ := (hS f).mp hf
        exact entry_unique_l hfMap hE hJ hr hEntry
      · exact False.elim (hNone p hp hEntry)
    · have hNone : ∀ p : type_l hℳ B, mem_l hℳ p.val P.val →
          ¬entry_l («𝒩» := 𝒩) ω X Y E J e one f p := fun p hp hEntry => h ⟨p, hp, hEntry⟩
      refine ⟨d, ⟨hd, (hφ f d).mpr (Or.inr ⟨hNone, rfl⟩)⟩, ?_⟩
      rintro r ⟨hr, hφr⟩
      rcases (hφ f r).mp hφr with hEntry | ⟨_, hrd⟩
      · exact False.elim (hNone r hr hEntry)
      · exact hrd
  obtain ⟨R, hR, hRead⟩ := PowerlessRelativeClassFunctionRelation.exists_l (hBase := hBase)
    (φ := φ) (delta_l w x y g j q z o a (.fvar .here) (.fvar (.there .here))) η S P hTotal
  exact ⟨R, hR, fun f p hEntry hf hp => (hRead f p).mpr ⟨hf, hp, (hφ f p).mpr (Or.inl hEntry)⟩⟩

/-- 精确的类坐标积规格与两个实际类满射产生实际类满射，不抽取见证函数。 -/
theorem exists_l {ω X Y E J P : type_l hℳ B}
    (hω : omega_l (ℳ := 𝒩) ω)
    (hE : map_l (ℳ := 𝒩) E ω X) (hJ : map_l (ℳ := 𝒩) J ω Y)
    (hEOnto : ∀ x : type_l hℳ B, mem_l hℳ x.val X.val →
      ∃ i : type_l hℳ B, mem_l hℳ i.val ω.val ∧ value_l (ℳ := 𝒩) E i x)
    (hJOnto : ∀ y : type_l hℳ B, mem_l hℳ y.val Y.val →
      ∃ j : type_l hℳ B, mem_l hℳ j.val ω.val ∧ value_l (ℳ := 𝒩) J j y)
    (hP : ∀ p : type_l hℳ B, mem_l hℳ p.val P.val ↔ ∃ x y : type_l hℳ B,
      mem_l hℳ x.val X.val ∧ mem_l hℳ y.val Y.val ∧ ordered_l (ℳ := 𝒩) x y p) :
    ∃ U : type_l hℳ B, map_l (ℳ := 𝒩) U ω P ∧ ∀ p : type_l hℳ B,
      mem_l hℳ p.val P.val → ∃ i : type_l hℳ B, mem_l hℳ i.val ω.val ∧ value_l (ℳ := 𝒩) U i p := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hωEq := SecondOrderOmega.unique_l hℳ
    ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mp hω) K.omega_spec
  have hNum (i : SecondOrderModel.num_l ℳ) :
      PowerlessRelativeClassCorrespondence.member_l hℳ B (numberCode_l K i).val :=
    PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property
      (hωEq.symm ▸ (numberCode_l K i).property)
  let e : type_l hℳ B := ⟨(numberCode_l K (SecondOrderModel.zero_l ℳ)).val, hNum _⟩
  let one : type_l hℳ B := ⟨(numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).val, hNum _⟩
  let two : type_l hℳ B := ⟨(numberCode_l K (SecondOrderModel.succ_l
    (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ)))).val, hNum _⟩
  have heω : mem_l hℳ e.val ω.val := hωEq.symm ▸ (numberCode_l K (SecondOrderModel.zero_l ℳ)).property
  have htwoω : mem_l hℳ two.val ω.val := hωEq.symm ▸
    (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ)))).property
  have he : PowerlessNatural.zero_l (ℳ := 𝒩) e := fun x => PowerlessBMSQuotientSuccessor.zero_l K x.val
  have hone : PowerlessNatural.successor_l (ℳ := 𝒩) e one :=
    (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) e one).mpr
      (PowerlessBMSQuotientSuccessor.successor_l K (SecondOrderModel.zero_l ℳ))
  have htwo : PowerlessNatural.successor_l (ℳ := 𝒩) one two :=
    (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) one two).mpr
      (PowerlessBMSQuotientSuccessor.successor_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ)))
  obtain ⟨x₀, ⟨hx₀, _⟩, _⟩ := hE.2 e heω
  obtain ⟨y₀, ⟨hy₀, _⟩, _⟩ := hJ.2 e heω
  obtain ⟨d₀, hd₀⟩ := SecondOrderPairObjects.ordered_exists_l hℳ x₀.val y₀.val
  let d : type_l hℳ B := ⟨d₀, PowerlessRelativeClassPair.ordered_l hℳ hBase x₀.property y₀.property hd₀⟩
  have hdPair : ordered_l (ℳ := 𝒩) x₀ y₀ d :=
    (PowerlessRelativeClassFunctionAbsolute.ordered_l x₀ y₀ d).mpr hd₀
  have hdP := (hP d).mpr ⟨x₀, y₀, hx₀, hy₀, hdPair⟩
  obtain ⟨S, hS, F, hF, hFOnto⟩ := PowerlessRelativeClassFiniteNumericEnumeration.exists_l (hBase := hBase) hω
  obtain ⟨R, hR, hDecode⟩ := decoder_l (e := e) (one := one) hS hE hJ hdP
  obtain ⟨U, hU, hRead⟩ := PowerlessRelativeClassFunctionComposition.exists_l hF hR
  refine ⟨U, hU, ?_⟩
  intro p hp
  obtain ⟨x, y, hx, hy, hxy⟩ := (hP p).mp hp
  obtain ⟨i, hi, hix⟩ := hEOnto x hx
  obtain ⟨j, hj, hjy⟩ := hJOnto y hy
  obtain ⟨f, hf, hfi, hfj⟩ := PowerlessRelativeClassTwoEntrySequence.exists_l he hone htwo hi hj
  have hfS := (hS f).mpr ⟨two, htwoω, hf⟩
  have hfp := hDecode f p ⟨i, hi, j, hj, x, hx, y, hy, hfi, hfj, hix, hjy, hxy⟩ hfS hp
  obtain ⟨n, hn, hnf⟩ := hFOnto f hfS
  exact ⟨n, hn, (hRead n p).mpr ⟨hn, hp, f, hfS, hnf, hfp⟩⟩

#print axioms entry_delta_l
#print axioms decoder_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassProductEnumeration
