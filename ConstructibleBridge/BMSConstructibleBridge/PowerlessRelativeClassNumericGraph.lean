import BMSConstructibleBridge.PowerlessBoundedNumericPairing
import BMSConstructibleBridge.PowerlessRelativeClassFiniteSequencesDerives
import BMSConstructibleBridge.PowerlessRelativeClassDeltaSeparation
import BMSConstructibleBridge.PowerlessBMSQuotientReals
import BMSConstructibleBridge.SecondOrderPairingBounds

/-! # 类内关系的单张数编码实数

先在类内 ω 上做实际 Δ₀ 分离，再用内部平方分支配数的单射性读取两坐标。
有限序列界由既有存在定理提供其类内与环境双重规格，不额外假定 Collection。
输出 U 确实属于相对类；原模型实数 R 与 U 逐数对应。这里没有证明任意
未编码见证族的内域闭包，也没有把环境中的任意实数自动认作类内对象。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassNumericGraph

open Logic FirstOrder StabilityFrame ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def body_m {Γ Δ : SortContext ℒ} (ω e S Q c : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| membershipLevyBound.boundedExists (up ω) <| .conj
    (PowerlessBoundedNumericPairing.formula_m (up (up ω)) (up (up e)) (up (up S))
      (.bvar (.there .here)) (.bvar .here) (up (up c)))
    (PowerlessValueBounded.formula_m (up (up Q)) (.bvar (.there .here)) (.bvar .here))

theorem body_delta_m {Γ Δ : SortContext ℒ} (ω e S Q c : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (body_m ω e S Q c) :=
  .bounded_exists _ (.bounded_exists _ (.conj (PowerlessBoundedNumericPairing.delta_l _ _ _ _ _ _)
    (PowerlessValueBounded.delta_l _ _ _)))

def body_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e S Q c : carrier_l ℳ₀) : Prop :=
  ∃ a, member_l ℳ₀ a ω ∧ ∃ b, member_l ℳ₀ b ω ∧
    PowerlessBoundedNumericPairing.holds_l (𝒩 := ℳ₀) ω e S a b c ∧
    ThirdOrderSemantics.value_l (ℳ := ℳ₀) Q a b

theorem body_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e S Q c : Term ℒ Γ Δ .set) :
    (body_m ω e S Q c).satisfies η ↔ body_l (ω.eval η) (e.eval η) (S.eval η) (Q.eval η) (c.eval η) := by
  simp only [body_m, body_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessBoundedNumericPairing.formula_l,
    PowerlessValueBounded.formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def spec_m {Γ Δ : SortContext ℒ} (ω e S Q U : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .iff (SecondOrderObjectSyntax.member_m (.bvar .here) (up U)) <|
    .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up ω))
      (body_m (up ω) (up e) (up S) (up Q) (.bvar .here))

def schema_m : Formula ℒ [] [.set, .set, .set, .set] :=
  .existsE .set (spec_m (.fvar .here) (.fvar (.there .here))
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here)))) (.bvar .here))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem spec_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e S Q U : Term ℒ Γ Δ .set) :
    (spec_m ω e S Q U).satisfies η ↔ ∀ c, member_l 𝒩 c (U.eval η) ↔
      member_l 𝒩 c (ω.eval η) ∧ body_l (ω.eval η) (e.eval η) (S.eval η) (Q.eval η) c := by
  simp only [spec_m, Formula.satisfies, body_formula_l, SecondOrderObjectSyntax.member_m,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒩" => structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

include hBase in
theorem exists_l (ω e S Q : type_l hℳ B) : ∃ U : type_l hℳ B, ∀ c : type_l hℳ B,
    mem_l hℳ c.val U.val ↔ mem_l hℳ c.val ω.val ∧ body_l (ℳ₀ := 𝒩) ω e S Q c := by
  let η : Env 𝒩 [] [.set, .set, .set, .set] :=
    ((((Env.empty).pushFree Q).pushFree S).pushFree e).pushFree ω
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] := body_m
    (.fvar (.there .here)) (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here))))) (.fvar .here)
  obtain ⟨U, hU⟩ := PowerlessRelativeClassDeltaSeparation.exists_l (φ := φ) (body_delta_m _ _ _ _ _) η ω
  exact ⟨U, fun c => (hU c).trans (and_congr Iff.rfl (body_formula_l (η.pushFree c) _ _ _ _ _))⟩

include hBase in
/-- 类内分离规格经过有界绝对性覆盖环境中的全部对象。 -/
theorem exists_ambient_l (ω e S Q : type_l hℳ B) : ∃ U : type_l hℳ B, ∀ c,
    mem_l hℳ c U.val ↔ mem_l hℳ c ω.val ∧ body_l (ℳ₀ := 𝒱) ω.val e.val S.val Q.val c := by
  obtain ⟨U, hU⟩ := exists_l (hBase := hBase) ω e S Q
  let η : Env 𝒩 [] [.set, .set, .set, .set] :=
    ((((Env.empty).pushFree Q).pushFree S).pushFree e).pushFree ω
  have hAbs (c : type_l hℳ B) : body_l (ℳ₀ := 𝒩) ω e S Q c ↔
      body_l (ℳ₀ := 𝒱) ω.val e.val S.val Q.val c.val := by
    let φ : Formula ℒ [] [.set, .set, .set, .set, .set] := body_m
      (.fvar (.there .here)) (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here))))) (.fvar .here)
    exact (body_formula_l (η.pushFree c) _ _ _ _ _).symm.trans
      ((PowerlessRelativeClassBounded.formula_l (φ := φ) (body_delta_m _ _ _ _ _)
        (η.pushFree c)).trans
        (body_formula_l (PowerlessRelativeClassRelativization.env_l (η.pushFree c)) _ _ _ _ _))
  refine ⟨U, fun c => ?_⟩
  constructor
  · intro hc
    let c' : type_l hℳ B := ⟨c, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase U.property hc⟩
    obtain ⟨hcω, hBody⟩ := (hU c').mp hc
    exact ⟨hcω, (hAbs c').mp hBody⟩
  · rintro ⟨hcω, hBody⟩
    let c' : type_l hℳ B := ⟨c, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property hcω⟩
    exact (hU c').mpr ⟨hcω, (hAbs c').mpr hBody⟩

include hBase in
/-- 原模型实数的商代表就是类内 U，不只是一个环境关系码。 -/
theorem coded_l (K : source_coding_l hℳ) (Q : type_l hℳ B) :
    ∃ U : type_l hℳ B, ∃ hU : ∀ c, mem_l hℳ c U.val → mem_l hℳ c K.omega,
      ∃ R : SecondOrderModel.set_l ℳ, setRel_l K ⟨U.val, hU⟩ R ∧ ∀ n m,
        SecondOrderPairing.relation_l R n m ↔
          ThirdOrderSemantics.value_l (ℳ := 𝒱) Q.val (numberCode_l K n).val (numberCode_l K m).val := by
  let O : type_l hℳ B := ⟨K.omega, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)⟩
  let e : type_l hℳ B := ⟨(numberCode_l K (SecondOrderModel.zero_l ℳ)).val,
    PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase O.property
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).property⟩
  have hω := (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) O).mpr K.omega_spec
  obtain ⟨S, hS, _⟩ := PowerlessRelativeClassFiniteSequencesDerives.exists_ambient_l (hBase := hBase)
    (X := O) hω
  obtain ⟨U, hU⟩ := exists_ambient_l (hBase := hBase) O e S Q
  have hSub : ∀ c, mem_l hℳ c U.val → mem_l hℳ c K.omega := fun c hc => ((hU c).mp hc).1
  have hRead n m : mem_l hℳ (numberCode_l K (SecondOrderPairing.value_l n m)).val U.val ↔
      ThirdOrderSemantics.value_l (ℳ := 𝒱) Q.val (numberCode_l K n).val (numberCode_l K m).val := by
    constructor
    · intro hc
      obtain ⟨_, a, ha, b, hb, hPair, hValue⟩ := (hU _).mp hc
      obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨a, ha⟩
      obtain ⟨j, hj⟩ := numberCode_surjective_l K ⟨b, hb⟩
      have hi' : (numberCode_l K i).val = a := congrArg Subtype.val hi
      have hj' : (numberCode_l K j).val = b := congrArg Subtype.val hj
      rw [← hi', ← hj'] at hPair hValue
      have hCode := (PowerlessBoundedNumericPairing.instance_l K hS i j _).mp hPair
      have hNum : SecondOrderPairing.value_l i j = SecondOrderPairing.value_l n m :=
        numberCode_injective_l K (Subtype.ext hCode.symm)
      obtain ⟨hiEq, hjEq⟩ := SecondOrderPairingBounds.injective_l hℳ i j n m hNum
      simpa only [hiEq, hjEq] using hValue
    · intro hValue
      exact (hU _).mpr ⟨(numberCode_l K (SecondOrderPairing.value_l n m)).property,
        (numberCode_l K n).val, (numberCode_l K n).property,
        (numberCode_l K m).val, (numberCode_l K m).property,
        (PowerlessBoundedNumericPairing.instance_l K hS n m _).mpr rfl, hValue⟩
  obtain ⟨R, hR⟩ := PowerlessBMSQuotientReals.trace_exists_l K ⟨U.val, hSub⟩
  exact ⟨U, hSub, R, hR, fun n m => (hR (SecondOrderPairing.value_l n m)).symm.trans (hRead n m)⟩

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    sentence_m.TrueIn (structure_l hℳ B hBase) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  obtain ⟨U, hU⟩ := exists_l (hBase := hBase) (η.freeVal .here) (η.freeVal (.there .here))
    (η.freeVal (.there (.there .here))) (η.freeVal (.there (.there (.there .here))))
  exact ⟨U, (spec_formula_l (η.pushBound U) _ _ _ _ _).mpr hU⟩

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m _ (fun _ h𝒩 B hBase => models_l h𝒩 B hBase)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassNumericGraph
