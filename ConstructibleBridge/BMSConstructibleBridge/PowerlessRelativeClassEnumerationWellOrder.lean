import BMSConstructibleBridge.PowerlessRelativeClassEnumerationSectionDerives
import BMSConstructibleBridge.PowerlessRelativeClassFunctionProperties

/-! # 固定类内枚举的最小编号良序

用实际最小编号逆图拉回内部 ω 的隶属序。非空类内子集的编号集由
Δ₀ 分离构造，其极小元由正则性取得；不使用外部良基性或 Collection。
对象出口位于原 Z₂，保留给定满射和内部 ω 的明确前提。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassEnumerationWellOrder

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

/-- 比较实际逆图值；全部量词有内部 ω 界。 -/
def comparison_m {Γ Δ : SortContext ℒ} (ω J x y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| membershipLevyBound.boundedExists (up ω) <|
    .conj (PowerlessValueBounded.formula_m (up (up J)) (up (up x)) (.bvar (.there .here))) <|
      .conj (PowerlessValueBounded.formula_m (up (up J)) (up (up y)) (.bvar .here))
        (member_m (.bvar (.there .here)) (.bvar .here))

theorem comparison_delta_l {Γ Δ : SortContext ℒ} (ω J x y : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (comparison_m ω J x y) :=
  .bounded_exists _ (.bounded_exists _ (.conj (PowerlessValueBounded.delta_l _ _ _)
    (.conj (PowerlessValueBounded.delta_l _ _ _) (.rel _ _))))

def comparison_l {M0 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω J x y : carrier_l M0) : Prop :=
  ∃ i j, member_l M0 i ω ∧ member_l M0 j ω ∧ value_l J x i ∧ value_l J y j ∧ member_l M0 i j

theorem comparison_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω J x y : Term ℒ Γ Δ .set) :
    (comparison_m ω J x y).satisfies η ↔ comparison_l (ω.eval η) (J.eval η) (x.eval η) (y.eval η) := by
  simp only [comparison_m, comparison_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessValueBounded.formula_l, member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  exact ⟨fun ⟨i, hi, j, hj, hxi, hyj, hij⟩ => ⟨i, j, hi, hj, hxi, hyj, hij⟩,
    fun ⟨i, j, hi, hj, hxi, hyj, hij⟩ => ⟨i, hi, j, hj, hxi, hyj, hij⟩⟩

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒩" => structure_l hℳ B hBase

def precedes_l (ω G x y : type_l hℳ B) : Prop :=
  ∃ i j : type_l hℳ B, mem_l hℳ i.val ω.val ∧ mem_l hℳ j.val ω.val ∧
    PowerlessRelativeClassEnumerationSection.minimal_l (hBase := hBase) G x i ∧
    PowerlessRelativeClassEnumerationSection.minimal_l (hBase := hBase) G y j ∧ mem_l hℳ i.val j.val

theorem exists_l {ω G X : type_l hℳ B}
    (hω : omega_l (ℳ := 𝒩) ω) (hG : map_l (ℳ := 𝒩) G ω X)
    (hOnto : ∀ y : type_l hℳ B, mem_l hℳ y.val X.val → ∃ i : type_l hℳ B,
      mem_l hℳ i.val ω.val ∧ value_l (ℳ := 𝒩) G i y) :
    ∃ R : type_l hℳ B, wellOrder_l (ℳ := 𝒩) X R ∧
      ∀ x y : type_l hℳ B, value_l (ℳ := 𝒩) R x y ↔
        mem_l hℳ x.val X.val ∧ mem_l hℳ y.val X.val ∧ precedes_l (hBase := hBase) ω G x y := by
  obtain ⟨J, hJ, hSection⟩ := PowerlessRelativeClassEnumerationSection.exists_l (hBase := hBase) hω hOnto
  let φ : Formula ℒ [] [.set, .set, .set, .set] := comparison_m
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here)))) (.fvar .here) (.fvar (.there .here))
  let η : Env 𝒩 [] [.set, .set] := ((Env.empty).pushFree J).pushFree ω
  have hφ (x y : type_l hℳ B) : φ.satisfies ((η.pushFree y).pushFree x) ↔
      comparison_l (M0 := 𝒩) ω J x y := comparison_formula_l _ _ _ _ _
  obtain ⟨R, hR⟩ := PowerlessRelativeClassRelation.exists_l (φ := φ)
    (comparison_delta_l _ _ _ _) η X X
  have hRead (x y : type_l hℳ B) : value_l (ℳ := 𝒩) R x y ↔
      mem_l hℳ x.val X.val ∧ mem_l hℳ y.val X.val ∧ comparison_l (M0 := 𝒩) ω J x y := by
    constructor
    · rintro ⟨p, hp, hxy⟩
      obtain ⟨a, b, ha, hb, hab, hφab⟩ := (hR p).mp hp
      have hEq := (SecondOrderPairObjects.ordered_eq_l hℳ
        ((PowerlessRelativeClassFunctionAbsolute.ordered_l x y p).mp hxy)
        ((PowerlessRelativeClassFunctionAbsolute.ordered_l a b p).mp hab)).mp rfl
      have hxa : x = a := Subtype.ext hEq.1
      have hyb : y = b := Subtype.ext hEq.2
      simpa only [hxa, hyb] using And.intro ha (And.intro hb ((hφ a b).mp hφab))
    · rintro ⟨hx, hy, hxy⟩
      obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ x.val y.val
      let p' : type_l hℳ B := ⟨p, PowerlessRelativeClassPair.ordered_l hℳ hBase x.property y.property hp⟩
      have hp' := (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) x y p').mpr hp
      exact ⟨p', (hR p').mpr ⟨x, y, hx, hy, hp', (hφ x y).mpr hxy⟩, hp'⟩
  have hOrd := SecondOrderOmegaOrdinal.ordinal_l hℳ
    ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mp hω)
  have hUnique {x i j : type_l hℳ B} (hi : value_l (ℳ := 𝒩) J x i)
      (hj : value_l (ℳ := 𝒩) J x j) : i = j :=
    PowerlessRelativeClassFunctionProperties.value_unique_l hJ hi hj
  have hWO : wellOrder_l (ℳ := 𝒩) X R := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x _ hxx
      obtain ⟨_, _, i, j, hi, _, hxi, hxj, hij⟩ := (hRead x x).mp hxx
      have heq := hUnique hxi hxj
      subst j
      exact hOrd.wellOrder.linear.irrefl i.val hi hij
    · intro x y z hxyz hxy hyz
      obtain ⟨hx, _, i, j, hi, hj, hxi, hyj, hij⟩ := (hRead x y).mp hxy
      obtain ⟨_, hz, j', k, hj', hk, hyj', hzk, hjk⟩ := (hRead y z).mp hyz
      have heq := hUnique hyj hyj'
      subst j'
      exact (hRead x z).mpr ⟨hx, hz, i, k, hi, hk, hxi, hzk,
        hOrd.wellOrder.linear.trans i.val hi j.val hj k.val hk hij hjk⟩
    · intro x y hxy
      obtain ⟨i, ⟨hi, hxi⟩, _⟩ := hJ.2 x hxy.1
      obtain ⟨j, ⟨hj, hyj⟩, _⟩ := hJ.2 y hxy.2
      rcases hOrd.wellOrder.linear.compare i.val hi j.val hj with heq | hij | hji
      · have hij : i = j := Subtype.ext (SecondOrderQuotient.ext_l hℳ i.val j.val heq)
        subst j
        exact Or.inr (Or.inl (PowerlessRelativeClassFunctionProperties.value_unique_l hG
          ((hSection x i).mp hxi).2.2.1 ((hSection y i).mp hyj).2.2.1))
      · exact Or.inl ((hRead x y).mpr ⟨hxy.1, hxy.2, i, j, hi, hj, hxi, hyj, hij⟩)
      · exact Or.inr (Or.inr ((hRead y x).mpr ⟨hxy.2, hxy.1, j, i, hj, hi, hyj, hxi, hji⟩))
    · intro U hU
      let ψ : Formula ℒ [] [.set, .set, .set] := membershipLevyBound.boundedExists (.fvar (.there .here))
        (PowerlessValueBounded.formula_m (.fvar (.there (.there .here))) (.bvar .here) (.fvar .here))
      let ξ : Env 𝒩 [] [.set, .set] := ((Env.empty).pushFree J).pushFree U
      have hψ : Formula.IsDelta0 membershipLevyBound ψ := .bounded_exists _ (PowerlessValueBounded.delta_l _ _ _)
      have hψRead (i : type_l hℳ B) : ψ.satisfies (ξ.pushFree i) ↔
          ∃ x : type_l hℳ B, mem_l hℳ x.val U.val ∧ value_l (ℳ := 𝒩) J x i := by
        simp only [ψ, ξ, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
          membershipLevyBound, Formula.satisfies, PowerlessValueBounded.formula_l, Arguments.eval, Term.eval]
        rfl
      obtain ⟨S, hS⟩ := PowerlessRelativeClassDeltaSeparation.exists_l hψ ξ ω
      have hSRead (i : type_l hℳ B) : mem_l hℳ i.val S.val ↔ mem_l hℳ i.val ω.val ∧
          ∃ x : type_l hℳ B, mem_l hℳ x.val U.val ∧ value_l (ℳ := 𝒩) J x i :=
        (hS i).trans (and_congr Iff.rfl (hψRead i))
      obtain ⟨x, hx⟩ := hU.2
      obtain ⟨j, ⟨hj, hxj⟩, _⟩ := hJ.2 x (hU.1 x hx)
      have hFoundation := PowerlessRelativeClassStructure.foundation_l hℳ B hBase
      change ∀ S : type_l hℳ B, (∃ i : type_l hℳ B, mem_l hℳ i.val S.val) →
        ∃ i : type_l hℳ B, mem_l hℳ i.val S.val ∧ ∀ j : type_l hℳ B,
          mem_l hℳ j.val i.val → ¬mem_l hℳ j.val S.val at hFoundation
      obtain ⟨i, hiS, hMin⟩ := hFoundation S ⟨j, (hSRead j).mpr ⟨hj, x, hx, hxj⟩⟩
      obtain ⟨hi, y, hy, hyi⟩ := (hSRead i).mp hiS
      refine ⟨y, hy, ?_⟩
      intro z hz hzy
      obtain ⟨_, _, k, j, hk, _, hzk, hyj, hkj⟩ := (hRead z y).mp hzy
      have hji := hUnique hyj hyi
      subst j
      exact hMin k hkj ((hSRead k).mpr ⟨hk, z, hz, hzk⟩)
  refine ⟨R, hWO, fun x y => (hRead x y).trans ?_⟩
  apply and_congr_right
  intro hx
  apply and_congr_right
  intro hy
  constructor
  · rintro ⟨i, j, hi, hj, hxi, hyj, hij⟩
    exact ⟨i, j, hi, hj, ((hSection x i).mp hxi).2.2, ((hSection y j).mp hyj).2.2, hij⟩
  · rintro ⟨i, j, hi, hj, hxi, hyj, hij⟩
    exact ⟨i, j, hi, hj, (hSection x i).mpr ⟨hx, hi, hxi⟩, (hSection y j).mpr ⟨hy, hj, hyj⟩, hij⟩

private def wellOrderTerms_m {Γ Δ : SortContext ℒ} (X R : Term ℒ Γ Δ .set) :
    VariableSubstitution ℒ [SetTheory.SetSort.set, SetTheory.SetSort.set] Γ Δ
  | _, .here => X
  | _, .there .here => R

/-- 以实际两项代入现有良序正文。 -/
def wellOrder_m {Γ Δ : SortContext ℒ} (X R : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  ThirdOrderTheory.wellOrder_template_m.substitute (.map
    (fun {s} (v : Variable ([] : SortContext ℒ) s) => nomatch v) (wellOrderTerms_m X R))

theorem wellOrder_formula_l {M0 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env M0 Γ Δ) (X R : Term ℒ Γ Δ .set) :
    (wellOrder_m X R).satisfies η ↔ wellOrder_l (X.eval η) (R.eval η) := by
  rw [wellOrder_m, Formula.satisfies_substitute, ThirdOrderSemantics.wellOrder_formula_l]
  rfl

def schema_m : Formula ℒ [] [.set, .set, .set] :=
  let ω : Term ℒ [] [.set, .set, .set] .set := .fvar .here
  let G : Term ℒ [] [.set, .set, .set] .set := .fvar (.there .here)
  let X : Term ℒ [] [.set, .set, .set] .set := .fvar (.there (.there .here))
  .imp (SecondOrderOmegaSyntax.omega_m ω) <| .imp (map_m G ω X) <|
    .imp (PowerlessRelativeClassEnumerationSectionDerives.onto_m G ω X)
      (.existsE .set (wellOrder_m (up X) (.bvar .here)))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    sentence_m.TrueIn (structure_l hℳ B hBase) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, omega_formula_l, map_formula_l,
    PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l, wellOrder_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  intro hω hG hOnto
  obtain ⟨R, hR, _⟩ := exists_l (hBase := hBase) hω hG hOnto
  exact ⟨R, hR⟩

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m _ (fun _ h𝒩 B hBase => models_l h𝒩 B hBase)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassEnumerationWellOrder
