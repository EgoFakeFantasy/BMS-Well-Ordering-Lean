import BMSConstructibleBridge.PowerlessFunctionHistoryLimitBound
import BMSConstructibleBridge.PowerlessHierarchyLightHistoryBudgetExists

/-! # 任意实际类内单值算子的长历史入类

对象语言为纯隶属 ℒ，背景为原 Z₂。初值 X 与相对构造基集 B 分开；
实际层 W 作值域，给定 Class 后继图 D 只需单值。已有 raw 历史在零、
后继、非零极限分别用空图、同层单点延拓和精确前缀并取得成员界。
统一预算由原规范尾真正构造，不假设 Collection、类内超限递归或历史
事先属于 Class。最终导出原 Derives；这仍不构造任意算子的 raw 历史，
也不推出预算尾低于 Ω。预算块的实际方程与入类需由调用端接入。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFunctionHistoryClass

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l mk_l)
open PowerlessFunctionHistoryAgreement (functional_l functional_m functional_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def point_m {Γ Δ : SortContext ℒ} (B X D W Q a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <|
    let w (t : Term ℒ Γ Δ .set) := up (up (up t))
    let δ : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
    let C : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let f : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar .here
    .imp (PowerlessValueBounded.formula_m (w Q) (w a) δ) <|
      .imp (PowerlessRelativeHierarchySyntax.level_m (w B) δ C) <|
        .imp (PowerlessHierarchyLightHistory.formula_m (w X) (w D) (w a) (w W) f)
          (SecondOrderObjectSyntax.member_m f C)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Ordinal" => SetTheory.Structure.IsOrdinal
  (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱)

def point_l (B X D W Q a : type_l hℳ) : Prop :=
  ∀ δ C f, value_l (ℳ := 𝒱) Q a δ →
    PowerlessRelativeHierarchySemantics.level_l hℳ B δ C →
      PowerlessHierarchyLightHistory.history_l hℳ X D a W f → mem_l hℳ f C

theorem point_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (B X D W Q a : Term ℒ Γ Δ .set) :
    (point_m B X D W Q a).satisfies η ↔
      point_l hℳ (B.eval η) (X.eval η) (D.eval η) (W.eval η) (Q.eval η) (a.eval η) := by
  simp only [point_m, point_l, Formula.satisfies, PowerlessValueBounded.formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessHierarchyLightHistory.reading_formula_l hℳ, SecondOrderObjectSyntax.member_m,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

/-- 初值只需在真实陪域内；预算母层的 W 成员证据实际覆盖该初值。 -/
theorem step_l {B X D W A Q a : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hD : functional_l hℳ D) (hXW : mem_l hℳ X W)
    (hBudget : PowerlessHierarchyLightHistoryBudgetInduction.budget_l hℳ B D W A Q)
    (hPast : ∀ b, mem_l hℳ b a → point_l hℳ B X D W Q b) :
    point_l hℳ B X D W Q a := by
  intro δ C f hQ hC hf
  have ha : Ordinal a := SetTheory.Structure.IsOrdinal.mem hBudget.domain_ordinal
    (hBudget.source a δ hQ)
  obtain ⟨ξ, C₀, C₁, hLimit, hC₀, hDef₀₁, hDef₁C, _hBC₀, hDC₀, hWC₀, haC₀, hEarlier⟩ :=
    hBudget.layers a δ C hQ hC
  have hTransC₀ := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hC₀
  have hTransC₁ := SecondOrderMemberDefProperties.transitive_l hℳ hDef₀₁
    (fun x y hx hy => hTransC₀ x hx y hy)
  have hSub₀₁ := SecondOrderMemberDefProperties.contains_l hℳ hDef₀₁
    (fun x y hx hy => hTransC₀ x hx y hy)
  have hSub₁C := SecondOrderMemberDefProperties.contains_l hℳ hDef₁C hTransC₁
  have hIntoC (x : type_l hℳ) (hx : mem_l hℳ x C₀) : mem_l hℳ x C :=
    hSub₁C x (hSub₀₁ x hx)
  have hPrefix (b : type_l hℳ) (hb : mem_l hℳ b a) :
      ∃ g, PowerlessHierarchyLightHistory.history_l hℳ X D b W g ∧ mem_l hℳ g C₀ ∧
        ∀ x y, SecondOrderFunctionObjects.value_l hℳ g x y ↔
          mem_l hℳ x b ∧ SecondOrderFunctionObjects.value_l hℳ f x y := by
    have hbA : mem_l hℳ b A := hBudget.domain_ordinal.transitive a
      (hBudget.source a δ hQ) b hb
    have hbOrd : Ordinal b := SetTheory.Structure.IsOrdinal.mem ha hb
    obtain ⟨θ, hQb⟩ := hBudget.total b hbA
    obtain ⟨E, hE⟩ := PowerlessRelativeOrdinalCoverage.level_exists_l hℳ hBase
      (hBudget.output_ordinal b θ hQb)
    obtain ⟨g, hg, hValue⟩ := PowerlessHierarchyLightHistoryRestriction.exists_l hℳ hbOrd
      (fun x hx => ha.transitive b hb x hx) hf
    have hgE : mem_l hℳ g E := hPast b hb θ E g hQb hE hg
    exact ⟨g, hg, hTransC₀ E (hEarlier b hb θ E hQb hE) g hgE, hValue⟩
  rcases PowerlessHierarchyLightHistoryBudgetInduction.cases_l hℳ ha with
    hZero | ⟨b, hSucc⟩ | hLimitA
  · have hfa : f = a := by
      apply SecondOrderQuotient.ext_l hℳ
      intro x
      constructor
      · intro hx
        obtain ⟨i, _, hi, _, _⟩ := hf.1.1 x hx
        exact False.elim (hZero i hi)
      · intro hx
        exact False.elim (hZero x hx)
    exact hIntoC f (hfa.symm ▸ haC₀)
  · have hb : mem_l hℳ b a := (hSucc b).mpr (Or.inr rfl)
    have hbOrd : Ordinal b := SetTheory.Structure.IsOrdinal.mem ha hb
    obtain ⟨g, hg, hgC₀, hValue⟩ := hPrefix b hb
    exact hIntoC f (PowerlessHierarchyLightHistoryRestriction.successor_member_l hℳ
      hBase hLimit hC₀ hWC₀ (hTransC₀ a haC₀ b hb) hgC₀ hbOrd hSucc hf.1 hg.1 hValue)
  · exact PowerlessFunctionHistoryLimitBound.member_l hℳ hD ha hLimitA hf
      (fun x hx y hy => hTransC₀ x hx y hy) hDef₀₁ hDef₁C
      (hTransC₀ W hWC₀ X hXW) hDC₀ hWC₀ haC₀ (fun b hb => by
        obtain ⟨g, hg, hgC₀, _⟩ := hPrefix b hb
        exact ⟨g, hgC₀, hg⟩)

theorem bounded_l (K : source_coding_l hℳ) {B X D W A Q : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hD : functional_l hℳ D) (hXW : mem_l hℳ X W)
    (hBudget : PowerlessHierarchyLightHistoryBudgetInduction.budget_l hℳ B D W A Q) :
    ∀ a, point_l hℳ B X D W Q a := by
  let η : Env 𝒱 [] [.set, .set, .set, .set, .set] :=
    Env.empty |>.pushFree B |>.pushFree X |>.pushFree D |>.pushFree W |>.pushFree Q
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set] :=
    point_m (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there .here)))
      (.fvar (.there .here)) (.fvar .here)
  have hFormula (a : type_l hℳ) : φ.satisfies (η.pushFree a) ↔ point_l hℳ B X D W Q a :=
    point_formula_l hℳ K (η.pushFree a) _ _ _ _ _ _
  have hAll := PowerlessWeakSetInduction.induction_l (SecondOrderWeakSetTheory.models_l hℳ) φ η
    (fun a ih => (hFormula a).mpr (step_l hℳ hBase hD hXW hBudget
      (fun b hb => (hFormula b).mp (ih b hb))))
  exact fun a => (hFormula a).mp (hAll a)

/-- 真正构造预算域的后继，以覆盖整张 A 历史，而非仅其严格前缀。 -/
theorem class_l (K : source_coding_l hℳ) {B X Ω W A f : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (D : PowerlessRelativeClassStructure.type_l hℳ B)
    (hD : functional_l hℳ D.val) (hXW : mem_l hℳ X W)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W) (hA : Ordinal A)
    (hf : PowerlessHierarchyLightHistory.history_l hℳ X D.val A W f) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B f := by
  obtain ⟨A₀, hA₀⟩ := SecondOrderQuotient.surj_l hℳ A
  obtain ⟨A₁, hA₁, hAA₁, _⟩ := SecondOrderOrdinalSuccessor.exists_l hℳ A₀ (hA₀.symm ▸ hA)
  obtain ⟨Q, hBudget⟩ := PowerlessHierarchyLightHistoryBudgetExists.exists_l hℳ K
    hBase D hW hA₁
  obtain ⟨δ, hQ⟩ := hBudget.total A (hA₀ ▸ hAA₁)
  obtain ⟨C, hC⟩ := PowerlessRelativeOrdinalCoverage.level_exists_l hℳ hBase
    (hBudget.output_ordinal A δ hQ)
  exact ⟨δ, C, hC, bounded_l hℳ K hBase hD hXW hBudget A δ C f hQ hC hf⟩

def schema_m : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set] :=
  let B : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar .here
  let X := .fvar (.there .here)
  let D := .fvar (.there (.there .here))
  let Ω := .fvar (.there (.there (.there .here)))
  let W := .fvar (.there (.there (.there (.there .here))))
  let A := .fvar (.there (.there (.there (.there (.there .here)))))
  let f := .fvar (.there (.there (.there (.there (.there (.there .here))))))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B D) <|
      .imp (functional_m D) <| .imp (SecondOrderObjectSyntax.member_m X W) <|
        .imp (PowerlessRelativeHierarchySyntax.level_m B Ω W) <|
          .imp (PowerlessRelativeHierarchySyntax.ordinal_m A) <|
            .imp (PowerlessHierarchyLightHistory.formula_m X D A W f)
              (PowerlessRelativeHierarchySyntax.class_m B f)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, functional_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeHierarchySemantics.ordinal_formula_l,
    PowerlessHierarchyLightHistory.reading_formula_l hℳ, Term.eval]
  exact fun hBase hD hFunctional hXW hW hA hf =>
    class_l hℳ K hBase ⟨η.freeVal (.there (.there .here)), hD⟩ hFunctional hXW hW hA hf

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms class_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFunctionHistoryClass
