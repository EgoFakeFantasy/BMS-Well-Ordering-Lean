import BMSConstructibleBridge.PowerlessHereditarySeparationTraceDerives

/-! # 遗传分离与类内实数迹的精确等价

固定一个实际源公式、参数环境和母集。其遗传域切片存在，当且仅当
任意真实可数包络枚举的精确索引迹属于相对类。反向使用已经验证的
迹恢复模式；正向只需 Δ₀ 逆像。因此实数迹条件既充分又必要，不是
为方便实现而强加更强的源模型条件。此处尚未无条件证明该条件。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditarySeparationCriterion

open Logic FirstOrder StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessHereditaryStructure (type_l structure_l)
open PowerlessHereditarySeparationTrace (cut_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem cut_source_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) (η : Env (structure_l hℳ B hBase) [] Δ) (x : type_l hℳ B) :
    cut_l φ (PowerlessHereditaryRelativization.env_l η) B x.val ↔ φ.satisfies (η.pushFree x) := by
  have hEnv : (PowerlessHereditaryRelativization.env_l η).pushFree
      (sort := SetTheory.SetSort.set) x.val =
      PowerlessHereditaryRelativization.env_l (η.pushFree (sort := SetTheory.SetSort.set) x) := by
    apply Env.ext
    · intro s v; nomatch v
    · intro s v
      cases s
      cases v <;> rfl
  unfold cut_l
  rw [hEnv]
  exact PowerlessHereditaryRelativization.formula_l K φ (η.pushFree x)

def slice_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (η : Env (structure_l hℳ B hBase) [] Δ) (X : type_l hℳ B) : Prop :=
  ∃ Y : type_l hℳ B, ∀ x : type_l hℳ B,
    mem_l hℳ x.val Y.val ↔ mem_l hℳ x.val X.val ∧ φ.satisfies (η.pushFree x)

def traces_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (η : Env (structure_l hℳ B hBase) [] Δ) (X : type_l hℳ B) : Prop :=
  ∀ T f w, PowerlessHereditaryClass.body_l hℳ B X.val T f w →
    ∃ S, PowerlessRelativeClassCorrespondence.member_l hℳ B S ∧ ∀ n,
      mem_l hℳ n S ↔ mem_l hℳ n w ∧ ∃ y,
        SecondOrderFunctionObjects.value_l hℳ f n y ∧ mem_l hℳ y X.val ∧
          cut_l φ (PowerlessHereditaryRelativization.env_l η) B y

/-- 必要性：已有遗传切片沿真实类内枚举的逆像是类内 Δ₀ 分离。 -/
theorem traces_of_slice_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) (η : Env (structure_l hℳ B hBase) [] Δ) (X : type_l hℳ B)
    (hSlice : slice_l φ η X) : traces_l φ η X := by
  obtain ⟨Y, hY⟩ := hSlice
  have hAmbient y : mem_l hℳ y Y.val ↔ mem_l hℳ y X.val ∧
      cut_l φ (PowerlessHereditaryRelativization.env_l η) B y := by
    constructor
    · intro hy
      let y' : type_l hℳ B := ⟨y, PowerlessHereditaryClass.transitive_l hℳ Y.property hy⟩
      obtain ⟨hyX, hφy⟩ := (hY y').mp hy
      exact ⟨hyX, (cut_source_l K φ η y').mpr hφy⟩
    · rintro ⟨hyX, hφy⟩
      let y' : type_l hℳ B := ⟨y, PowerlessHereditaryClass.transitive_l hℳ X.property hyX⟩
      exact (hY y').mpr ⟨hyX, (cut_source_l K φ η y').mp hφy⟩
  intro T f w hBody
  let F : PowerlessRelativeClassStructure.type_l hℳ B := ⟨f, hBody.2.1⟩
  let A : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨Y.val, PowerlessHereditaryClass.contained_l hℳ hBase Y.property⟩
  let O : PowerlessRelativeClassStructure.type_l hℳ B := ⟨w,
    PowerlessHereditaryClass.contained_l hℳ hBase
      (PowerlessHereditaryOmega.member_l hℳ hBase hBody.2.2.2.2.1)⟩
  let ψ : Formula ℒ [] [.set, .set, .set] :=
    membershipLevyBound.boundedExists (.fvar (.there (.there .here)))
      (PowerlessValueBounded.formula_m (.fvar (.there .here)) (.fvar .here) (.bvar .here))
  have hψ : Formula.IsDelta0 membershipLevyBound ψ :=
    .bounded_exists _ (PowerlessValueBounded.delta_l _ _ _)
  let ξ : Env (PowerlessRelativeClassStructure.structure_l hℳ B hBase) [] [.set, .set] :=
    ((Env.empty (M := PowerlessRelativeClassStructure.structure_l hℳ B hBase)).pushFree A).pushFree F
  obtain ⟨S, hS⟩ := PowerlessRelativeClassDeltaSeparation.exists_l hψ ξ O
  have hψRead (n : PowerlessRelativeClassStructure.type_l hℳ B) :
      ψ.satisfies (ξ.pushFree n) ↔ ∃ y : PowerlessRelativeClassStructure.type_l hℳ B,
        mem_l hℳ y.val Y.val ∧
          ThirdOrderSemantics.value_l (ℳ := PowerlessRelativeClassStructure.structure_l hℳ B hBase) F n y := by
    simp only [ψ, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
      membershipLevyBound, Formula.satisfies, PowerlessValueBounded.formula_l, Arguments.eval,
      Term.eval, ξ]
    rfl
  refine ⟨S.val, S.property, fun n => ?_⟩
  constructor
  · intro hnS
    let n' : PowerlessRelativeClassStructure.type_l hℳ B := ⟨n,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase S.property hnS⟩
    obtain ⟨hnw, hψn⟩ := (hS n').mp hnS
    obtain ⟨y, hy, hny⟩ := (hψRead n').mp hψn
    obtain ⟨hyX, hφy⟩ := (hAmbient y.val).mp hy
    exact ⟨hnw, y.val, (PowerlessRelativeClassFunctionAbsolute.value_l F n' y).mp hny, hyX, hφy⟩
  · rintro ⟨hnw, y, hny, hyX, hφy⟩
    have hyY := (hAmbient y).mpr ⟨hyX, hφy⟩
    let n' : PowerlessRelativeClassStructure.type_l hℳ B := ⟨n,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase O.property hnw⟩
    let y' : PowerlessRelativeClassStructure.type_l hℳ B := ⟨y,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase A.property hyY⟩
    exact (hS n').mpr ⟨hnw, (hψRead n').mpr
      ⟨y', hyY, (PowerlessRelativeClassFunctionAbsolute.value_l F n' y').mpr hny⟩⟩

/-- 充分性只消费 X 已有的真实包络，不要求环境中所有实数进入内域。 -/
theorem slice_of_traces_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) (η : Env (structure_l hℳ B hBase) [] Δ) (X : type_l hℳ B)
    (hTraces : traces_l φ η X) : slice_l φ η X := by
  obtain ⟨T, f, w, hBody⟩ := X.property
  obtain ⟨S, hS, hTrace⟩ := hTraces T f w hBody
  obtain ⟨Y, hHY, hY⟩ := PowerlessHereditarySeparationTrace.slice_l φ
    (PowerlessHereditaryRelativization.env_l η) hBase hBody hS hTrace
  refine ⟨⟨Y, hHY⟩, fun x => ?_⟩
  exact (hY x.val).trans (and_congr Iff.rfl (cut_source_l K φ η x))

theorem iff_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) (η : Env (structure_l hℳ B hBase) [] Δ) (X : type_l hℳ B) :
    slice_l φ η X ↔ traces_l φ η X :=
  ⟨traces_of_slice_l K φ η X, slice_of_traces_l K φ η X⟩

/-- 条件覆盖原分离闭句的全部实际参数和母集，而非仅单个切片。 -/
theorem models_iff_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) :
    (SecondOrderSeparationAxiom.sentence_m φ).TrueIn (structure_l hℳ B hBase) ↔
      ∀ (η : Env (structure_l hℳ B hBase) [] Δ) (X : type_l hℳ B), traces_l φ η X := by
  unfold Formula.TrueIn SecondOrderSeparationAxiom.sentence_m
  rw [_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff]
  constructor
  · intro h η X
    exact (iff_l K φ η X).mp ((PowerlessWeakSeparationSyntax.schema_formula_l φ η).mp (h η) X)
  · intro h η
    apply (PowerlessWeakSeparationSyntax.schema_formula_l φ η).mpr
    intro X
    exact (iff_l K φ η X).mpr (h η X)

#print axioms cut_source_l
#print axioms iff_l
#print axioms models_iff_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditarySeparationCriterion
