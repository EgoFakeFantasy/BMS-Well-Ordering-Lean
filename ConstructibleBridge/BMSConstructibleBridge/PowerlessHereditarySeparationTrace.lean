import BMSConstructibleBridge.PowerlessRelativeClassSelectedImage
import BMSConstructibleBridge.PowerlessHereditaryRelativization
import BMSConstructibleBridge.PowerlessHereditarySubset
import BMSConstructibleBridge.SecondOrderFunctionLaws

/-! # 遗传域完整分离的实数迹归约

对任意实际公式，环境完整分离给出可数包络枚举上的精确索引迹。
若此迹本身属于相对构造类，类内 Δ₀ 选取像和遗传子集封闭即恢复原切片。
最后一个内域成员性前提仍待消去；环境迹存在不代表完整源分离已经成立。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditarySeparationTrace

open Logic FirstOrder SecondOrderObjectSyntax
open SecondOrderQuotient (type_l mem_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_l parameters_pushBound_l parameters_empty_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessHereditaryStructure.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

def cut_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ) (B y : type_l hℳ) : Prop :=
  (PowerlessHereditaryRelativization.formula_m φ).satisfies ((η.pushFree y).pushFree B)

def cut_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (B y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  PowerlessBMSQuotientSubsetImageDerives.at_m
    (PowerlessHereditaryRelativization.formula_m φ) y B

theorem cut_formula_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (B y : Term ℒ Γ Δ .set) :
    (cut_m φ B y).satisfies η ↔ cut_l φ (parameters_l η) (B.eval η) (y.eval η) :=
  PowerlessBMSQuotientSubsetImageDerives.at_formula_l _ η y B

private def matrix_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    Formula ℒ [.set] (.set :: Δ) :=
  (PowerlessHereditaryRelativization.formula_m φ).swapFreeTop.abstractFreeTop

private theorem matrix_formula_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ) (B y : type_l hℳ) :
    (matrix_m φ).satisfies ((η.pushFree B).pushBound y) ↔ cut_l φ η B y := by
  rw [matrix_m, Formula.satisfies_abstractFreeTop]
  change ((PowerlessHereditaryRelativization.formula_m φ).rename
    (Renaming.free VariableRenaming.swapTop)).satisfies ((η.pushFree B).pushFree y) ↔ _
  rw [Formula.satisfies_rename]
  apply Iff.of_eq
  apply congrArg (fun ξ => (PowerlessHereditaryRelativization.formula_m φ).satisfies ξ)
  apply Env.ext
  · intro s v; nomatch v
  · intro s v
    cases v with
    | here => rfl
    | there v => cases v <;> rfl

/-- 自由槽为索引 n、图 f、母集 X、基底 B，以及原公式参数。 -/
def trace_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    Formula ℒ [] (.set :: .set :: .set :: .set :: Δ) :=
  .existsE .set (.conj
    (PowerlessValueBounded.formula_m (.fvar (.there .here)) (.fvar .here) (.bvar .here))
    (.conj (member_m (.bvar .here) (.fvar (.there (.there .here))))
      ((((matrix_m φ).weakenFree SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set)))

theorem trace_formula_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ) (B f X n : type_l hℳ) :
    (trace_m φ).satisfies ((((η.pushFree B).pushFree X).pushFree f).pushFree n) ↔
      ∃ y, SecondOrderFunctionObjects.value_l hℳ f n y ∧ mem_l hℳ y X ∧ cut_l φ η B y := by
  simp only [trace_m, Formula.satisfies, PowerlessValueBounded.formula_l, member_m,
    Arguments.eval, Term.eval]
  change (∃ y, SecondOrderFunctionObjects.value_l hℳ f n y ∧ mem_l hℳ y X ∧
    ((((matrix_m φ).weakenFree SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set).satisfies
      (((((η.pushFree B).pushBound y).pushFree X).pushFree f).pushFree n)) ↔ _
  simp only [Formula.satisfies_weakenFree, matrix_formula_l]

/-- 原 Z₂ 只保证环境迹；该定理没有输出类内成员证书。 -/
theorem trace_exists_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ) (B f X w : type_l hℳ) :
    ∃ S, ∀ n, mem_l hℳ n S ↔ mem_l hℳ n w ∧
      ∃ y, SecondOrderFunctionObjects.value_l hℳ f n y ∧ mem_l hℳ y X ∧ cut_l φ η B y := by
  let ξ : Env (SecondOrderQuotient.structure_l hℳ) [] (.set :: .set :: .set :: Δ) :=
    ((η.pushFree B).pushFree X).pushFree f
  obtain ⟨S, hS⟩ := (SecondOrderSeparationAxiom.schema_l hℳ (trace_m φ) ξ).mp
    (SecondOrderSeparationAxiom.models_l hℳ (trace_m φ) ξ) w
  exact ⟨S, fun n => (hS n).trans (and_congr Iff.rfl (trace_formula_l φ η B f X n))⟩

/-- 真实类内包络与真实类内索引迹恢复遗传域的任意公式切片。 -/
theorem slice_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ) {B X T f w S : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hBody : PowerlessHereditaryClass.body_l hℳ B X T f w)
    (hS : PowerlessRelativeClassCorrespondence.member_l hℳ B S)
    (hTrace : ∀ n, mem_l hℳ n S ↔ mem_l hℳ n w ∧
      ∃ y, SecondOrderFunctionObjects.value_l hℳ f n y ∧ mem_l hℳ y X ∧ cut_l φ η B y) :
    ∃ Y, PowerlessHereditaryClass.member_l hℳ B Y ∧ ∀ y,
      mem_l hℳ y Y ↔ mem_l hℳ y X ∧ cut_l φ η B y := by
  obtain ⟨hT, hf, hXT, hTrans, hω, hMap, hOnto⟩ := hBody
  have hX : PowerlessHereditaryClass.member_l hℳ B X :=
    ⟨T, f, w, hT, hf, hXT, hTrans, hω, hMap, hOnto⟩
  obtain ⟨Y, hY⟩ := PowerlessRelativeClassSelectedImage.exists_l (hBase := hBase)
    ⟨f, hf⟩ ⟨S, hS⟩ ⟨X, PowerlessHereditaryClass.contained_l hℳ hBase hX⟩
  refine ⟨Y.val, PowerlessHereditarySubset.member_l hℳ hBase hX Y.property
    (fun y hy => ((hY y).mp hy).1), fun y => ?_⟩
  constructor
  · intro hy
    obtain ⟨hyX, n, hn, hny⟩ := (hY y).mp hy
    obtain ⟨_, z, hnz, _, hφz⟩ := (hTrace n).mp hn
    have hyz := SecondOrderFunctionLaws.value_unique_l hℳ hMap hny hnz
    exact ⟨hyX, hyz ▸ hφz⟩
  · rintro ⟨hyX, hφy⟩
    obtain ⟨n, hn, hny⟩ := hOnto y (hTrans X hXT y hyX)
    exact (hY y).mpr ⟨hyX, n, (hTrace n).mpr ⟨hn, y, hny, hyX, hφy⟩, hny⟩

#print axioms trace_exists_l
#print axioms slice_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditarySeparationTrace
