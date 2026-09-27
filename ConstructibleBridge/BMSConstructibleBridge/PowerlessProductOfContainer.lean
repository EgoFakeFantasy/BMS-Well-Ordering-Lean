import BMSConstructibleBridge.PowerlessBasic
import BMSConstructibleBridge.PowerlessBoundedWitness
import BMSConstructibleBridge.PowerlessProduct

/-!
# 行集有实际容器时的笛卡尔积

`PowerlessProduct.exists_l` 的依赖里共有两次 `PowerlessComprehension.image_l`（各经
`collection_l` 消费 Collection）：一次在 `family_l` 收集行集族（承重），一次在反向分支
用 `row_exists_l` 取单个已知坐标的行集（存在性引用）；尾段 `PowerlessBasic.union_l`
直接读取并公理。本模块把两列义务分别改写成假设：`hF` 给出族收集所需的容器，
`hRow` 直接给出逐坐标落在容器内的实际行集。`family_of_container_l` 只消费分离；
`exists_l` 在此基础上只再加并公理，不再调用 `row_exists_l`。
它不声称这些容器或行集在无幂集核心内总存在，也不替代原 `exists_l`。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessProductOfContainer

open Logic FirstOrder ThirdOrderSemantics PowerlessProduct

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

/-- 行集容器给出时逐行收集族：把 `family_l` 的 `image_l` 换成容器假设。 -/
theorem family_of_container_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (a b F : carrier_l ℳ)
    (hF : ∀ x, member_l ℳ x a → ∀ d, row_l x b d → member_l ℳ d F) :
    ∃ c, ∀ d, member_l ℳ d c ↔ ∃ x, member_l ℳ x a ∧ row_l x b d := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 1 :=
    { bound := fun _ => b, free := fun _ => a }
  let φ : Formula ℒ [] [.set, .set, .set] :=
    row_m (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)
  have h : ∀ x d, φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree d) ↔
      row_l x b d := by
    intro x d
    dsimp only [φ]
    rw [row_formula_l]
    rfl
  obtain ⟨c, hc⟩ := PowerlessBoundedWitness.image_of_container_l hℳ φ η a F
    (fun x hx d hd => hF x hx d ((h x d).mp hd))
  exact ⟨c, fun d => (hc d).trans (exists_congr fun x => and_congr Iff.rfl (h x d))⟩

/-- 行集容器与实际行集存在性给出时的笛卡尔积，结论与 `PowerlessProduct.exists_l` 同形。
`hRow` 将原 `row_exists_l` 那一列收集义务显式假设化；行集本身含全部序对。 -/
theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (a b F : carrier_l ℳ)
    (hF : ∀ x, member_l ℳ x a → ∀ d, row_l x b d → member_l ℳ d F)
    (hRow : ∀ x, member_l ℳ x a → ∃ d, row_l x b d ∧ member_l ℳ d F) :
    ∃ c, product_l a b c := by
  obtain ⟨d, hd⟩ := family_of_container_l hℳ a b F hF
  obtain ⟨c, hc⟩ := PowerlessBasic.union_l hℳ d
  refine ⟨c, fun p => (hc p).trans ?_⟩
  constructor
  · rintro ⟨e, he, hp⟩
    obtain ⟨x, hx, h₀⟩ := (hd e).mp he
    obtain ⟨y, hy, h₁⟩ := (h₀ p).mp hp
    exact ⟨x, hx, y, hy, h₁⟩
  · rintro ⟨x, hx, y, hy, h₀⟩
    obtain ⟨e, he, _⟩ := hRow x hx
    exact ⟨e, (hd e).mpr ⟨x, hx, he⟩, (he p).mpr ⟨y, hy, h₀⟩⟩

#print axioms family_of_container_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessProductOfContainer
