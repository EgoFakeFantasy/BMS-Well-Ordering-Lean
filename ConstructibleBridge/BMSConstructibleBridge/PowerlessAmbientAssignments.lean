import BMSConstructibleBridge.PowerlessAssignmentDomain

/-!
# 不以当前域为参数的有限赋值公式

值域由公式内部量化；变量槽位额外要求属于同一实际函数的定义域。
这不是在源语言中命名整个当前域或它的有限赋值全集。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessAmbientAssignments

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def finite_l (ω f : carrier_l ℳ) : Prop :=
  ∃ n A, member_l ℳ n ω ∧ map_l f n A

def slot_l (ω f i : carrier_l ℳ) : Prop :=
  ∃ n A, member_l ℳ n ω ∧ map_l f n A ∧ member_l ℳ i n

def finite_m {Γ Δ : SortContext ℒ} (ω f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let q (s : Term ℒ Γ Δ .set) := (s.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .existsE .set <| .existsE .set <|
    .conj (member_m (.bvar (.there .here)) (q ω))
      (map_m (q f) (.bvar (.there .here)) (.bvar .here))

def slot_m {Γ Δ : SortContext ℒ} (ω f i : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let q (s : Term ℒ Γ Δ .set) := (s.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .existsE .set <| .existsE .set <|
    .conj (member_m (.bvar (.there .here)) (q ω))
      (.conj (map_m (q f) (.bvar (.there .here)) (.bvar .here))
        (member_m (q i) (.bvar (.there .here))))

theorem finite_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω f : Term ℒ Γ Δ .set) :
    (finite_m ω f).satisfies η ↔ finite_l (ω.eval η) (f.eval η) := by
  simp only [finite_m, finite_l, member_m, Formula.satisfies, Arguments.eval, map_formula_l, Term.eval_weakenBound]
  rfl

theorem slot_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω f i : Term ℒ Γ Δ .set) :
    (slot_m ω f i).satisfies η ↔ slot_l (ω.eval η) (f.eval η) (i.eval η) := by
  simp only [slot_m, slot_l, member_m, Formula.satisfies, Arguments.eval, map_formula_l, Term.eval_weakenBound]
  rfl

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessAmbientAssignments
