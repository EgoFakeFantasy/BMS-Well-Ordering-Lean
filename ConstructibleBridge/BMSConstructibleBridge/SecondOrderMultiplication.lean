import BMSConstructibleBridge.SecondOrderNumbers

/-!
# 任意模型中的乘法运算规律

每次归纳均由当前二阶算术模型中的具体纯公式承载，不将外部任意性质用于归纳。
这组规律针对整个模型数域，为非标准输入的多项式配对分析提供代数基础。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMultiplication

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel SecondOrderNumbers

set_option autoImplicit false

universe u

private def zero {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .zero .nil

private def succ {Γ Δ : SortContext signature_m} (s : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num := Term.app (σ := signature_m) .succ (.cons s .nil)

private def add {Γ Δ : SortContext signature_m} (s t : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num := Term.app (σ := signature_m) .add (.cons s (.cons t .nil))

private def mul {Γ Δ : SortContext signature_m} (s t : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num := Term.app (σ := signature_m) .mul (.cons s (.cons t .nil))

private def v₀ {Δ : SortContext signature_m} : Term signature_m [] (.num :: Δ) .num :=
  .fvar .here

private def v₁ {Δ : SortContext signature_m} : Term signature_m [] (.num :: .num :: Δ) .num :=
  .fvar (.there .here)

private def v₂ {Δ : SortContext signature_m} :
    Term signature_m [] (.num :: .num :: .num :: Δ) .num := .fvar (.there (.there .here))

theorem zero_mul_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (n : num_l ℳ) : mul_l (zero_l ℳ) n = zero_l ℳ := by
  let φ : Formula signature_m [] [.num] := .equal (mul zero v₀) zero
  apply induct_l hℳ φ rfl Env.empty
    (fun n => mul_l (zero_l ℳ) n = zero_l ℳ) (fun _ => Iff.rfl) ?_ ?_ n
  · exact mul_zero_l hℳ _
  · intro n h
    rw [mul_succ_l hℳ, add_zero_l hℳ, h]

theorem succ_mul_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (m n : num_l ℳ) :
    mul_l (succ_l m) n = add_l (mul_l m n) n := by
  let φ : Formula signature_m [] [.num, .num] := .equal (mul (succ v₁) v₀) (add (mul v₁ v₀) v₀)
  apply induct_l hℳ φ rfl ((Env.empty (M := ℳ)).pushFree m)
    (fun n => mul_l (succ_l m) n = add_l (mul_l m n) n) (fun _ => Iff.rfl) ?_ ?_ n
  · rw [mul_zero_l hℳ, mul_zero_l hℳ, add_zero_l hℳ]
  · intro n h
    rw [mul_succ_l hℳ, mul_succ_l hℳ, h, add_succ_l hℳ, add_succ_l hℳ]
    apply congrArg succ_l
    rw [add_assoc_l hℳ, add_comm_l hℳ n m, ← add_assoc_l hℳ]

theorem mul_comm_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (m n : num_l ℳ) : mul_l m n = mul_l n m := by
  let φ : Formula signature_m [] [.num, .num] := .equal (mul v₁ v₀) (mul v₀ v₁)
  apply induct_l hℳ φ rfl ((Env.empty (M := ℳ)).pushFree m)
    (fun n => mul_l m n = mul_l n m) (fun _ => Iff.rfl) ?_ ?_ n
  · rw [mul_zero_l hℳ, zero_mul_l hℳ]
  · intro n h
    rw [mul_succ_l hℳ, succ_mul_l hℳ, h]

theorem mul_add_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (m n p : num_l ℳ) :
    mul_l m (add_l n p) = add_l (mul_l m n) (mul_l m p) := by
  let φ : Formula signature_m [] [.num, .num, .num] :=
    .equal (mul v₂ (add v₁ v₀)) (add (mul v₂ v₁) (mul v₂ v₀))
  apply induct_l hℳ φ rfl (((Env.empty (M := ℳ)).pushFree m).pushFree n)
    (fun p => mul_l m (add_l n p) = add_l (mul_l m n) (mul_l m p)) (fun _ => Iff.rfl) ?_ ?_ p
  · rw [add_zero_l hℳ, mul_zero_l hℳ, add_zero_l hℳ]
  · intro p h
    rw [add_succ_l hℳ, mul_succ_l hℳ, mul_succ_l hℳ, h, add_assoc_l hℳ]

theorem add_mul_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (m n p : num_l ℳ) :
    mul_l (add_l m n) p = add_l (mul_l m p) (mul_l n p) := by
  rw [mul_comm_l hℳ (add_l m n) p, mul_add_l hℳ, mul_comm_l hℳ p m, mul_comm_l hℳ p n]

theorem mul_assoc_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (m n p : num_l ℳ) :
    mul_l (mul_l m n) p = mul_l m (mul_l n p) := by
  let φ : Formula signature_m [] [.num, .num, .num] :=
    .equal (mul (mul v₂ v₁) v₀) (mul v₂ (mul v₁ v₀))
  apply induct_l hℳ φ rfl (((Env.empty (M := ℳ)).pushFree m).pushFree n)
    (fun p => mul_l (mul_l m n) p = mul_l m (mul_l n p)) (fun _ => Iff.rfl) ?_ ?_ p
  · rw [mul_zero_l hℳ, mul_zero_l hℳ, mul_zero_l hℳ]
  · intro p h
    rw [mul_succ_l hℳ, mul_succ_l hℳ, mul_add_l hℳ, h]

theorem mul_one_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (m : num_l ℳ) : mul_l m (succ_l (zero_l ℳ)) = m := by
  rw [mul_succ_l hℳ, mul_zero_l hℳ, zero_add_l hℳ]

theorem one_mul_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (m : num_l ℳ) : mul_l (succ_l (zero_l ℳ)) m = m := by
  rw [mul_comm_l hℳ, mul_one_l hℳ]

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMultiplication
