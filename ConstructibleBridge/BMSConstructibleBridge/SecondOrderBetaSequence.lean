import BMSConstructibleBridge.SecondOrderDivision
import BMSConstructibleBridge.SecondOrderFiniteRange
import BMSConstructibleBridge.PrimitiveFormulas
import BMSConstructibleBridge.PrimitiveHistory

/-!
# 任意 Z₂ 模型内的 β 有限序列存在性

本模块在任意满足 `SecondOrderArithmetic.theory_m` 的模型内，给出原
`PrimitiveFormulas.beta_m` 所编码的模数族 `m_i = 1 + (i+1)c` 的有限余数编码。
所有索引、见证、归纳变量都是模型数（`num_l ℳ`），不使用宿主 `Nat.rec`，
也不把非标准长度当成 Lean 的有限类型。

主要步骤对应路线：
1. 构造同时被 `1..n` 整除且大于输出界的内部 `c`；
2. 纯多项式恒等式 `m_i * u = 1 + v * m_j`（`i < j`）；
3. 固定 `j` 时有界归纳，得到"同时保持全部旧余数、在新模数下可逆"的增量；
4. 归纳构造整体的 `b`，并把每个取值读成 `b` 在模数 `m_i` 下的规范余数。

结论分两条接口给出：

* `beta_sequence_l`：`H(i,a) → beta_rel_l b c i a`（原有正向接口，签名不变）；
* `beta_sequence_iff_l`：同一对 `b c` 上 `beta_rel_l b c i a ↔ H(i,a)`，
  反向由"同一被除数在同一正模数下的规范余数唯一"（`beta_remainder_unique_l`，
  直接消费 `SecondOrderDivision.eq_l`）把任意 β 值还原为 `H` 的唯一取值。

语法层有两个独立出口，二者都实际展开模板并证出等价，不靠注释声称相同：

* `beta_rel_syntax_l`：固定四个自由数参数的 `SecondOrderSyntax.beta_m`；
* `beta_primitive_syntax_l`：任意 `Γ Δ`、任意环境 `η`、任意数项上的
  `PrimitiveFormulas.beta_m`（该模板内部把四个项用两次提升跨过两个数量词）。

边界：`n = 0` 时截段为空，归纳基例给出 `b = 0`、`M = 1`，`beta_sequence_iff_l`
的全称前提与结论都空真；后继情形由归纳步在 `j` 上追加新模数 `m_j` 处理。

结论只声明"给定有限函数输入时存在 β 编码"，不称为 BM4 良序性证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderBetaSequence

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderNumbers
open SecondOrderDivision SecondOrderFiniteRange

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-! ## 内部项记法（与 `PrimitiveFormulas` 的私有记法同形） -/

/-- 模型语法中的零项。 -/
abbrev zero_m {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .zero .nil

/-- 模型语法中的后继项。 -/
abbrev succ_m {Γ Δ : SortContext signature_m} (t : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .succ (.cons t .nil)

/-- 模型语法中的加法项。 -/
abbrev add_m {Γ Δ : SortContext signature_m} (s t : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .add (.cons s (.cons t .nil))

/-- 模型语法中的乘法项。 -/
abbrev mul_m {Γ Δ : SortContext signature_m} (s t : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .mul (.cons s (.cons t .nil))

/-- 内部整除关系，由模型自身的乘法给出，不调用宿主 `Nat.dvd`。 -/
def dvd_l (d m : num_l ℳ) : Prop := ∃ k : num_l ℳ, mul_l d k = m

theorem one_dvd_l (hℳ : Theory.Models ℳ theory_m) (m : num_l ℳ) :
    dvd_l (succ_l (zero_l ℳ)) m := by
  letI := semiring_l hℳ
  exact ⟨m, one_mul m⟩

/-! ## 第 1 步：构造整除 `1..n` 且大于输出界的内部 `c` -/

/-- 第 1 步：对任意内部 `r`，存在正的内部 `c`，使得每个 `0 < d ≤ r` 都整除 `c`。
归纳变量与被除见证都是模型数，不构造宿主阶乘。 -/
theorem common_multiple_l (hℳ : Theory.Models ℳ theory_m) (r : num_l ℳ) :
    ∃ c, SecondOrderOrder.lt_l (zero_l ℳ) c ∧
      ∀ d, SecondOrderOrder.lt_l (zero_l ℳ) d →
        SecondOrderOrder.lt_l d (succ_l r) → dvd_l d c := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  let φ : Formula signature_m [] [.num] :=
    .existsE .num (.conj
      (PrimitiveFormulas.lt_m zero_m (.bvar .here))
      (.forallE .num (.imp
        (PrimitiveFormulas.lt_m zero_m (.bvar .here))
        (.imp
          (PrimitiveFormulas.lt_m (.bvar .here) (succ_m (.fvar .here)))
          (.existsE .num (.equal
            (mul_m (.bvar (.there .here)) (.bvar .here))
            (.bvar (.there (.there .here)))))))))
  have hφ : language_m φ = true := pure_language_m _ rfl
  have hP : ∀ r, Formula.satisfies (Env.pushFree (M := ℳ) (Env.empty (M := ℳ)) r) φ ↔
      ∃ c, zero_l ℳ < c ∧ ∀ d, zero_l ℳ < d → d < succ_l r → dvd_l d c := by
    intro r
    simp only [φ, Formula.satisfies, SecondOrderOrder.formula_l, SecondOrderOrder.lt_l,
      zero_m, succ_m, Term.eval, Arguments.eval, zero_l, succ_l, mul_l, dvd_l,
      Env.pushBound, Env.pushFree, Assignment.push]
    exact Iff.rfl
  refine induct_l hℳ φ hφ Env.empty
    (fun r => ∃ c, zero_l ℳ < c ∧
      ∀ d, zero_l ℳ < d → d < succ_l r → dvd_l d c) hP ?_ ?_ r
  · -- 基例：`r = 0`，取 `c = 1`；前提 `d < 1` 与 `0 < d` 矛盾。
    refine ⟨succ_l (zero_l ℳ), SecondOrderOrder.zero_succ_l hℳ (zero_l ℳ), ?_⟩
    intro d hd hd1
    exfalso
    -- `hd : 0 < d` 蕴含 `succ_l 0 ≤ d`（`0 < d ↔ 0 + 1 ≤ d`，且 `succ_l 0 = 0 + 1`）。
    have hle : succ_l (zero_l ℳ) ≤ d := by
      rw [succ_eq_l hℳ]
      exact (lt_iff_add_one_le_l hℳ (zero_l ℳ) d).mp hd
    exact absurd hd1 (not_lt.mpr hle)
  · -- 后继：目标为 `∀d, 0<d → d < succ_l (succ_l r) → d | c * succ_l r`。
    rintro r ⟨c, hc, hcd⟩
    have hr : zero_l ℳ < succ_l r := SecondOrderOrder.zero_succ_l hℳ r
    refine ⟨mul_l c (succ_l r), mul_pos hc hr, ?_⟩
    intro d hd hdr
    -- `hdr : d < succ_l (succ_l r)`。两层后继各展开一层，得 `d < r + 1 + 1`。
    have h3 : d < r + 1 + 1 := by
      have h := hdr
      rw [succ_eq_l hℳ, succ_eq_l hℳ] at h
      exact h
    -- `d < r + 1 + 1` 即 `d + 1 ≤ (r + 1) + 1`，两边消去一层 `+1` 得 `d ≤ r + 1 = succ_l r`。
    have hle : d ≤ succ_l r := by
      have h4 : d + 1 ≤ (r + 1) + 1 := (lt_iff_add_one_le_l hℳ d (r + 1 + 1)).mp h3
      rw [succ_eq_l hℳ]
      exact add_le_add_iff_right 1 |>.mp h4
    rcases eq_or_lt_of_le hle with hdr | hdr
    · -- `d = succ_l r`：直接被新因子 `succ_l r` 整除。
      refine ⟨c, ?_⟩
      rw [hdr]
      exact mul_comm _ _
    · -- `d < succ_l r`：由归纳假设 `d | c`，故 `d | c * succ_l r`。
      obtain ⟨k, hk⟩ := hcd d hd hdr
      refine ⟨mul_l k (succ_l r), ?_⟩
      rw [← hk]
      exact (mul_assoc _ _ _).symm

/-! ## 第 2 步：特殊模数的显式多项式恒等式

模数族 `modulus_l c i = 1 + (i+1) * c`。对 `i < j`，写成 `j = i + d`（`d > 0`）并取
`e` 使 `c = d * e`，则纯多项式恒等式

  `A * m_i + 1 = D * m_j`

成立，其中 `p := i+1`、`q := j+1`、`A := q * q * e`、`D := p * q * e + 1`。
展开只用 `q = p + d` 与 `c = d * e`，不依赖 gcd 或 CRT。
-/

/-- 模数族 `m i c = 1 + (i+1) * c`。 -/
def modulus_l (c : num_l ℳ) (i : num_l ℳ) : num_l ℳ :=
  add_l (succ_l (zero_l ℳ)) (mul_l (succ_l i) c)

/-- 实例加法就是 `add_l`：`add_l` 定义为 `ℳ.funcInterp .add`，
`HAdd.hAdd` 实例也直接指向它，故两侧可判定相等。
注意这只对"定义相等"成立：`simp` 不会展开实例算子，
跨记法改写仍需本定理或 `change`。 -/
theorem add_l_eq (hℳ : Theory.Models ℳ theory_m) (a b : num_l ℳ) :
    letI := semiring_l hℳ
    add_l a b = a + b := rfl

/-- 实例乘法就是 `mul_l`。同理只在定义相等层面使用。 -/
theorem mul_l_eq (hℳ : Theory.Models ℳ theory_m) (a b : num_l ℳ) :
    letI := semiring_l hℳ
    mul_l a b = a * b := rfl

/-- 第 2 步核心恒等式（无减法形式）：`A * m_i + 1 = D * m_j`。
其中 `p = i+1`、`q = j+1`、`A = q*q*e`、`D = p*q*e+1`，假定 `j = i + d` 且 `c = d*e`。
结论用实例记法书写；证明先用 `add_l_eq`／`mul_l_eq` 把两个假设改写为实例记法，
再由 `succ_eq_l` 展开后继并交给 `ring`。 -/
theorem modulus_core_l (hℳ : Theory.Models ℳ theory_m) (c i j d e : num_l ℳ)
    (hj : add_l i d = j) (hc : mul_l d e = c) :
    letI := semiring_l hℳ
    (succ_l j * succ_l j * e) * (1 + (i + 1) * c) + 1
      = ((i + 1) * succ_l j * e + 1) * (1 + (j + 1) * c) := by
  letI := semiring_l hℳ
  rw [add_l_eq hℳ] at hj
  rw [mul_l_eq hℳ] at hc
  subst hj
  simp only [succ_eq_l hℳ] at *
  have hce : c = d * e := hc.symm
  subst hce
  ring

/-! ## 第 3 步：新模数下的可逆增量

`inv_l X m` 表示 `X` 在模 `m` 下有**正逆**：`X * u = 1 + k * m`。
只使用加乘与等式，不出现减法；所有见证都是模型数。
-/

/-- 模 `m` 下的可逆性：存在 `u`、`k` 使 `X * u = 1 + k * m`。 -/
def inv_l (X m : num_l ℳ) : Prop :=
  ∃ u k : num_l ℳ, mul_l X u = add_l (succ_l (zero_l ℳ)) (mul_l k m)

/-- 后继的纯 `add_l` 展开：`n + 1 = succ_l n`。
与 `succ_eq_l` 同义，但两侧都固定在 `add_l` 记法，不经过实例记法，
因此可以被 `rw` 直接用于 `add_l`/`succ_l` 写成的目标。 -/
theorem succ_add_one_l (hℳ : Theory.Models ℳ theory_m) (n : num_l ℳ) :
    add_l n (succ_l (zero_l ℳ)) = succ_l n := by
  rw [add_comm_l hℳ n (succ_l (zero_l ℳ)), succ_add_l hℳ, zero_add_l hℳ]

/-- 单位元在任意模数下可逆。 -/
theorem inv_one_l (hℳ : Theory.Models ℳ theory_m) (m : num_l ℳ) :
    inv_l (succ_l (zero_l ℳ)) m := by
  letI := semiring_l hℳ
  refine ⟨succ_l (zero_l ℳ), zero_l ℳ, ?_⟩
  change (1 : num_l ℳ) * 1 = 1 + 0 * m
  simp

/-- 两个可逆因子的乘积仍可逆：逆元相乘，系数按 `(1+km)(1+lm)` 展开。 -/
theorem inv_mul_l (hℳ : Theory.Models ℳ theory_m) {X Y m : num_l ℳ}
    (hX : inv_l X m) (hY : inv_l Y m) : inv_l (mul_l X Y) m := by
  letI := semiring_l hℳ
  obtain ⟨u, k, hu⟩ := hX
  obtain ⟨v, l, hv⟩ := hY
  change X * u = 1 + k * m at hu
  change Y * v = 1 + l * m at hv
  refine ⟨mul_l u v, add_l (add_l k l) (mul_l (mul_l k l) m), ?_⟩
  change (X * Y) * (u * v) = 1 + (k + l + k * l * m) * m
  calc
    (X * Y) * (u * v) = (X * u) * (Y * v) := by ring
    _ = (1 + k * m) * (1 + l * m) := by rw [hu, hv]
    _ = 1 + (k + l + k * l * m) * m := by ring

/-- 无减法贝祖等式 `A * X + 1 = D * m` 在 `m ≥ 2`、`D ≥ 1` 时给出 `X` 的正逆。
取 `s = m-1` 与 `k' = D*m-(D+1)`，全部差值都由 `le_iff_l` 的见证给出。 -/
theorem inv_of_bezout_l (hℳ : Theory.Models ℳ theory_m) {X A D m : num_l ℳ}
    (h : add_l (mul_l A X) (succ_l (zero_l ℳ)) = mul_l D m)
    (hD : SecondOrderOrder.lt_l (zero_l ℳ) D)
    (hm : SecondOrderOrder.lt_l (succ_l (zero_l ℳ)) m) : inv_l X m := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  change A * X + 1 = D * m at h
  have hm₂ : (1 : num_l ℳ) + 1 ≤ m :=
    (lt_iff_add_one_le_l hℳ (succ_l (zero_l ℳ)) m).mp hm
  have h11 : (1 : num_l ℳ) ≤ 1 + 1 :=
    (le_iff_l hℳ (1 : num_l ℳ) (1 + 1)).mpr ⟨1, rfl⟩
  have h1m : (1 : num_l ℳ) ≤ m := le_trans h11 hm₂
  obtain ⟨s, hs⟩ := (le_iff_l hℳ (1 : num_l ℳ) m).mp h1m
  change 1 + s = m at hs
  -- `hD : 0 < D` 直接给出 `D = succ_l k`，于是 `1 + k = D` 是 `1 ≤ D` 的见证。
  obtain ⟨k₀, hk₀⟩ := hD
  have hD₁ : (1 : num_l ℳ) ≤ D :=
    (le_iff_l hℳ (1 : num_l ℳ) D).mpr ⟨k₀, by
      change add_l (succ_l (zero_l ℳ)) k₀ = D
      calc
        add_l (succ_l (zero_l ℳ)) k₀ = add_l k₀ (succ_l (zero_l ℳ)) :=
            add_comm_l hℳ (succ_l (zero_l ℳ)) k₀
        _ = succ_l k₀ := succ_add_one_l hℳ k₀
        _ = add_l (zero_l ℳ) (succ_l k₀) := (zero_add_l hℳ (succ_l k₀)).symm
        _ = D := hk₀⟩
  have hle : D + 1 ≤ D * m := by
    calc
      D + 1 ≤ D + D := by simpa [add_comm] using (add_le_add_left hD₁ D)
      _ = D * (1 + 1) := by ring
      _ ≤ D * m := mul_le_mul_of_nonneg_left hm₂ (zero_le_l hℳ D)
  obtain ⟨kk, hkk⟩ := (le_iff_l hℳ (D + 1) (D * m)).mp hle
  change (D + 1) + kk = D * m at hkk
  have hXA : X * A = D + kk := by
    have h₁ : X * A + 1 = (D + kk) + 1 := by
      calc
        X * A + 1 = A * X + 1 := by ring
        _ = D * m := h
        _ = (D + kk) + 1 := by
          rw [← hkk]
          ring
    have h₂ : (1 : num_l ℳ) + X * A = 1 + (D + kk) := by
      simpa [add_comm] using h₁
    exact (add_cancel_l hℳ (succ_l (zero_l ℳ)) (mul_l X A) (add_l D kk)).mp h₂
  have hDs : (1 : num_l ℳ) + kk = D * s := by
    have h₃ : D + (1 + kk) = D + D * s := by
      calc
        D + (1 + kk) = (D + 1) + kk := by ring
        _ = D * m := hkk
        _ = D * (1 + s) := by rw [← hs]
        _ = D + D * s := by ring
    exact (add_cancel_l hℳ D (add_l (succ_l (zero_l ℳ)) kk) (mul_l D s)).mp h₃
  refine ⟨mul_l A s, kk, ?_⟩
  change X * (A * s) = 1 + kk * m
  calc
    X * (A * s) = (X * A) * s := by ring
    _ = (D + kk) * s := by rw [hXA]
    _ = D * s + kk * s := by ring
    _ = (1 + kk) + kk * s := by rw [← hDs]
    _ = 1 + kk * (1 + s) := by ring
    _ = 1 + kk * m := by rw [hs]

/-- 模数族在后续模数下的可逆性：`i < j < n` 时 `m_i` 在模 `m_j` 下有正逆。
来自第 1 步的整除性与第 2 步的纯多项式恒等式，不调用 gcd 或中国剩余定理。 -/
theorem modulus_inv_l (hℳ : Theory.Models ℳ theory_m) (n c : num_l ℳ)
    (hc : ∀ d, SecondOrderOrder.lt_l (zero_l ℳ) d →
      SecondOrderOrder.lt_l d (succ_l n) → dvd_l d c)
    (hc₀ : SecondOrderOrder.lt_l (zero_l ℳ) c)
    {i j : num_l ℳ} (hij : SecondOrderOrder.lt_l i j)
    (hjn : SecondOrderOrder.lt_l j n) : inv_l (modulus_l c i) (modulus_l c j) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  obtain ⟨d, hd⟩ := (le_iff_l hℳ i j).mp (le_of_lt hij)
  have hdpos : SecondOrderOrder.lt_l (zero_l ℳ) d := by
    rcases eq_or_lt_of_le (zero_le_l hℳ d) with hd₀ | hd₀
    · subst d
      exfalso
      have hieq : i = j := by simpa [add_zero_l hℳ] using hd
      exact (SecondOrderOrder.irrefl_l hℳ j) (hieq ▸ hij)
    · exact hd₀
  have hdn : SecondOrderOrder.lt_l d (succ_l n) := by
    have hdlej : d ≤ j := (le_iff_l hℳ d j).mpr ⟨i, by simpa [add_comm] using hd⟩
    exact lt_of_le_of_lt hdlej
      (SecondOrderOrder.trans_l hℳ hjn ((SecondOrderNaturalGraph.lt_succ_l hℳ n n).mpr le_rfl))
  obtain ⟨e, he⟩ := hc d hdpos hdn
  have hcore := modulus_core_l hℳ c i j d e hd he
  -- 把两个模数展开成 `1 + (i+1)*c` 的形状；`succ_l` 用纯 `add_l` 引理展开。
  have hmi : modulus_l c i =
      add_l (succ_l (zero_l ℳ)) (mul_l (add_l i (succ_l (zero_l ℳ))) c) := by
    change add_l (succ_l (zero_l ℳ)) (mul_l (succ_l i) c) =
      add_l (succ_l (zero_l ℳ)) (mul_l (add_l i (succ_l (zero_l ℳ))) c)
    rw [(succ_add_one_l hℳ i).symm]
  have hmj : modulus_l c j =
      add_l (succ_l (zero_l ℳ)) (mul_l (add_l j (succ_l (zero_l ℳ))) c) := by
    change add_l (succ_l (zero_l ℳ)) (mul_l (succ_l j) c) =
      add_l (succ_l (zero_l ℳ)) (mul_l (add_l j (succ_l (zero_l ℳ))) c)
    rw [(succ_add_one_l hℳ j).symm]
  have hcore' : add_l (mul_l (mul_l (mul_l (succ_l j) (succ_l j)) e) (modulus_l c i))
      (succ_l (zero_l ℳ)) =
      mul_l (add_l (mul_l (mul_l (add_l i (succ_l (zero_l ℳ))) (succ_l j)) e)
        (succ_l (zero_l ℳ))) (modulus_l c j) := by
    rw [hmi, hmj]
    change (succ_l j * succ_l j * e) * (1 + (i + 1) * c) + 1 =
      ((i + 1) * succ_l j * e + 1) * (1 + (j + 1) * c)
    exact hcore
  have hpos : SecondOrderOrder.lt_l (zero_l ℳ) (mul_l (succ_l j) c) := by
    obtain ⟨l, hl⟩ := hc₀
    have hc_eq : c = succ_l l := by simpa [zero_add_l hℳ] using hl.symm
    refine ⟨add_l (mul_l (succ_l j) l) j, ?_⟩
    calc
      add_l (zero_l ℳ) (succ_l (add_l (mul_l (succ_l j) l) j)) =
          succ_l (add_l (mul_l (succ_l j) l) j) := zero_add_l hℳ _
      _ = add_l (mul_l (succ_l j) l) (succ_l j) :=
          (add_succ_l hℳ (mul_l (succ_l j) l) j).symm
      _ = mul_l (succ_l j) (succ_l l) := (mul_succ_l hℳ (succ_l j) l).symm
      _ = mul_l (succ_l j) c := by rw [← hc_eq]
  have hmgt : SecondOrderOrder.lt_l (succ_l (zero_l ℳ)) (modulus_l c j) := by
    obtain ⟨k, hk⟩ := hpos
    refine ⟨k, ?_⟩
    have hk' : succ_l k = mul_l (succ_l j) c := by simpa [zero_add_l hℳ] using hk
    change add_l (succ_l (zero_l ℳ)) (succ_l k) =
      add_l (succ_l (zero_l ℳ)) (mul_l (succ_l j) c)
    rw [hk']
  exact inv_of_bezout_l hℳ hcore'
    (by
      refine ⟨mul_l (mul_l (add_l i (succ_l (zero_l ℳ))) (succ_l j)) e, ?_⟩
      rw [zero_add_l hℳ]
      exact (succ_add_one_l hℳ
        (mul_l (mul_l (add_l i (succ_l (zero_l ℳ))) (succ_l j)) e)).symm)
    hmgt

/-! ## 第 4 步：归纳构造整体的 `b`

归纳不变量同时携带三件事：

* (A) 累积因子 `M` 被所有旧模数 `m_i`（`i < j`）整除，因此给 `b` 加上 `M` 的倍数
  不会改变任何已经定好的余数；
* (B) `M` 在所有"尚未使用"的模数 `m_l`（`j ≤ l < n`）下可逆，于是每步都能解出
  新模数下的增量系数；
* (C) `b` 在 `i < j` 上已经读到 `F` 的取值。

增量 `M * t` 的系数 `t` 只由加法给出：`b ≤ a_j` 时取 `t = u * (a_j - b)` 的加法见证，
`a_j ≤ b` 时取 `t = u * (b - a_j) * (m_j - 1)` 的两个加法见证之积，全程不出现减法。
-/

/-! 这四个模板是归纳不变量的语法层副本（`_m`）。它们与上面的宿主层谓词（`_l`）
的对应关系不是"逐字相同"的声明，而是由 `beta_sequence_l` 里的 `hP` 用一次
`simp`＋`rfl` 实际核对出来的：展开 `Formula.satisfies` 与 `Term.eval` 后，
两侧表达式判定相等。 -/

/-- 模数项 `1 + (i+1) * c`；求值后等于宿主层的 `modulus_l`。 -/
abbrev modulus_m {Γ Δ : SortContext signature_m} (c i : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num :=
  add_m (succ_m zero_m) (mul_m (succ_m i) c)

/-- 整除模板 `∃ q, d * q = m`；求值后等于 `dvd_l`。 -/
def dvd_m {Γ Δ : SortContext signature_m} (d m : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ :=
  .existsE .num (.equal
    (mul_m (d.weakenBound sort_m.num) (.bvar .here))
    (m.weakenBound sort_m.num))

/-- 可逆模板 `∃ u k, X * u = 1 + k * m`；求值后等于 `inv_l`。 -/
def inv_m {Γ Δ : SortContext signature_m} (X m : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ :=
  .existsE .num (.existsE .num (.equal
    (mul_m ((X.weakenBound sort_m.num).weakenBound sort_m.num) (.bvar (.there .here)))
    (add_m (succ_m zero_m)
      (mul_m (.bvar .here) ((m.weakenBound sort_m.num).weakenBound sort_m.num)))))

/-- 余数模板 `∃ q, q * m + a = b`；用于不变量的第 (C) 条。 -/
def rem_m {Γ Δ : SortContext signature_m} (m a b : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ :=
  .existsE .num (.equal
    (add_m (mul_m (.bvar .here) (m.weakenBound sort_m.num)) (a.weakenBound sort_m.num))
    (b.weakenBound sort_m.num))

/-- 与 `PrimitiveFormulas.beta_m` 同形的本地模板。
`PrimitiveFormulas.beta_m` 的项记法（零、后继、加、乘、两次提升、两个绑定变量）
都是该文件内的私有定义，本模块无法按名展开它们；因此这里用本模块自己的公开
`_m` 记法重述同一个 AST，并由 `beta_template_eq_m` 用定义相等核对两者一致。
模数项同样是 `succ ((i+1) * c)`，四个自由项各提升两层以跨过两个数量词。 -/
def beta_template_m {Γ Δ : SortContext signature_m}
    (b c i v : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  let q : Term signature_m (.num :: .num :: Γ) Δ .num := .bvar (.there .here)
  let d : Term signature_m (.num :: .num :: Γ) Δ .num := .bvar .here
  let m : Term signature_m (.num :: .num :: Γ) Δ .num :=
    succ_m (mul_m (succ_m ((i.weakenBound sort_m.num).weakenBound sort_m.num))
      ((c.weakenBound sort_m.num).weakenBound sort_m.num))
  .existsE .num (.existsE .num (.conj
    (.equal ((b.weakenBound sort_m.num).weakenBound sort_m.num)
      (add_m (mul_m q m) ((v.weakenBound sort_m.num).weakenBound sort_m.num)))
    (.equal (add_m ((v.weakenBound sort_m.num).weakenBound sort_m.num) (succ_m d)) m)))

/-- 本地模板与原 `PrimitiveFormulas.beta_m` 逐层定义相等。
这是"两个模板可连接"的实际核对，不是注释层面的声称。 -/
theorem beta_template_eq_m {Γ Δ : SortContext signature_m}
    (b c i v : Term signature_m Γ Δ .num) :
    PrimitiveFormulas.beta_m b c i v = beta_template_m b c i v := rfl

/-- 内部 β 读取：`b` 在模数 `m_i = 1 + (i+1)c` 下余 `a`，且 `a < m_i`。 -/
def beta_rel_l (b c i a : num_l ℳ) : Prop :=
  ∃ q d : num_l ℳ,
    add_l (mul_l q (modulus_l c i)) a = b ∧ add_l a (succ_l d) = modulus_l c i

/-- 从一次 β 读取中取出它的商见证 `q * m_i + a = b`。 -/
theorem beta_rel_quotient_l {b c i a : num_l ℳ} (h : beta_rel_l b c i a) :
    ∃ q : num_l ℳ, add_l (mul_l q (modulus_l c i)) a = b := by
  obtain ⟨q, _d, hq, _hv⟩ := h
  exact ⟨q, hq⟩

/-- β 读取的余数是规范的：`a < m_i`，差值见证就是读取里的 `d`。 -/
theorem beta_rel_bound_l {b c i a : num_l ℳ} (h : beta_rel_l b c i a) :
    SecondOrderOrder.lt_l a (modulus_l c i) := by
  obtain ⟨_q, d, _hq, hv⟩ := h
  exact ⟨d, hv⟩

/-- 同一被除数在同一模数下的规范余数唯一。
若 `q*m + a = b`、`q'*m + a' = b` 且 `a < m`、`a' < m`，则 `a = a'`。
本引理直接消费 `SecondOrderDivision.eq_l`（它只依赖模型内纯算术），
因此不额外引入总图、编码存在性或标准性前提。 -/
theorem beta_remainder_unique_l (hℳ : Theory.Models ℳ theory_m)
    {m q a q' a' b : num_l ℳ}
    (h : add_l (mul_l q m) a = b) (h' : add_l (mul_l q' m) a' = b)
    (ha : SecondOrderOrder.lt_l a m) (ha' : SecondOrderOrder.lt_l a' m) : a = a' :=
  (SecondOrderDivision.eq_l hℳ m q a q' a' (h.trans h'.symm) ha ha').2

/-- 同一个 `b`、`c`、同一个下标 `i` 上的两次 β 读取只能给出同一个余数。 -/
theorem beta_rel_unique_l (hℳ : Theory.Models ℳ theory_m) {b c i a a' : num_l ℳ}
    (h : beta_rel_l b c i a) (h' : beta_rel_l b c i a') : a = a' := by
  obtain ⟨q, hq⟩ := beta_rel_quotient_l h
  obtain ⟨q', hq'⟩ := beta_rel_quotient_l h'
  exact beta_remainder_unique_l hℳ hq hq' (beta_rel_bound_l h) (beta_rel_bound_l h')

/-- `0 < x` 的见证直接给出 `1 ≤ x` 的见证。 -/
theorem one_le_of_pos_l (hℳ : Theory.Models ℳ theory_m) {x : num_l ℳ}
    (hx : SecondOrderOrder.lt_l (zero_l ℳ) x) :
    letI := semiring_l hℳ
    letI := order_l hℳ
    (1 : num_l ℳ) ≤ x := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  obtain ⟨k, hk⟩ := hx
  exact (le_iff_l hℳ (1 : num_l ℳ) x).mpr ⟨k, by
    change add_l (succ_l (zero_l ℳ)) k = x
    calc
      add_l (succ_l (zero_l ℳ)) k = add_l k (succ_l (zero_l ℳ)) :=
          add_comm_l hℳ (succ_l (zero_l ℳ)) k
      _ = succ_l k := succ_add_one_l hℳ k
      _ = add_l (zero_l ℳ) (succ_l k) := (zero_add_l hℳ (succ_l k)).symm
      _ = x := hk⟩

/-- `modulus_l` 等于两个 `beta_m` 模板里实际出现的模数项 `succ ((i+1) * c)`。
两侧的差别只是加法两个参数的位置，由 `add_comm_l` 与 `succ_add_one_l` 证出，
不是定义相等。 -/
theorem modulus_succ_l (hℳ : Theory.Models ℳ theory_m) (c i : num_l ℳ) :
    modulus_l c i = succ_l (mul_l (succ_l i) c) := by
  change add_l (succ_l (zero_l ℳ)) (mul_l (succ_l i) c) = succ_l (mul_l (succ_l i) c)
  calc
    add_l (succ_l (zero_l ℳ)) (mul_l (succ_l i) c) =
        add_l (mul_l (succ_l i) c) (succ_l (zero_l ℳ)) :=
        add_comm_l hℳ (succ_l (zero_l ℳ)) (mul_l (succ_l i) c)
    _ = succ_l (mul_l (succ_l i) c) := succ_add_one_l hℳ (mul_l (succ_l i) c)

/-- 语法出口之一：`SecondOrderSyntax.beta_m`（四个自由数参数依次为 b、c、i、v）
在任意模型、由这四个参数直接压栈得到的环境中的满足关系就是 `beta_rel_l`。
本出口只覆盖该固定模板，不覆盖任意上下文／任意项的通用模板。 -/
theorem beta_rel_syntax_l (hℳ : Theory.Models ℳ theory_m) (b c i v : num_l ℳ) :
    beta_rel_l b c i v ↔
      Formula.satisfies
        (((((Env.empty (M := ℳ)).pushFree v).pushFree i).pushFree c).pushFree b)
        (SecondOrderSyntax.beta_m) := by
  letI := semiring_l hℳ
  have hsat : Formula.satisfies
        (((((Env.empty (M := ℳ)).pushFree v).pushFree i).pushFree c).pushFree b)
        (SecondOrderSyntax.beta_m) ↔
      (∃ q d : num_l ℳ, b = q * succ_l (mul_l (succ_l i) c) + v ∧
        v + succ_l d = succ_l (mul_l (succ_l i) c)) := by
    simp only [SecondOrderSyntax.beta_m, Formula.satisfies, Term.eval, succ_l, mul_l,
      Env.pushFree]
    rfl
  rw [hsat]
  have hm := modulus_succ_l hℳ c i
  constructor
  · rintro ⟨q, d, hb, hv⟩
    refine ⟨q, d, ?_, ?_⟩
    · calc
        b = add_l (mul_l q (modulus_l c i)) v := hb.symm
        _ = add_l (mul_l q (succ_l (mul_l (succ_l i) c))) v := by rw [hm]
        _ = q * succ_l (mul_l (succ_l i) c) + v := rfl
    · calc
        v + succ_l d = add_l v (succ_l d) := rfl
        _ = modulus_l c i := hv
        _ = succ_l (mul_l (succ_l i) c) := hm
  · rintro ⟨q, d, hb, hv⟩
    refine ⟨q, d, ?_, ?_⟩
    · calc
        add_l (mul_l q (modulus_l c i)) v
            = add_l (mul_l q (succ_l (mul_l (succ_l i) c))) v := by rw [hm]
        _ = q * succ_l (mul_l (succ_l i) c) + v := rfl
        _ = b := hb.symm
    · calc
        add_l v (succ_l d) = v + succ_l d := rfl
        _ = succ_l (mul_l (succ_l i) c) := hv
        _ = modulus_l c i := hm.symm

/-- 语法出口之二（原 `PrimitiveFormulas` 模板的任意模型接线）。
`PrimitiveFormulas.beta_m` 对任意 `Γ Δ`、任意数项 `b c i v` 都给出一条公式，
其内部用两次提升把这四个项跨过两个数量词。本引理对**任意**模型 `ℳ`、
**任意**环境 `η : Env ℳ Γ Δ` 证明：该公式在 `η` 下成立，当且仅当
四项求值后满足 `beta_rel_l`。

证明先把原模板换成本地同形模板（`beta_template_eq_m`），再把
`Formula.satisfies` 与 `Term.eval`（含两次提升的求值）展开成显式的存在式，
最后用 `modulus_succ_l` 把模板里的模数项 `succ ((i+1) * c)` 换成 `modulus_l`。
这里不引用标准模型上的 `PrimitiveFormulas.beta_l`（它只对 `structure_l` 成立），
也不引用 `Nat.beta` 的历史等价。 -/
theorem beta_primitive_syntax_l (hℳ : Theory.Models ℳ theory_m)
    {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (b c i v : Term signature_m Γ Δ .num) :
    Formula.satisfies η (PrimitiveFormulas.beta_m b c i v) ↔
      beta_rel_l (b.eval η) (c.eval η) (i.eval η) (v.eval η) := by
  letI := semiring_l hℳ
  rw [beta_template_eq_m b c i v]
  have hsat : Formula.satisfies η (beta_template_m b c i v) ↔
      (∃ q d : num_l ℳ,
        b.eval η = q * succ_l (mul_l (succ_l (i.eval η)) (c.eval η)) + v.eval η ∧
        v.eval η + succ_l d = succ_l (mul_l (succ_l (i.eval η)) (c.eval η))) := by
    simp only [beta_template_m, Formula.satisfies, Term.eval, Arguments.eval,
      Term.eval_weakenBound, succ_l, mul_l]
    rfl
  rw [hsat]
  have hm := modulus_succ_l hℳ (c.eval η) (i.eval η)
  constructor
  · rintro ⟨q, d, hb, hv⟩
    refine ⟨q, d, ?_, ?_⟩
    · calc
        add_l (mul_l q (modulus_l (c.eval η) (i.eval η))) (v.eval η)
            = add_l (mul_l q (succ_l (mul_l (succ_l (i.eval η)) (c.eval η)))) (v.eval η) :=
                by rw [hm]
        _ = q * succ_l (mul_l (succ_l (i.eval η)) (c.eval η)) + v.eval η := rfl
        _ = b.eval η := hb.symm
    · calc
        add_l (v.eval η) (succ_l d) = v.eval η + succ_l d := rfl
        _ = succ_l (mul_l (succ_l (i.eval η)) (c.eval η)) := hv
        _ = modulus_l (c.eval η) (i.eval η) := hm.symm
  · rintro ⟨q, d, hb, hv⟩
    refine ⟨q, d, ?_, ?_⟩
    · calc
        b.eval η = add_l (mul_l q (modulus_l (c.eval η) (i.eval η))) (v.eval η) := hb.symm
        _ = add_l (mul_l q (succ_l (mul_l (succ_l (i.eval η)) (c.eval η)))) (v.eval η) :=
                by rw [hm]
        _ = q * succ_l (mul_l (succ_l (i.eval η)) (c.eval η)) + v.eval η := rfl
    · calc
        v.eval η + succ_l d = add_l (v.eval η) (succ_l d) := rfl
        _ = modulus_l (c.eval η) (i.eval η) := hv
        _ = succ_l (mul_l (succ_l (i.eval η)) (c.eval η)) := hm

/-- 两个模板的一致性推论。

取上下文 `[.num,.num,.num,.num]`，把四个**自由变量** `.fvar` 依次赋值为 `b`、`c`、
`i`、`v`（用四次 `Env.pushFree` 压成同一个环境），再把这四个自由变量项送入
`beta_primitive_syntax_l`。于是 `beta_rel_syntax_l`（固定四元的 `SecondOrderSyntax.beta_m`）
与 `beta_primitive_syntax_l`（任意上下文的 `PrimitiveFormulas.beta_m`）在该环境下
给出同一个命题。

注意这里**不是**把 `b c i v` 当作新引入的常项符号：它们只是这一次环境赋值的
四个自由变量，`beta_primitive_syntax_l` 本身对任意 `Γ Δ η` 与任意数项成立，
本推论只是它在这一组赋值上的一次实例。语义内容仍由上面两条引理各自证出。 -/
theorem beta_syntax_agree_l (hℳ : Theory.Models ℳ theory_m) (b c i v : num_l ℳ) :
    Formula.satisfies
        (((((Env.empty (M := ℳ)).pushFree v).pushFree i).pushFree c).pushFree b)
        (SecondOrderSyntax.beta_m) ↔
      Formula.satisfies
        (((((Env.empty (M := ℳ)).pushFree v).pushFree i).pushFree c).pushFree b)
        (PrimitiveFormulas.beta_m (.fvar (.here))
          (.fvar (.there .here)) (.fvar (.there (.there .here)))
          (.fvar (.there (.there (.there .here))))) := by
  rw [← beta_rel_syntax_l hℳ b c i v]
  exact (beta_primitive_syntax_l hℳ
    (((((Env.empty (M := ℳ)).pushFree v).pushFree i).pushFree c).pushFree b)
    (.fvar (.here)) (.fvar (.there .here))
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))).symm

/-- 只要 `a` 已经是小于模数的规范余数，`b = q * m_i + a` 就是 β 读取。 -/
theorem beta_rel_of_remainder_l {b c i a : num_l ℳ}
    (hq : ∃ q : num_l ℳ, add_l (mul_l q (modulus_l c i)) a = b)
    (ha : SecondOrderOrder.lt_l a (modulus_l c i)) : beta_rel_l b c i a := by
  obtain ⟨q, hq⟩ := hq
  obtain ⟨d, hd⟩ := ha
  exact ⟨q, d, hq, hd⟩

/-- 第 4 步（正向接口，签名保持原样）：任意内部有限函数都有 β 编码。
`H` 在 `i < n` 上唯一取值；结论给出 `b`、`c`，使每个取值都是 `b` 在模数
`m_i = 1 + (i+1)c` 下的规范余数，即内部 β 读取。
只声明 `H(i,a) → beta_rel_l b c i a`；反向见 `beta_sequence_iff_l`。 -/
theorem beta_sequence_l (hℳ : Theory.Models ℳ theory_m) (H : set_l ℳ) (n : num_l ℳ)
    (hH : ∀ i, SecondOrderOrder.lt_l i n → ∃! a, relation_l H i a) :
    ∃ b c : num_l ℳ, ∀ i, SecondOrderOrder.lt_l i n →
      ∀ a, relation_l H i a → beta_rel_l b c i a := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  -- 把只在截段上有定义的关系补全为内部全函数，并取统一值域界。
  obtain ⟨F, hF, hFH⟩ := complete_l hℳ H n hH
  obtain ⟨B, hB⟩ := bound_l hℳ F hF n
  -- 取被 `1..n` 整除的 `c₀`，再放大到超过值域界。
  obtain ⟨c₀, hc₀pos, hc₀dvd⟩ := common_multiple_l hℳ n
  let c : num_l ℳ := mul_l c₀ (succ_l B)
  have hc₀₁ : (1 : num_l ℳ) ≤ c₀ := one_le_of_pos_l hℳ hc₀pos
  have hcdvd : ∀ d, SecondOrderOrder.lt_l (zero_l ℳ) d →
      SecondOrderOrder.lt_l d (succ_l n) → dvd_l d c := by
    intro d hd hdn
    obtain ⟨k, hk⟩ := hc₀dvd d hd hdn
    refine ⟨mul_l k (succ_l B), ?_⟩
    change d * (k * succ_l B) = c₀ * succ_l B
    change d * k = c₀ at hk
    rw [← hk]
    ring
  have hcpos : SecondOrderOrder.lt_l (zero_l ℳ) c := by
    change (0 : num_l ℳ) < c₀ * succ_l B
    exact mul_pos hc₀pos (SecondOrderOrder.zero_succ_l hℳ B)
  have hcB : SecondOrderOrder.lt_l B c := by
    have hle : succ_l B ≤ c := by
      change succ_l B ≤ c₀ * succ_l B
      calc
        succ_l B = (1 : num_l ℳ) * succ_l B := (SecondOrderMultiplication.one_mul_l hℳ (succ_l B)).symm
        _ ≤ c₀ * succ_l B := mul_le_mul_of_nonneg_right hc₀₁ (zero_le_l hℳ (succ_l B))
    exact lt_of_lt_of_le ((SecondOrderNaturalGraph.lt_succ_l hℳ B B).mpr le_rfl) hle
  -- 每个模数都不小于 `c`，于是既正又大于值域界。
  have hmge : ∀ i, c ≤ modulus_l c i := by
    intro i
    have h₁ : (succ_l (zero_l ℳ) : num_l ℳ) ≤ succ_l i := by
      have h := add_le_add_right (zero_le_l hℳ i) (succ_l (zero_l ℳ))
      change add_l (succ_l (zero_l ℳ)) (zero_l ℳ) ≤ add_l (succ_l (zero_l ℳ)) i at h
      simpa [add_zero_l hℳ, add_comm_l hℳ (succ_l (zero_l ℳ)) i, succ_add_one_l hℳ] using h
    have h₂ : c ≤ mul_l (succ_l i) c := by
      calc
        c = (succ_l (zero_l ℳ) : num_l ℳ) * c := (SecondOrderMultiplication.one_mul_l hℳ c).symm
        _ ≤ succ_l i * c := mul_le_mul_of_nonneg_right h₁ (zero_le_l hℳ c)
    have h₃ : mul_l (succ_l i) c ≤ modulus_l c i := by
      change succ_l i * c ≤ 1 + succ_l i * c
      calc
        succ_l i * c ≤ succ_l i * c + 1 :=
            le_add_of_nonneg_right (zero_le_l hℳ (succ_l (zero_l ℳ)))
        _ = 1 + succ_l i * c := by rw [add_comm]
    exact le_trans h₂ h₃
  have hmpos : ∀ i, SecondOrderOrder.lt_l (zero_l ℳ) (modulus_l c i) :=
    fun i => lt_of_lt_of_le hcpos (hmge i)
  have hmB : ∀ i, SecondOrderOrder.lt_l B (modulus_l c i) :=
    fun i => lt_of_lt_of_le hcB (hmge i)
  -- 归纳不变量：`b` 已读出的前缀、`M` 的整除性与可逆性。
  let P : num_l ℳ → Prop := fun j =>
    ∃ b M : num_l ℳ,
      (∀ i, SecondOrderOrder.lt_l i j → dvd_l (modulus_l c i) M) ∧
      (∀ l, SecondOrderOrder.lt_l l n → SecondOrderOrder.lt_l j (succ_l l) →
        inv_l M (modulus_l c l)) ∧
      (∀ i, SecondOrderOrder.lt_l i j → ∀ a, relation_l F i a →
        ∃ q : num_l ℳ, add_l (mul_l q (modulus_l c i)) a = b)
  let P' : num_l ℳ → Prop := fun j => SecondOrderOrder.lt_l j (succ_l n) → P j
  -- 三条不变量的纯算术模板；绑定变量上下文都是 `[.num, .num]`（`M`、`b`）。
  let A₁ : Formula signature_m [.num, .num] [.num, .num, .num, .set] :=
    .forallE .num (.imp
      (PrimitiveFormulas.lt_m (.bvar .here) (.fvar .here))
      (dvd_m (modulus_m (.fvar (.there (.there .here))) (.bvar .here))
        (.bvar (.there .here))))
  let B₁ : Formula signature_m [.num, .num] [.num, .num, .num, .set] :=
    .forallE .num (.imp
      (PrimitiveFormulas.lt_m (.bvar .here) (.fvar (.there .here)))
      (.imp (PrimitiveFormulas.lt_m (.fvar .here) (succ_m (.bvar .here)))
        (inv_m (.bvar (.there .here))
          (modulus_m (.fvar (.there (.there .here))) (.bvar .here)))))
  let C₁ : Formula signature_m [.num, .num] [.num, .num, .num, .set] :=
    .forallE .num (.imp
      (PrimitiveFormulas.lt_m (.bvar .here) (.fvar .here))
      (.forallE .num (.imp
        (GraphSyntax.edge_m (.fvar (.there (.there (.there .here))))
          (.bvar (.there .here)) (.bvar .here))
        (rem_m (modulus_m (.fvar (.there (.there .here))) (.bvar (.there .here)))
          (.bvar .here) (.bvar (.there (.there (.there .here))))))))
  let φ : Formula signature_m [] [.num, .num, .num, .set] :=
    .imp
      (PrimitiveFormulas.lt_m (.fvar .here) (succ_m (.fvar (.there .here))))
      (.existsE .num (.existsE .num (.conj A₁ (.conj B₁ C₁))))
  have hφ : language_m φ = true := pure_language_m _ rfl
  let η : Env ℳ [] [.num, .num, .set] :=
    (((Env.empty (M := ℳ)).pushFree F).pushFree c).pushFree n
  have hP : ∀ j, Formula.satisfies (Env.pushFree η j) φ ↔ P' j := by
    intro j
    simp only [φ, A₁, B₁, C₁, P', P, Formula.satisfies, SecondOrderOrder.formula_l,
      SecondOrderOrder.lt_l, SecondOrderPairing.edge_l, zero_m, succ_m, add_m, mul_m,
      modulus_m, dvd_m, inv_m, rem_m, Term.eval, Arguments.eval,
      zero_l, succ_l, add_l, mul_l, dvd_l, inv_l, modulus_l,
      Env.pushBound, Env.pushFree, Assignment.push]
    rfl
  have hmain : ∀ j, P' j := induct_l hℳ φ hφ η P' hP
    (by
      intro hj
      refine ⟨zero_l ℳ, succ_l (zero_l ℳ), ?_, ?_, ?_⟩
      · intro i hi
        exact False.elim ((not_lt_of_ge (zero_le_l hℳ i)) hi)
      · intro l hln hjl
        exact inv_one_l hℳ (modulus_l c l)
      · intro i hi
        exact False.elim ((not_lt_of_ge (zero_le_l hℳ i)) hi))
    (by
      rintro j hpj hj1
      have hle_jn : succ_l j ≤ n := (SecondOrderNaturalGraph.lt_succ_l hℳ (succ_l j) n).mp hj1
      have hjn : SecondOrderOrder.lt_l j n := lt_of_lt_of_le
        ((SecondOrderNaturalGraph.lt_succ_l hℳ j j).mpr le_rfl) hle_jn
      have hjjn : SecondOrderOrder.lt_l j (succ_l n) := SecondOrderOrder.trans_l hℳ hjn
        ((SecondOrderNaturalGraph.lt_succ_l hℳ n n).mpr le_rfl)
      obtain ⟨b, M, hA, hBv, hC⟩ := hpj hjjn
      obtain ⟨a, hFa, hFaU⟩ := hF j
      obtain ⟨u, k, hMu⟩ :=
        hBv j hjn ((SecondOrderNaturalGraph.lt_succ_l hℳ j j).mpr le_rfl)
      obtain ⟨s, hs⟩ :=
        (le_iff_l hℳ (1 : num_l ℳ) (modulus_l c j)).mp (one_le_of_pos_l hℳ (hmpos j))
      change M * u = 1 + k * modulus_l c j at hMu
      change 1 + s = modulus_l c j at hs
      -- 增量系数 `t` 与新商 `Q`：两种情况都只由加法见证与乘法给出。
      obtain ⟨t, Q, hstep⟩ : ∃ t Q : num_l ℳ,
          add_l (mul_l Q (modulus_l c j)) a = add_l b (mul_l M t) := by
        rcases le_total b a with hba | hab
        · obtain ⟨w, hw⟩ := (le_iff_l hℳ b a).mp hba
          change b + w = a at hw
          refine ⟨mul_l u w, mul_l k w, ?_⟩
          change (k * w) * modulus_l c j + a = b + M * (u * w)
          calc
            (k * w) * modulus_l c j + a = (k * w) * modulus_l c j + (b + w) := by rw [← hw]
            _ = b + (1 + k * modulus_l c j) * w := by ring
            _ = b + (M * u) * w := by rw [← hMu]
            _ = b + M * (u * w) := by ring
        · obtain ⟨w, hw⟩ := (le_iff_l hℳ a b).mp hab
          change a + w = b at hw
          refine ⟨mul_l (mul_l u w) s, add_l w (mul_l (mul_l k w) s), ?_⟩
          change (w + k * w * s) * modulus_l c j + a = b + M * ((u * w) * s)
          calc
            (w + k * w * s) * modulus_l c j + a
                = a + w * modulus_l c j + (k * w * s) * modulus_l c j := by ring
            _ = a + w * (1 + s) + (k * w * s) * modulus_l c j := by rw [← hs]
            _ = a + w + w * s + (k * w * s) * modulus_l c j := by ring
            _ = b + w * s + (k * w * s) * modulus_l c j := by rw [hw]
            _ = b + (1 + k * modulus_l c j) * (w * s) := by ring
            _ = b + (M * u) * (w * s) := by rw [← hMu]
            _ = b + M * ((u * w) * s) := by ring
      let M' : num_l ℳ := mul_l M (modulus_l c j)
      let b' : num_l ℳ := add_l b (mul_l M t)
      refine ⟨b', M', ?_, ?_, ?_⟩
      · intro i hi
        have hilej : i ≤ j := (SecondOrderNaturalGraph.lt_succ_l hℳ i j).mp hi
        rcases eq_or_lt_of_le hilej with hieq | hij
        · refine ⟨M, ?_⟩
          rw [hieq]
          change modulus_l c j * M = M * modulus_l c j
          rw [mul_comm]
        · obtain ⟨r, hr⟩ := hA i hij
          refine ⟨mul_l r (modulus_l c j), ?_⟩
          change modulus_l c i * (r * modulus_l c j) = M * modulus_l c j
          change modulus_l c i * r = M at hr
          rw [← hr]
          ring
      · intro l hln hj1l
        have hle : succ_l j ≤ l := (SecondOrderNaturalGraph.lt_succ_l hℳ (succ_l j) l).mp hj1l
        have hjl : SecondOrderOrder.lt_l j l := lt_of_lt_of_le
          ((SecondOrderNaturalGraph.lt_succ_l hℳ j j).mpr le_rfl) hle
        have hjls : SecondOrderOrder.lt_l j (succ_l l) := SecondOrderOrder.trans_l hℳ hjl
          ((SecondOrderNaturalGraph.lt_succ_l hℳ l l).mpr le_rfl)
        exact inv_mul_l hℳ (hBv l hln hjls) (modulus_inv_l hℳ n c hcdvd hcpos hjl hln)
      · intro i hi a' hFi
        have hilej : i ≤ j := (SecondOrderNaturalGraph.lt_succ_l hℳ i j).mp hi
        rcases eq_or_lt_of_le hilej with hieq | hij
        · have hFi' : relation_l F j a' := by
            rw [← hieq]
            exact hFi
          refine ⟨Q, ?_⟩
          rw [hieq, hFaU a' hFi']
          exact hstep
        · obtain ⟨q, hq⟩ := hC i hij a' hFi
          obtain ⟨r, hr⟩ := hA i hij
          refine ⟨add_l q (mul_l r t), ?_⟩
          change (q + r * t) * modulus_l c i + a' = b + M * t
          change q * modulus_l c i + a' = b at hq
          change modulus_l c i * r = M at hr
          calc
            (q + r * t) * modulus_l c i + a' =
                (q * modulus_l c i + a') + (r * t) * modulus_l c i := by ring
            _ = b + (r * t) * modulus_l c i := by rw [hq]
            _ = b + (modulus_l c i * r) * t := by ring
            _ = b + M * t := by rw [hr])
  obtain ⟨b, _M, _hA, _hBv, hC⟩ :=
    hmain n ((SecondOrderNaturalGraph.lt_succ_l hℳ n n).mpr le_rfl)
  refine ⟨b, c, ?_⟩
  intro i hi a ha
  have hFi : relation_l F i a := (hFH i hi a).mpr ha
  exact beta_rel_of_remainder_l (hC i hi a hFi)
    (SecondOrderOrder.trans_l hℳ (hB i hi a hFi) (hmB i))

/-- 第 4 步（双向结论）：同一对 `b`、`c` 上，β 读取与 `H` 的取值精确等价。

正向就是 `beta_sequence_l`，未作改动。反向的思路是：
对 `i < n`，由 `hH` 取 `H` 在该处的实际唯一取值 `a₀`；正向已给出
`beta_rel_l b c i a₀`。任意满足 `beta_rel_l b c i a` 的 `a` 当然也是
小于 `m_i` 的规范余数，于是 `beta_remainder_unique_l` 给出 `a = a₀`，
再把 `a₀` 处的 `H` 成员关系改写回来。

除 `hH` 给出的唯一取值外不增加任何前提：没有总图、编码存在性或标准性假设。
`n = 0` 时 `i < n` 无实例，等价式空真；`n` 为后继时由 `beta_sequence_l`
归纳的最后一步覆盖到 `i < n` 的全部下标。 -/
theorem beta_sequence_iff_l (hℳ : Theory.Models ℳ theory_m) (H : set_l ℳ) (n : num_l ℳ)
    (hH : ∀ i, SecondOrderOrder.lt_l i n → ∃! a, relation_l H i a) :
    ∃ b c : num_l ℳ, ∀ i, SecondOrderOrder.lt_l i n →
      ∀ a, beta_rel_l b c i a ↔ relation_l H i a := by
  obtain ⟨b, c, hfwd⟩ := beta_sequence_l hℳ H n hH
  refine ⟨b, c, ?_⟩
  intro i hi a
  constructor
  · -- β 值 → `H`：先用 `hH` 取该下标的实际取值，再用余数唯一性对齐。
    intro hb
    obtain ⟨a₀, ha₀H, _ha₀U⟩ := hH i hi
    have hb₀ : beta_rel_l b c i a₀ := hfwd i hi a₀ ha₀H
    have haa₀ : a = a₀ := beta_rel_unique_l hℳ hb hb₀
    rw [haa₀]
    exact ha₀H
  · -- `H` 值 → β 值：就是原正向接口。
    exact hfwd i hi a

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderBetaSequence



