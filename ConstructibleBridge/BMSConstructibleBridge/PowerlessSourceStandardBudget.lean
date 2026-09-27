import BMSConstructibleBridge.PowerlessSourceComplexityQuantifier
import BMSConstructibleBridge.PowerlessSourceFiniteReflection
import BMSConstructibleBridge.PowerlessSourceInclusion
import BMSConstructibleBridge.PowerlessNumeral
import BMSConstructibleBridge.PowerlessNaturalCompare

/-!
# 原源公式的固定外部数码编译预算

对原 `Logic.FirstOrder.Formula ℒ Γ Δ` 定义真正可计算的外部预算 `budget_m`——原子、
`falsum`、`truth` 取 0，`neg` 不变，二元联结词取两侧 `max`，`existsE`／`forallE` 的
body 预算加 2。本节把层号固定为该外部预算对应的实际数码值，并在此同一数码层上交付
两项同源出口。

检查点1 `bound_l`（`bound_budget_l`）：任意公式都能在其预算对应的外部数码层上编译，
即取 `a` 满足 `numeral_l e (budget_m φ) a`，就有 `bound_l ... a p φ`。

检查点2 `reflects_l`（`reflect_budget_l`）：同一 `a` 上原公式的有限层反射合同成立，
即对全部两域实际求值器与小域参数，`ν(budget_m φ)` 层足以把上域满足性反射回子域。
量化分支由 `peel_succ_l` 剥去 body 加两层的数码、`PowerlessNaturalCompare.zero_le_l`
取下域含 `e`，再经 `monotone_l` 把子式预算升到同一 `max` 层。

与 `PowerlessSourceComplexityTotal` 只宣称“存在某个内部层号”不同，这里把层号固定为
外部预算对应的实际数码值；小前置 `numeral_le_subset_l` 说明数码单调：`k ≤ l` 时
`ν(k) ⊆ ν(l)`，据此把子式预算升级合并到同一 `max` 层。本节定理不反向解码内部自然数，
也不把模型 ω 假定为外部标准。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceStandardBudget

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessSourceFiniteReflection

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}

/-- 可计算的外部编译预算：原子／`falsum`／`truth` 为 0，`neg` 不变，
二元联结词取两侧最大值，量化 body 加两层。 -/
def budget_m {Γ Δ : SortContext ℒ} : Formula ℒ Γ Δ → Nat
  | .falsum => 0
  | .truth => 0
  | .rel _ _ => 0
  | .equal _ _ => 0
  | .neg body => budget_m body
  | .conj left right
  | .disj left right
  | .imp left right
  | .iff left right => Nat.max (budget_m left) (budget_m right)
  | .forallE _ body
  | .existsE _ body => budget_m body + 2

/-- 外部数码在语法后继处的展开：`numeral_l e (m+1) a` 恰为存在上一步 `b`。 -/
theorem peel_succ_l (e : carrier_l ℳ) {m : Nat} {a : carrier_l ℳ}
    (ha : PowerlessNumeral.numeral_l e (m + 1) a) :
    ∃ b, PowerlessNumeral.numeral_l e m b ∧ PowerlessNatural.successor_l b a := ha

/-- 数码单调：外部 `k ≤ l` 时，两个数码值满足 `ν(k) ⊆ ν(l)`。
对较大的外部指标 `l` 归纳；后继情形按 `k = l+1`（两侧数码同为 `ν(l)` 的后继，先由
`unique_l` 再 `successor_unique_l` 得 `a = b`）或 `k ≤ l`（递归得 `ν(k) ⊆ ν(l)` 再并入
`ν(l+1)`）分治。 -/
theorem numeral_le_subset_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (e : carrier_l ℳ) {k l : Nat} {a b : carrier_l ℳ} (hkl : k ≤ l)
    (ha : PowerlessNumeral.numeral_l e k a) (hb : PowerlessNumeral.numeral_l e l b) :
    subset_l a b := by
  have key : ∀ (l : Nat) (b : carrier_l ℳ), PowerlessNumeral.numeral_l e l b →
      ∀ (k : Nat) (a : carrier_l ℳ), PowerlessNumeral.numeral_l e k a → k ≤ l →
        subset_l a b := by
    intro l
    induction l with
    | zero =>
        intro b hb k a ha hle
        have hk : k = 0 := Nat.le_zero.mp hle
        subst hk
        have ha' : a = e := ha
        have hb' : b = e := hb
        subst ha'
        subst hb'
        exact fun _ hx => hx
    | succ l ih =>
        intro b hb k a ha hle
        obtain ⟨c, hc, hs⟩ := hb
        rcases Nat.eq_or_lt_of_le hle with hkeq | hlt
        · subst hkeq
          obtain ⟨c', hc', hs'⟩ := ha
          have hcc : c' = c := PowerlessNumeral.unique_l hℳ hc' hc
          subst hcc
          have hab : a = b := PowerlessNatural.successor_unique_l hℳ hs' hs
          subst hab
          exact fun _ hx => hx
        · have hsub1 : subset_l a c := ih c hc k a ha (Nat.lt_succ_iff.mp hlt)
          have hsub2 : subset_l c b := fun x hx => (hs x).mpr (Or.inl hx)
          exact fun x hx => hsub2 x (hsub1 x hx)
  exact key l b hb k a ha hkl

variable (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)

include hℳ hω ht hT

/-- 每个原源公式都能在其固定外部预算数码层上编译：取 `a` 为预算对应的外部数码值，
即 `numeral_l e (budget_m φ) a`，则任意极性 `p` 下 `bound_l ... a p φ` 成立。
逐构造对照 `PowerlessSourceComplexityTotal`，但把层号钉死为预算数码：叶子层由
`numeral_l` 落回零元、联结词由 `numeral_le_subset_l` 升级到 `max` 层、量词把
`+2` 数码两次 `successor` 剥成中间层与目标层。 -/
theorem bound_budget_l {Γ Δ : SortContext ℒ} :
    ∀ (φ : Formula ℒ Γ Δ) (a : carrier_l ℳ),
      PowerlessNumeral.numeral_l e (budget_m φ) a →
      ∀ p, PowerlessSourceComplexity.bound_l ω e T t₁ t₂ t₃ a p φ := by
  intro φ
  induction φ with
  | falsum =>
      intro a ha p
      have hm : member_l ℳ a ω := PowerlessNumeral.natural_l hℳ hω ht.1 ha
      exact PowerlessSourceComplexity.delta_l hℳ hω ht hT .falsum hm p
  | truth =>
      intro a ha p
      have hm : member_l ℳ a ω := PowerlessNumeral.natural_l hℳ hω ht.1 ha
      exact PowerlessSourceComplexity.delta_l hℳ hω ht hT .truth hm p
  | rel r args =>
      intro a ha p
      have hm : member_l ℳ a ω := PowerlessNumeral.natural_l hℳ hω ht.1 ha
      exact PowerlessSourceComplexity.delta_l hℳ hω ht hT (.rel r args) hm p
  | equal s t =>
      intro a ha p
      have hm : member_l ℳ a ω := PowerlessNumeral.natural_l hℳ hω ht.1 ha
      exact PowerlessSourceComplexity.delta_l hℳ hω ht hT (.equal s t) hm p
  | neg body ih =>
      intro a ha p
      have ha' : PowerlessNumeral.numeral_l e (budget_m body) a := ha
      simpa only [PowerlessSourcePolarity.flip_l] using
        PowerlessSourceComplexityLogic.negation_l hℳ hω ht hT (ih a ha' p.flip)
  | conj left right ihLeft ihRight =>
      intro a ha p
      obtain ⟨b₁, hb₁⟩ := PowerlessNumeral.exists_l hℳ e (budget_m left)
      obtain ⟨b₂, hb₂⟩ := PowerlessNumeral.exists_l hℳ e (budget_m right)
      have hm : member_l ℳ a ω := PowerlessNumeral.natural_l hℳ hω ht.1 ha
      have h₁ : PowerlessSourceComplexity.bound_l ω e T t₁ t₂ t₃ a p left :=
        PowerlessSourceComplexity.monotone_l hℳ hω ht hT hm
          (numeral_le_subset_l hℳ e (Nat.le_max_left _ _) hb₁ ha) (ihLeft b₁ hb₁ p)
      have h₂ : PowerlessSourceComplexity.bound_l ω e T t₁ t₂ t₃ a p right :=
        PowerlessSourceComplexity.monotone_l hℳ hω ht hT hm
          (numeral_le_subset_l hℳ e (Nat.le_max_right _ _) hb₂ ha) (ihRight b₂ hb₂ p)
      exact PowerlessSourceComplexityLogic.conjunction_l hℳ hω ht hT h₁ h₂
  | disj left right ihLeft ihRight =>
      intro a ha p
      obtain ⟨b₁, hb₁⟩ := PowerlessNumeral.exists_l hℳ e (budget_m left)
      obtain ⟨b₂, hb₂⟩ := PowerlessNumeral.exists_l hℳ e (budget_m right)
      have hm : member_l ℳ a ω := PowerlessNumeral.natural_l hℳ hω ht.1 ha
      have h₁ : PowerlessSourceComplexity.bound_l ω e T t₁ t₂ t₃ a p left :=
        PowerlessSourceComplexity.monotone_l hℳ hω ht hT hm
          (numeral_le_subset_l hℳ e (Nat.le_max_left _ _) hb₁ ha) (ihLeft b₁ hb₁ p)
      have h₂ : PowerlessSourceComplexity.bound_l ω e T t₁ t₂ t₃ a p right :=
        PowerlessSourceComplexity.monotone_l hℳ hω ht hT hm
          (numeral_le_subset_l hℳ e (Nat.le_max_right _ _) hb₂ ha) (ihRight b₂ hb₂ p)
      exact PowerlessSourceComplexityLogic.disjunction_l hℳ hω ht hT h₁ h₂
  | imp left right ihLeft ihRight =>
      intro a ha p
      obtain ⟨b₁, hb₁⟩ := PowerlessNumeral.exists_l hℳ e (budget_m left)
      obtain ⟨b₂, hb₂⟩ := PowerlessNumeral.exists_l hℳ e (budget_m right)
      have hm : member_l ℳ a ω := PowerlessNumeral.natural_l hℳ hω ht.1 ha
      have h₁ : PowerlessSourceComplexity.bound_l ω e T t₁ t₂ t₃ a p.flip left :=
        PowerlessSourceComplexity.monotone_l hℳ hω ht hT hm
          (numeral_le_subset_l hℳ e (Nat.le_max_left _ _) hb₁ ha) (ihLeft b₁ hb₁ p.flip)
      have h₂ : PowerlessSourceComplexity.bound_l ω e T t₁ t₂ t₃ a p right :=
        PowerlessSourceComplexity.monotone_l hℳ hω ht hT hm
          (numeral_le_subset_l hℳ e (Nat.le_max_right _ _) hb₂ ha) (ihRight b₂ hb₂ p)
      exact PowerlessSourceComplexityLogic.implication_l hℳ hω ht hT h₁ h₂
  | iff left right ihLeft ihRight =>
      intro a ha p
      obtain ⟨b₁, hb₁⟩ := PowerlessNumeral.exists_l hℳ e (budget_m left)
      obtain ⟨b₂, hb₂⟩ := PowerlessNumeral.exists_l hℳ e (budget_m right)
      have hm : member_l ℳ a ω := PowerlessNumeral.natural_l hℳ hω ht.1 ha
      have hL₁ : PowerlessSourceComplexity.bound_l ω e T t₁ t₂ t₃ a p left :=
        PowerlessSourceComplexity.monotone_l hℳ hω ht hT hm
          (numeral_le_subset_l hℳ e (Nat.le_max_left _ _) hb₁ ha) (ihLeft b₁ hb₁ p)
      have hL₀ : PowerlessSourceComplexity.bound_l ω e T t₁ t₂ t₃ a p.flip left :=
        PowerlessSourceComplexity.monotone_l hℳ hω ht hT hm
          (numeral_le_subset_l hℳ e (Nat.le_max_left _ _) hb₁ ha) (ihLeft b₁ hb₁ p.flip)
      have hR₁ : PowerlessSourceComplexity.bound_l ω e T t₁ t₂ t₃ a p right :=
        PowerlessSourceComplexity.monotone_l hℳ hω ht hT hm
          (numeral_le_subset_l hℳ e (Nat.le_max_right _ _) hb₂ ha) (ihRight b₂ hb₂ p)
      have hR₀ : PowerlessSourceComplexity.bound_l ω e T t₁ t₂ t₃ a p.flip right :=
        PowerlessSourceComplexity.monotone_l hℳ hω ht hT hm
          (numeral_le_subset_l hℳ e (Nat.le_max_right _ _) hb₂ ha) (ihRight b₂ hb₂ p.flip)
      exact PowerlessSourceComplexityLogic.biconditional_l hℳ hω ht hT hL₁ hL₀ hR₁ hR₀
  | existsE sort body ih =>
      cases sort
      intro a ha q
      have h2 : PowerlessNumeral.numeral_l e (budget_m body + 1 + 1) a := ha
      obtain ⟨a₁, ha₁, hs₁⟩ := peel_succ_l e h2
      obtain ⟨a₀, ha₀, hs₀⟩ := peel_succ_l e ha₁
      have hm₀ : member_l ℳ a₀ ω := PowerlessNumeral.natural_l hℳ hω ht.1 ha₀
      have hm₁ : member_l ℳ a₁ ω := PowerlessNumeral.natural_l hℳ hω ht.1 ha₁
      have hm : member_l ℳ a ω := PowerlessNumeral.natural_l hℳ hω ht.1 ha
      have he : member_l ℳ e a₁ :=
        (hs₀ e).mpr (PowerlessNaturalCompare.zero_le_l hℳ hω ht.1 a₀ hm₀)
      exact PowerlessSourceComplexity.raise_l hℳ hω ht hT hm ((hs₁ a₁).mpr (Or.inr rfl))
        (PowerlessSourceComplexityQuantifier.existential_l hℳ hω ht hT he
          (PowerlessSourceComplexity.monotone_l hℳ hω ht hT hm₁
            (fun x hx => (hs₀ x).mpr (Or.inl hx)) (ih a₀ ha₀ .sigma)))
  | forallE sort body ih =>
      cases sort
      intro a ha q
      have h2 : PowerlessNumeral.numeral_l e (budget_m body + 1 + 1) a := ha
      obtain ⟨a₁, ha₁, hs₁⟩ := peel_succ_l e h2
      obtain ⟨a₀, ha₀, hs₀⟩ := peel_succ_l e ha₁
      have hm₀ : member_l ℳ a₀ ω := PowerlessNumeral.natural_l hℳ hω ht.1 ha₀
      have hm₁ : member_l ℳ a₁ ω := PowerlessNumeral.natural_l hℳ hω ht.1 ha₁
      have hm : member_l ℳ a ω := PowerlessNumeral.natural_l hℳ hω ht.1 ha
      have he : member_l ℳ e a₁ :=
        (hs₀ e).mpr (PowerlessNaturalCompare.zero_le_l hℳ hω ht.1 a₀ hm₀)
      exact PowerlessSourceComplexity.raise_l hℳ hω ht hT hm ((hs₁ a₁).mpr (Or.inr rfl))
        (PowerlessSourceComplexityQuantifier.universal_l hℳ hω ht hT he
          (PowerlessSourceComplexity.monotone_l hℳ hω ht hT hm₁
            (fun x hx => (hs₀ x).mpr (Or.inl hx)) (ih a₀ ha₀ .pi)))

/-- 每个原源公式的有限反射也能钉在其固定外部预算数码层上：取 `a` 满足
`numeral_l e (budget_m φ) a`，则 `reflects_l ... a φ`。逐构造对照
`PowerlessSourceReflectionTotal.formula_l`，但层号由预算数码固定。量词的 `+2`
剥出中间层 `a₁`（用于把 `e ∈ a` 经 `successor` 与 `zero_le` 落实），再把子式的
`reflects` 与 `bound`（由 `bound_budget_l` 给出）经 `monotone_l` 升到目标层 `a`。 -/
theorem reflect_budget_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ Γ Δ) :
    ∀ (a : carrier_l ℳ), PowerlessNumeral.numeral_l e (budget_m φ) a →
      reflects_l ω e T t₁ t₂ t₃ a φ := by
  match φ with
  | .falsum =>
      intro a ha A U S R F G hA hU hF hG hS hAU hC η
      exact Iff.rfl
  | .truth =>
      intro a ha A U S R F G hA hU hF hG hS hAU hC η
      exact Iff.rfl
  | .rel .membership (.cons s (.cons t .nil)) =>
      intro a ha A U S R F G hA hU hF hG hS hAU hC η
      exact PowerlessSourceInclusion.member_l hAU η s t
  | .equal (sort := .set) s t =>
      intro a ha A U S R F G hA hU hF hG hS hAU hC η
      exact PowerlessSourceInclusion.equal_l hAU η s t
  | .neg body =>
      intro a ha
      exact PowerlessSourceFiniteReflection.negation_l (reflect_budget_l body a ha)
  | .conj left right =>
      intro a ha
      obtain ⟨b₁, hb₁⟩ := PowerlessNumeral.exists_l hℳ e (budget_m left)
      obtain ⟨b₂, hb₂⟩ := PowerlessNumeral.exists_l hℳ e (budget_m right)
      have hm : member_l ℳ a ω := PowerlessNumeral.natural_l hℳ hω ht.1 ha
      have h₁ : reflects_l ω e T t₁ t₂ t₃ a left :=
        PowerlessSourceFiniteReflection.monotone_l hℳ hω ht hT hm
          (numeral_le_subset_l hℳ e (Nat.le_max_left _ _) hb₁ ha) (reflect_budget_l left b₁ hb₁)
      have h₂ : reflects_l ω e T t₁ t₂ t₃ a right :=
        PowerlessSourceFiniteReflection.monotone_l hℳ hω ht hT hm
          (numeral_le_subset_l hℳ e (Nat.le_max_right _ _) hb₂ ha) (reflect_budget_l right b₂ hb₂)
      apply PowerlessSourceFiniteReflection.conjunction_l
      · exact h₁
      · exact h₂
  | .disj left right =>
      intro a ha
      obtain ⟨b₁, hb₁⟩ := PowerlessNumeral.exists_l hℳ e (budget_m left)
      obtain ⟨b₂, hb₂⟩ := PowerlessNumeral.exists_l hℳ e (budget_m right)
      have hm : member_l ℳ a ω := PowerlessNumeral.natural_l hℳ hω ht.1 ha
      have h₁ : reflects_l ω e T t₁ t₂ t₃ a left :=
        PowerlessSourceFiniteReflection.monotone_l hℳ hω ht hT hm
          (numeral_le_subset_l hℳ e (Nat.le_max_left _ _) hb₁ ha) (reflect_budget_l left b₁ hb₁)
      have h₂ : reflects_l ω e T t₁ t₂ t₃ a right :=
        PowerlessSourceFiniteReflection.monotone_l hℳ hω ht hT hm
          (numeral_le_subset_l hℳ e (Nat.le_max_right _ _) hb₂ ha) (reflect_budget_l right b₂ hb₂)
      apply PowerlessSourceFiniteReflection.disjunction_l
      · exact h₁
      · exact h₂
  | .imp left right =>
      intro a ha
      obtain ⟨b₁, hb₁⟩ := PowerlessNumeral.exists_l hℳ e (budget_m left)
      obtain ⟨b₂, hb₂⟩ := PowerlessNumeral.exists_l hℳ e (budget_m right)
      have hm : member_l ℳ a ω := PowerlessNumeral.natural_l hℳ hω ht.1 ha
      have h₁ : reflects_l ω e T t₁ t₂ t₃ a left :=
        PowerlessSourceFiniteReflection.monotone_l hℳ hω ht hT hm
          (numeral_le_subset_l hℳ e (Nat.le_max_left _ _) hb₁ ha) (reflect_budget_l left b₁ hb₁)
      have h₂ : reflects_l ω e T t₁ t₂ t₃ a right :=
        PowerlessSourceFiniteReflection.monotone_l hℳ hω ht hT hm
          (numeral_le_subset_l hℳ e (Nat.le_max_right _ _) hb₂ ha) (reflect_budget_l right b₂ hb₂)
      apply PowerlessSourceFiniteReflection.implication_l
      · exact h₁
      · exact h₂
  | .iff left right =>
      intro a ha
      obtain ⟨b₁, hb₁⟩ := PowerlessNumeral.exists_l hℳ e (budget_m left)
      obtain ⟨b₂, hb₂⟩ := PowerlessNumeral.exists_l hℳ e (budget_m right)
      have hm : member_l ℳ a ω := PowerlessNumeral.natural_l hℳ hω ht.1 ha
      have h₁ : reflects_l ω e T t₁ t₂ t₃ a left :=
        PowerlessSourceFiniteReflection.monotone_l hℳ hω ht hT hm
          (numeral_le_subset_l hℳ e (Nat.le_max_left _ _) hb₁ ha) (reflect_budget_l left b₁ hb₁)
      have h₂ : reflects_l ω e T t₁ t₂ t₃ a right :=
        PowerlessSourceFiniteReflection.monotone_l hℳ hω ht hT hm
          (numeral_le_subset_l hℳ e (Nat.le_max_right _ _) hb₂ ha) (reflect_budget_l right b₂ hb₂)
      apply PowerlessSourceFiniteReflection.biconditional_l
      · exact h₁
      · exact h₂
  | .existsE .set body =>
      intro a ha
      have h2 : PowerlessNumeral.numeral_l e (budget_m body + 1 + 1) a := ha
      obtain ⟨a₁, ha₁, hs₁⟩ := peel_succ_l e h2
      obtain ⟨a₀, ha₀, hs₀⟩ := peel_succ_l e ha₁
      have hm : member_l ℳ a ω := PowerlessNumeral.natural_l hℳ hω ht.1 ha
      have hm₁ : member_l ℳ a₁ ω := PowerlessNumeral.natural_l hℳ hω ht.1 ha₁
      have he : member_l ℳ e a :=
        (hs₁ e).mpr (PowerlessNaturalCompare.zero_le_l hℳ hω ht.1 a₁ hm₁)
      have hsub : subset_l a₀ a := numeral_le_subset_l hℳ e (Nat.le_add_right _ 2) ha₀ ha
      have hφ : reflects_l ω e T t₁ t₂ t₃ a body :=
        PowerlessSourceFiniteReflection.monotone_l hℳ hω ht hT hm hsub (reflect_budget_l body a₀ ha₀)
      have hB : PowerlessSourceComplexity.bound_l ω e T t₁ t₂ t₃ a .sigma body :=
        PowerlessSourceComplexity.monotone_l hℳ hω ht hT hm hsub
          (bound_budget_l hℳ hω ht hT body a₀ ha₀ .sigma)
      apply PowerlessSourceFiniteReflection.existential_l hℳ hω ht hT he hB
      exact hφ
  | .forallE .set body =>
      intro a ha
      have h2 : PowerlessNumeral.numeral_l e (budget_m body + 1 + 1) a := ha
      obtain ⟨a₁, ha₁, hs₁⟩ := peel_succ_l e h2
      obtain ⟨a₀, ha₀, hs₀⟩ := peel_succ_l e ha₁
      have hm : member_l ℳ a ω := PowerlessNumeral.natural_l hℳ hω ht.1 ha
      have hm₁ : member_l ℳ a₁ ω := PowerlessNumeral.natural_l hℳ hω ht.1 ha₁
      have he : member_l ℳ e a :=
        (hs₁ e).mpr (PowerlessNaturalCompare.zero_le_l hℳ hω ht.1 a₁ hm₁)
      have hsub : subset_l a₀ a := numeral_le_subset_l hℳ e (Nat.le_add_right _ 2) ha₀ ha
      have hφ : reflects_l ω e T t₁ t₂ t₃ a body :=
        PowerlessSourceFiniteReflection.monotone_l hℳ hω ht hT hm hsub (reflect_budget_l body a₀ ha₀)
      have hB : PowerlessSourceComplexity.bound_l ω e T t₁ t₂ t₃ a .pi body :=
        PowerlessSourceComplexity.monotone_l hℳ hω ht hT hm hsub
          (bound_budget_l hℳ hω ht hT body a₀ ha₀ .pi)
      apply PowerlessSourceFiniteReflection.universal_l hℳ hω ht hT he hB
      exact hφ

/- 公理审计：外部预算的新出口只应继承已复编模块的可信基，
不得引入 `sorryAx` 或新公理。 -/
#print axioms budget_m
#print axioms peel_succ_l
#print axioms numeral_le_subset_l
#print axioms bound_budget_l
#print axioms reflect_budget_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceStandardBudget
