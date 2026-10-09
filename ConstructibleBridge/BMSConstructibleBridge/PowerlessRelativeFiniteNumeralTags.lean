import BMSConstructibleBridge.PowerlessBMSQuotientSuccessor
import BMSConstructibleBridge.PowerlessNumeralFormula
import BMSConstructibleBridge.PowerlessSourceRequestParameters
import BMSConstructibleBridge.PowerlessRelativeSourceSkolemFamily
import BMSConstructibleBridge.SecondOrderNumeralBounds

/-!
# 原 Z₂ 中实际存在的有限 numeral 标签

对象语言为纯隶属 ℒ，背景为原 SecondOrderArithmetic.theory_m。
标签依次为外部数码 m−1,…,0 的实际 quotient 根码，原参数保持不变。
有限量词块、数码图、ω 成员及互异守卫均有实际 AST 和原 Derives 出口。
只递归外部有限长度，不将模型 ω 假定为标准，不调用完整源理论的数码存在性，
也不在 Type 层选择模型相关的 ω 或标签。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteNumeralTags

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 固定外部数码的实际根码；编码参数显式传入，不选择全局 ω。 -/
def value_l (K : source_coding_l hℳ) (k : Nat) : SecondOrderQuotient.type_l hℳ :=
  (numberCode_l K (SecondOrderProgramArithmetic.numeral_val_l k)).val

theorem injective_l (K : source_coding_l hℳ) : Function.Injective (value_l K) := by
  intro i j h
  exact SecondOrderNumeralBounds.numeral_val_injective_l hℳ
    (numberCode_injective_l K (Subtype.ext h))

/-- 与调用处同一个实际 ω 对齐；覆盖模型全部内部自然数。 -/
theorem member_l (K : source_coding_l hℳ) {ω : SecondOrderQuotient.type_l hℳ}
    (hω : SecondOrderOmega.omega_l hℳ ω) (k : Nat) : mem_l hℳ (value_l K k) ω := by
  have h : mem_l hℳ (value_l K k) K.omega :=
    (numberCode_l K (SecondOrderProgramArithmetic.numeral_val_l k)).property
  exact Eq.mp (congrArg (fun w => mem_l hℳ (value_l K k) w)
    (SecondOrderOmega.unique_l hℳ K.omega_spec hω)) h

private theorem zero_unique_l {a b : SecondOrderQuotient.type_l hℳ}
    (ha : PowerlessNatural.zero_l (ℳ := 𝒱) a)
    (hb : PowerlessNatural.zero_l (ℳ := 𝒱) b) : a = b := by
  apply SecondOrderQuotient.ext_l hℳ
  intro x
  exact ⟨fun h => (ha x h).elim, fun h => (hb x h).elim⟩

/-- 数码关系通过 quotient 的真实零／后继规格证明，不假定源 Collection。 -/
theorem numeral_l (K : source_coding_l hℳ) {e : SecondOrderQuotient.type_l hℳ}
    (he : PowerlessNatural.zero_l (ℳ := 𝒱) e) (k : Nat) :
    PowerlessNumeral.numeral_l (ℳ := 𝒱) e k (value_l K k) := by
  induction k with
  | zero =>
    exact zero_unique_l (PowerlessBMSQuotientSuccessor.zero_l K) he
  | succ k ih =>
    refine ⟨value_l K k, ih, ?_⟩
    exact PowerlessBMSQuotientSuccessor.successor_l K
      (SecondOrderProgramArithmetic.numeral_val_l k)

/-- 首槽对应 m−1，后续槽依次递减；该编号只用于有限 AST。 -/
def index_m : (m : Nat) → Variable (List.replicate m .set : SortContext ℒ) .set → Nat
  | 0, v => nomatch v
  | m + 1, .here => m
  | m + 1, .there v => index_m m v

def prefix_m (Δ : SortContext ℒ) :
    (m : Nat) → Variable (List.replicate m .set : SortContext ℒ) .set →
      Variable (List.replicate m .set ++ Δ) .set
  | 0, v => nomatch v
  | m + 1, .here => .here
  | m + 1, .there v => .there (prefix_m Δ m v)

/-- 无选择的实际有限值列，供原 SourceTuple 环境直接使用。 -/
def values_l (K : source_coding_l hℳ) :
    (m : Nat) → Values (𝒱).Carrier (List.replicate m SetTheory.SetSort.set)
  | 0 => .nil
  | m + 1 => .cons (value_l K m) (values_l K m)

theorem prefix_l (K : source_coding_l hℳ) {Δ : SortContext ℒ} (η : Env 𝒱 [] Δ)
    (m : Nat) (v : Variable (List.replicate m .set : SortContext ℒ) .set) :
    (PowerlessSourceTuple.env_l η m (values_l K m)).freeVal (prefix_m Δ m v) =
      value_l K (index_m m v) := by
  match m, v with
  | 0, v => nomatch v
  | m + 1, .here => rfl
  | m + 1, .there v => exact prefix_l K η m v

/-- 加入标签后，原参数值逐项保持。 -/
theorem parameter_l (K : source_coding_l hℳ) {Δ : SortContext ℒ} (η : Env 𝒱 [] Δ)
    (m : Nat) (v : Variable Δ .set) :
    (PowerlessSourceTuple.env_l η m (values_l K m)).freeVal
      (PowerlessSourceOpening.skip_m m v) = η.freeVal v :=
  PowerlessSourceOpening.skip_l η m (values_l K m) v

theorem bounded_l (K : source_coding_l hℳ) {ω : SecondOrderQuotient.type_l hℳ}
    (hω : SecondOrderOmega.omega_l hℳ ω) (m : Nat) :
    PowerlessSourceTuple.bounded_l (ℳ := 𝒱) ω m (values_l K m) := by
  induction m with
  | zero => trivial
  | succ m ih => exact ⟨member_l K hω m, ih⟩

private theorem tag_value_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (η : Env 𝒱 [] Δ) (m : Nat) {v : Variable (List.replicate m .set ++ Δ) .set}
    (hv : v ∈ PowerlessSourceRequestParameters.tags_m Δ m) :
    ∃ i : Nat, i < m ∧
      (PowerlessSourceTuple.env_l η m (values_l K m)).freeVal v = value_l K i := by
  induction m with
  | zero => simp only [PowerlessSourceRequestParameters.tags_m, List.not_mem_nil] at hv
  | succ m ih =>
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ⟨m, Nat.lt_succ_self m, rfl⟩
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
      obtain ⟨i, hi, h⟩ := ih hw
      exact ⟨i, Nat.lt_trans hi (Nat.lt_succ_self m), h⟩

/-- 真实标签值互异，而不只是标签变量在语法上无重复。 -/
theorem distinct_l (K : source_coding_l hℳ) {Δ : SortContext ℒ} (η : Env 𝒱 [] Δ)
    (m : Nat) : List.Pairwise
      (fun v w => (PowerlessSourceTuple.env_l η m (values_l K m)).freeVal v ≠
        (PowerlessSourceTuple.env_l η m (values_l K m)).freeVal w)
      (PowerlessSourceRequestParameters.tags_m Δ m) := by
  induction m with
  | zero => exact List.Pairwise.nil
  | succ m ih =>
    rw [PowerlessSourceRequestParameters.tags_m, List.pairwise_cons]
    constructor
    · intro v hv h
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
      obtain ⟨i, hi, h₁⟩ := tag_value_l K η m hw
      have h₂ : m = i := injective_l K (h.trans h₁)
      exact (Nat.ne_of_lt hi) h₂.symm
    · exact List.pairwise_map.mpr ih

/-- 若同一 C 包含实际 ω 和原参数，增广后的全部参数仍属于 C。 -/
theorem parameters_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (η : Env 𝒱 [] Δ) (m : Nat) {ω C : SecondOrderQuotient.type_l hℳ}
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hωC : ∀ x, mem_l hℳ x ω → mem_l hℳ x C)
    (hParams : ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v) C) :
    ∀ s (v : Variable (List.replicate m .set ++ Δ) s),
      mem_l hℳ ((PowerlessSourceTuple.env_l η m (values_l K m)).freeVal v) C := by
  induction m with
  | zero => exact hParams
  | succ m ih =>
    intro s v
    cases s
    cases v with
    | here => exact hωC _ (member_l K hω m)
    | there v => exact ih _ v

/-- 纯 numeral 图和每个标签的 ω 成员守卫。 -/
def form_m {Γ Ε : SortContext ℒ} : (m : Nat) →
    Term ℒ Γ Ε .set → Term ℒ Γ Ε .set →
    (Variable (List.replicate m .set : SortContext ℒ) .set → Term ℒ Γ Ε .set) → Formula ℒ Γ Ε
  | 0, _, _, _ => .truth
  | m + 1, ω, e, τ => .conj (PowerlessNumeral.numeral_m m e (τ .here)) <|
      .conj (SecondOrderObjectSyntax.member_m (τ .here) ω)
        (form_m m ω e (fun v => τ (.there v)))

theorem formula_l (K : source_coding_l hℳ) {Γ Ε : SortContext ℒ} (m : Nat)
    (ζ : Env 𝒱 Γ Ε) (ω e : Term ℒ Γ Ε .set)
    (τ : Variable (List.replicate m .set : SortContext ℒ) .set → Term ℒ Γ Ε .set)
    (hω : SecondOrderOmega.omega_l hℳ (ω.eval ζ))
    (he : PowerlessNatural.zero_l (ℳ := 𝒱) (e.eval ζ))
    (hτ : ∀ v, (τ v).eval ζ = value_l K (index_m m v)) :
    (form_m m ω e τ).satisfies ζ := by
  induction m with
  | zero => trivial
  | succ m ih =>
    change _ ∧ _ ∧ _
    refine ⟨(PowerlessNumeral.formula_l ζ m e (τ .here)).mpr ?_, ?_, ?_⟩
    · rw [hτ .here]
      exact numeral_l K he m
    · change mem_l hℳ ((τ .here).eval ζ) (ω.eval ζ)
      rw [hτ .here]
      exact member_l K hω m
    · exact ih (fun v => τ (.there v)) (fun v => hτ (.there v))

/-- 外部有限个自由首槽逐个转成原存在量词，原 Δ 完全不变。 -/
def exists_m {Δ : SortContext ℒ} : (m : Nat) →
    Formula ℒ [] (List.replicate m .set ++ Δ) → Formula ℒ [] Δ
  | 0, φ => φ
  | m + 1, φ => exists_m m (φ.existsFreeTop .set)

theorem exists_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (m : Nat) (φ : Formula ℒ [] (List.replicate m .set ++ Δ)) (η : Env 𝒩 [] Δ) :
    (exists_m m φ).satisfies η ↔ ∃ v : Values 𝒩.Carrier (List.replicate m .set),
      φ.satisfies (PowerlessSourceTuple.env_l η m v) := by
  induction m with
  | zero =>
    constructor
    · intro h; exact ⟨.nil, h⟩
    · rintro ⟨v, h⟩; cases v; exact h
  | succ m ih =>
    rw [exists_m, ih]
    simp only [Formula.satisfies_existsFreeTop]
    constructor
    · rintro ⟨v, x, h⟩; exact ⟨.cons x v, h⟩
    · rintro ⟨v, h⟩; cases v with
      | cons x v => exact ⟨v, x, h⟩

def zero_m {Γ Δ : SortContext ℒ} (e : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.neg (SecondOrderObjectSyntax.member_m (.bvar .here)
    (e.weakenBound SetTheory.SetSort.set)))

theorem zero_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (e : Term ℒ Γ Δ .set) :
    (zero_m e).satisfies η ↔ PowerlessNatural.zero_l (e.eval η) := by
  simp only [zero_m, Formula.satisfies, SecondOrderObjectSyntax.member_m, Arguments.eval,
    Term.eval_weakenBound]
  rfl

def payload_m {Δ : SortContext ℒ} (m : Nat) (ω e : Term ℒ [] Δ .set) :
    Formula ℒ [] (List.replicate m .set ++ Δ) :=
  .conj (form_m m (PowerlessSourceRequestParameters.term_m 0 m ω)
    (PowerlessSourceRequestParameters.term_m 0 m e) (fun v => .fvar (prefix_m Δ m v)))
    (PowerlessRelativeSourceSkolemFamily.distinct_m (PowerlessSourceRequestParameters.tags_m Δ m)
      (fun v => .fvar v))

def schema_m {Δ : SortContext ℒ} (m : Nat) (ω e : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <| .imp (zero_m e) (exists_m m (payload_m m ω e))

def sentence_m {Δ : SortContext ℒ} (m : Nat) (ω e : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m m ω e)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} (m : Nat) (ω e : Term ℒ [] Δ .set) :
    (sentence_m m ω e).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hω he
  have hω := (SecondOrderOmegaSyntax.omega_l hℳ η ω).mp hω
  have he := (zero_formula_l η e).mp he
  apply (exists_formula_l m (payload_m m ω e) η).mpr
  refine ⟨values_l K m, ?_⟩
  let ζ := PowerlessSourceTuple.env_l η m (values_l K m)
  have ht (t : Term ℒ [] Δ .set) :
      (PowerlessSourceRequestParameters.term_m 0 m t).eval ζ = t.eval η :=
    PowerlessSourceRequestParameters.term_l η 0 m .nil (values_l K m) t
  change _ ∧ _
  constructor
  · exact formula_l K m ζ _ _ (fun v => .fvar (prefix_m Δ m v))
      (by simpa only [ht] using hω) (by simpa only [ht] using he) (prefix_l K η m)
  · exact (PowerlessRelativeSourceSkolemFamily.distinct_formula_l
      (PowerlessSourceRequestParameters.tags_m Δ m) (fun v => .fvar v) ζ).mpr (distinct_l K η m)

theorem derives_m {Δ : SortContext ℒ} (m : Nat) (ω e : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m m ω e)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 m ω e)

#print axioms injective_l
#print axioms numeral_l
#print axioms parameters_l
#print axioms distinct_l
#print axioms exists_formula_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteNumeralTags
