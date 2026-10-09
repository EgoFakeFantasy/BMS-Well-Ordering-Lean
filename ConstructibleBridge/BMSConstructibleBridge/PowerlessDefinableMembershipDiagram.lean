import BMSConstructibleBridge.PowerlessWeakSetInduction
import BMSConstructibleBridge.SecondOrderDefinableRelationImage
import BMSConstructibleBridge.SecondOrderRegularRelation
import BMSConstructibleBridge.PowerlessBMSQuotientCoding

/-! # 单值可定义求值的内部良基隶属图

纯隶属语言 ℒ、原 Z₂。求值关系可部分定义，其输出不要求共同集合界。
实际集合图只收集两代码间的隶属关系，不收集输出。原弱集合论的可定义
类极小元及单值性给出每个非空内部代码子集的极小元；再解码为原模型
实数图，所有根满足原无内部下降链公式。不存在外部良基或选择函数前提。
这不是全局 Skolem 壳、凝聚或完整 Collection 的已完成证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessDefinableMembershipDiagram

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def env_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Ε Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Ε) (τ : Variable Δ .set → Term ℒ Γ Ε .set) : Env 𝒩 [] Δ where
  boundVal v := nomatch v
  freeVal {s} v := match s with | .set => (τ v).eval η

private theorem env_pushBound_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Ε Δ : SortContext ℒ} (η : Env 𝒩 Γ Ε)
    (τ : Variable Δ .set → Term ℒ Γ Ε .set) (x : 𝒩.Carrier .set) :
    env_l (η.pushBound x) (fun v => up (τ v)) = env_l η τ := by
  apply Env.ext
  · intro s v; nomatch v
  · intro s v; cases s; exact Term.eval_weakenBound _ _ _

private theorem env_id_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ) :
    env_l η (fun v => .fvar v) = PowerlessBMSQuotientSubsetImageDerives.parameters_l η := by
  apply Env.ext
  · intro s v; nomatch v
  · intro s v; cases s; rfl

/-- 原首槽为输出，次槽为代码；参数代入保持原有限上下文。 -/
def at_m {Γ Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (n a : Term ℒ Γ Ε .set) (τ : Variable Δ .set → Term ℒ Γ Ε .set) : Formula ℒ Γ Ε :=
  φ.substitute (show Substitution ℒ [] (.set :: .set :: Δ) Γ Ε from
    .map (fun v => nomatch v) (fun {s} v => match s with
      | .set => match v with
        | .here => a
        | .there .here => n
        | .there (.there v) => τ v))

theorem at_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒩 Γ Ε) (n a : Term ℒ Γ Ε .set)
    (τ : Variable Δ .set → Term ℒ Γ Ε .set) :
    (at_m φ n a τ).satisfies η ↔
      φ.satisfies (((env_l η τ).pushFree (n.eval η)).pushFree (a.eval η)) := by
  refine (Formula.satisfies_substitute η _ φ).trans ?_
  apply Iff.of_eq
  apply congrArg (fun η => φ.satisfies η)
  apply Env.ext
  · intro s v; nomatch v
  · intro s v; cases s; cases v with
    | here => rfl
    | there v => cases v <;> rfl

def edge_m {Γ Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (n m : Term ℒ Γ Ε .set) (τ : Variable Δ .set → Term ℒ Γ Ε .set) : Formula ℒ Γ Ε :=
  .existsE .set <| .existsE .set <|
    .conj (at_m φ (up (up n)) (.bvar (.there .here)) (fun v => up (up (τ v)))) <|
      .conj (at_m φ (up (up m)) (.bvar .here) (fun v => up (up (τ v))))
        (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (.bvar .here))

def edge_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 [] Δ)
    (n m : 𝒩.Carrier .set) : Prop :=
  ∃ a b, φ.satisfies ((η.pushFree n).pushFree a) ∧
    φ.satisfies ((η.pushFree m).pushFree b) ∧ member_l 𝒩 a b

theorem edge_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒩 Γ Ε) (n m : Term ℒ Γ Ε .set)
    (τ : Variable Δ .set → Term ℒ Γ Ε .set) :
    (edge_m φ n m τ).satisfies η ↔ edge_l φ (env_l η τ) (n.eval η) (m.eval η) := by
  simp only [edge_m, edge_l, Formula.satisfies, at_formula_l, env_pushBound_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

private def image_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [] (.set :: .set :: Δ) :=
  .existsE .set <| .conj
    (SecondOrderObjectSyntax.member_m (.bvar .here) (.fvar (.there .here)))
    (at_m φ (.bvar .here) (.fvar .here) (fun v => .fvar (.there (.there v))))

private theorem image_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 [] Δ)
    (S a : 𝒩.Carrier .set) :
    (image_m φ).satisfies ((η.pushFree S).pushFree a) ↔
      ∃ n, member_l 𝒩 n S ∧ φ.satisfies ((η.pushFree n).pushFree a) := by
  simp only [image_m, Formula.satisfies, at_formula_l, SecondOrderObjectSyntax.member_m,
    Arguments.eval, Term.eval]
  have hη (n : 𝒩.Carrier .set) : env_l (((η.pushFree S).pushFree a).pushBound n)
      (fun v => .fvar (.there (.there v))) = η := by
    apply Env.ext
    · intro s v; nomatch v
    · intro s v; cases s; rfl
  simp only [hη]
  rfl

def regular_m {Γ Δ : SortContext ℒ} (D R : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp
    (.conj (ThirdOrderTheory.subset_m (.bvar .here) (up D))
      (.existsE .set (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there .here)))))
    (.existsE .set <| .conj
      (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there .here)))
      (.forallE .set <| .imp
        (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there (.there .here))))
        (.neg (SecondOrderObjectSyntax.value_m (up (up (up R))) (.bvar .here)
          (.bvar (.there .here))))))

def regular_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (D R : 𝒩.Carrier .set) : Prop :=
  ∀ S, subset_l S D ∧ (∃ n, member_l 𝒩 n S) →
    ∃ n, member_l 𝒩 n S ∧ ∀ m, member_l 𝒩 m S → ¬value_l R m n

theorem regular_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ) (D R : Term ℒ Γ Δ .set) :
    (regular_m D R).satisfies η ↔ regular_l (D.eval η) (R.eval η) := by
  simp only [regular_m, regular_l, Formula.satisfies, ThirdOrderSemantics.subset_formula_l,
    ThirdOrderSemantics.value_formula_l, SecondOrderObjectSyntax.member_m,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

/-- 不先收集输出；无输出的代码为叶，其余从可定义输出类中取隶属极小元。 -/
theorem regular_of_edge_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (h𝒩 : Theory.Models 𝒩 SecondOrderWeakSetTheory.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 [] Δ) (D R : 𝒩.Carrier .set)
    (hUnique : ∀ n a b, member_l 𝒩 n D → φ.satisfies ((η.pushFree n).pushFree a) →
      φ.satisfies ((η.pushFree n).pushFree b) → a = b)
    (hEdge : ∀ n m, member_l 𝒩 n D → member_l 𝒩 m D → value_l R n m → edge_l φ η n m) :
    regular_l D R := by
  classical
  intro S ⟨hSub, hSome⟩
  by_cases hAll : ∀ n, member_l 𝒩 n S → ∃ a, φ.satisfies ((η.pushFree n).pushFree a)
  · obtain ⟨n, hn⟩ := hSome
    obtain ⟨a, ha⟩ := hAll n hn
    obtain ⟨a, ha, hMin⟩ := PowerlessWeakSetInduction.minimum_l h𝒩 (image_m φ)
      (η.pushFree S) ⟨a, (image_formula_l φ η S a).mpr ⟨n, hn, ha⟩⟩
    obtain ⟨n, hn, hna⟩ := (image_formula_l φ η S a).mp ha
    refine ⟨n, hn, fun m hm hmn => ?_⟩
    obtain ⟨b, c, hmb, hnc, hbc⟩ := hEdge m n (hSub m hm) (hSub n hn) hmn
    obtain rfl := hUnique n c a (hSub n hn) hnc hna
    exact hMin b hbc ((image_formula_l φ η S b).mpr ⟨m, hm, hmb⟩)
  · simp only [not_forall] at hAll
    obtain ⟨n, hn, hNone⟩ := hAll
    refine ⟨n, hn, fun m hm hmn => ?_⟩
    obtain ⟨_, b, _, hb, _⟩ := hEdge m n (hSub m hm) (hSub n hn) hmn
    exact hNone ⟨b, hb⟩

def relation_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [] (.set :: .set :: Δ) :=
  edge_m φ (.fvar .here) (.fvar (.there .here)) (fun v => .fvar (.there (.there v)))

theorem relation_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 [] Δ)
    (n m : 𝒩.Carrier .set) :
    (relation_m φ).satisfies ((η.pushFree m).pushFree n) ↔ edge_l φ η n m := by
  rw [relation_m, edge_formula_l]
  have hη : env_l ((η.pushFree m).pushFree n)
      (fun v => .fvar (.there (.there v))) = η := by
    apply Env.ext
    · intro s v; nomatch v
    · intro s v; cases s; rfl
  rw [hη]
  rfl

def spec_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (D R : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .iff (SecondOrderObjectSyntax.member_m (.bvar .here) (up R)) <|
    .existsE .set <| .existsE .set <|
      .conj (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (up (up (up D)))) <|
        .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up (up (up D)))) <|
          .conj (edge_m φ (.bvar (.there .here)) (.bvar .here) (fun v => .fvar v))
            (SecondOrderObjectSyntax.ordered_m (.bvar (.there .here)) (.bvar .here)
              (.bvar (.there (.there .here))))

def spec_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 [] Δ) (D R : 𝒩.Carrier .set) : Prop :=
  ∀ p, member_l 𝒩 p R ↔ ∃ n m, member_l 𝒩 n D ∧ member_l 𝒩 m D ∧
    edge_l φ η n m ∧ ordered_l n m p

theorem spec_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒩 Γ Δ) (D R : Term ℒ Γ Δ .set) :
    (spec_m φ D R).satisfies η ↔
      spec_l φ (PowerlessBMSQuotientSubsetImageDerives.parameters_l η) (D.eval η) (R.eval η) := by
  simp only [spec_m, spec_l, Formula.satisfies, edge_formula_l, env_id_l,
    PowerlessBMSQuotientSubsetImageDerives.parameters_pushBound_l,
    ThirdOrderSemantics.ordered_formula_l, SecondOrderObjectSyntax.member_m,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 实际关系只在 D×D 收集边，原任意公式的所有输出仍可无界。 -/
theorem exists_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (D : Raw)
    (hUnique : ∀ n a b, SecondOrderQuotient.mem_l hℳ n D →
      φ.satisfies ((η.pushFree n).pushFree a) → φ.satisfies ((η.pushFree n).pushFree b) → a = b) :
    ∃ R : Raw, spec_l φ η D R ∧ regular_l (𝒩 := 𝒱) D R := by
  obtain ⟨R, hR⟩ := SecondOrderDefinableRelationImage.exists_l hℳ (relation_m φ) η D D
  have hSpec : spec_l φ η D R := by
    intro p
    exact (hR p).trans (exists_congr (fun n => exists_congr (fun m =>
      and_congr Iff.rfl (and_congr Iff.rfl (and_congr (relation_formula_l φ η n m) Iff.rfl)))))
  refine ⟨R, hSpec, regular_of_edge_l (SecondOrderWeakSetTheory.models_l hℳ) φ η D R hUnique ?_⟩
  intro n m _ _ hnm
  obtain ⟨p, hp, hnm⟩ := hnm
  obtain ⟨n', m', _, _, hEdge, hPair⟩ := (hSpec p).mp hp
  obtain ⟨rfl, rfl⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hnm hPair).mp rfl
  exact hEdge

/-- 精确图规格同时给出合法两坐标及原求值输出的隶属关系。 -/
theorem value_iff_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {D R : Raw} (hR : spec_l φ η D R) (n m : Raw) :
    value_l (ℳ := 𝒱) R n m ↔
      SecondOrderQuotient.mem_l hℳ n D ∧ SecondOrderQuotient.mem_l hℳ m D ∧ edge_l φ η n m := by
  constructor
  · rintro ⟨p, hp, hnm⟩
    obtain ⟨n', m', hn, hm, hEdge, hPair⟩ := (hR p).mp hp
    obtain ⟨rfl, rfl⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hnm hPair).mp rfl
    exact ⟨hn, hm, hEdge⟩
  · rintro ⟨hn, hm, hEdge⟩
    obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ n m
    exact ⟨p, (hR p).mpr ⟨n, m, hn, hm, hEdge, hp⟩, hp⟩

/-- 同一实际集合关系解码为原实数图；所有内部数码根良基，包括无输出的叶。 -/
theorem coded_exists_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (hUnique : ∀ n a b, SecondOrderQuotient.mem_l hℳ n K.omega →
      φ.satisfies ((η.pushFree n).pushFree a) → φ.satisfies ((η.pushFree n).pushFree b) → a = b) :
    ∃ A : Raw, ∃ R : SecondOrderModel.set_l ℳ,
      spec_l φ η K.omega A ∧ regular_l (𝒩 := 𝒱) K.omega A ∧
      (∀ n m, SecondOrderPairing.relation_l R n m ↔
        edge_l φ η (numberCode_l K n).val (numberCode_l K m).val) ∧
      ∀ n, SecondOrderDomain.wf_l R n := by
  obtain ⟨A, hSpec, hRegular⟩ := exists_l φ η K.omega hUnique
  obtain ⟨a, ha⟩ := SecondOrderQuotient.surj_l hℳ A
  obtain ⟨R, hR⟩ := SecondOrderRelationDecode.exists_l hℳ K.less K.less_spec a
  rw [ha] at hR
  have hA : SecondOrderRegularRelation.regular_l hℳ A K.omega := by
    intro S hSome hField
    exact hRegular S ⟨fun n hn => (hField n hn).1, hSome⟩
  refine ⟨A, R, hSpec, hRegular, ?_, ?_⟩
  · intro n m
    refine (hR n m).trans ?_
    change value_l (ℳ := 𝒱) A (numberCode_l K n).val (numberCode_l K m).val ↔ _
    rw [value_iff_l φ η hSpec]
    exact ⟨fun h => h.2.2, fun h => ⟨(numberCode_l K n).property, (numberCode_l K m).property, h⟩⟩
  · exact SecondOrderRegularRelation.wf_l hℳ K.less R K.less_spec A K.omega
      (fun n => (numberCode_l K n).property) hR hA

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Formula ℒ [] Δ :=
  .forallE .set <| .imp (PowerlessBMSQuotientSubsetImageDerives.unique_m φ (.bvar .here)) <|
    .existsE .set <| .conj (spec_m φ (.bvar (.there .here)) (.bvar .here))
      (regular_m (.bvar (.there .here)) (.bvar .here))

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    (sentence_m φ).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, PowerlessBMSQuotientSubsetImageDerives.unique_m, Formula.satisfies,
    PowerlessBMSQuotientSubsetImageDerives.at_formula_l,
    PowerlessBMSQuotientSubsetImageDerives.parameters_pushBound_l,
    PowerlessBMSQuotientSubsetImageDerives.parameters_empty_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound, Term.eval, and_imp]
  intro D hUnique
  obtain ⟨R, hSpec, hRegular⟩ := exists_l φ η D hUnique
  refine ⟨R, ?_, ?_⟩
  · apply (spec_formula_l φ ((η.pushBound D).pushBound R) _ _).mpr
    simpa only [PowerlessBMSQuotientSubsetImageDerives.parameters_pushBound_l,
      PowerlessBMSQuotientSubsetImageDerives.parameters_empty_l, Term.eval,
      Env.pushBound_bound_here, Env.pushBound_bound_there] using hSpec
  · exact (regular_formula_l ((η.pushBound D).pushBound R) _ _).mpr hRegular

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ φ)

#print axioms regular_of_edge_l
#print axioms exists_l
#print axioms coded_exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessDefinableMembershipDiagram
