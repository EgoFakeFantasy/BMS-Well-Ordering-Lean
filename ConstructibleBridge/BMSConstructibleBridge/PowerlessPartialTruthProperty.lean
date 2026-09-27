import BMSConstructibleBridge.PowerlessRelativeParameters
import BMSConstructibleBridge.PowerlessPartialTruthZero
import BMSConstructibleBridge.PowerlessSourceParameters

/-!
# 实际部分真值完备性的内部归纳正文

原正文同时读取环境中的分类记录 D、完整求值 H 和小层中的实际公式 B。
U、D、H 不要求属于 U。归纳指标是模型内部公式码，不是外部语法树；
本模块核验正文及内部归纳接口，构造子推进条件仍须逐项证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessPartialTruthProperty

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

abbrev context_m : SortContext ℒ :=
  [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set]

def body_m (B : Formula ℒ [] PowerlessTruthOracle.context_m) :
    Formula ℒ [.set, .set, .set] context_m :=
  PowerlessRelativeParameters.instance_m B (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (fun v => match v with
    | .here => .fvar (.there .here)
    | .there .here => .fvar (.there (.there .here))
    | .there (.there .here) => .fvar (.there (.there (.there .here)))
    | .there (.there (.there .here)) => .fvar (.there (.there (.there (.there .here))))
    | .there (.there (.there (.there .here))) => .fvar (.there (.there (.there (.there (.there .here)))))
    | .there (.there (.there (.there (.there .here)))) => .fvar (.there (.there (.there (.there (.there (.there .here))))))
    | .there (.there (.there (.there (.there (.there .here))))) => .fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))
    | .there (.there (.there (.there (.there (.there (.there .here)))))) => .bvar (.there .here)
    | .there (.there (.there (.there (.there (.there (.there (.there .here))))))) => .fvar .here
    | .there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) => .bvar .here)

def property_m (B : Formula ℒ [] PowerlessTruthOracle.context_m) : Formula ℒ [] context_m :=
  .forallE .set (.forallE .set (.forallE .set (.imp
    (.conj (SecondOrderObjectSyntax.member_m (.bvar (.there (.there .here))) (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
      (.conj (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
        (SecondOrderObjectSyntax.member_m (.bvar .here) (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))
    (.imp (ThirdOrderTheory.subset_m (.bvar (.there (.there .here))) (.fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))))
      (.imp (PowerlessLevyEntry.entry_m (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
        (.fvar .here) (.bvar (.there (.there .here))) (.bvar (.there .here)))
        (.imp (.existsE .set (.conj
          (SecondOrderObjectSyntax.member_m (.bvar .here) (.fvar (.there .here)))
          (SecondOrderObjectSyntax.map_m (.bvar (.there .here)) (.bvar .here) (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))
          (.imp (PowerlessTruthSign.sign_m (.fvar (.there (.there .here))) (.fvar (.there (.there (.there (.there .here))))) (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
            (.bvar (.there .here)) (.fvar .here) (.bvar .here)) (body_m B))))))))

def env_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e T t₁ t₂ t₃ n U D H : carrier_l ℳ) :
    Env ℳ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set] :=
  (((((((((Env.empty.pushFree H).pushFree D).pushFree U).pushFree n).pushFree t₃
    ).pushFree t₂).pushFree t₁).pushFree T).pushFree e).pushFree ω

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {U : carrier_l ℳ}
  {hU₀ : ∃ x, member_l ℳ x U}

def property_l (B : Formula ℒ [] PowerlessTruthOracle.context_m)
    (ω e T t₁ t₂ t₃ n : type_l U) (D H : carrier_l ℳ) (c : type_l U) : Prop :=
  ∀ m q : type_l U, subset_l m.val n.val →
    PowerlessLevyEntry.entry_l ω.val e.val T.val D c.val m.val q.val →
    ∀ f : type_l U, (∃ k, member_l ℳ k ω.val ∧ map_l f.val k U) →
      PowerlessTruthSign.sign_l e.val t₁.val H q.val c.val f.val →
      B.satisfies (PowerlessTruthOracle.env_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ n q c f)

theorem body_l (B : Formula ℒ [] PowerlessTruthOracle.context_m)
    (ω e T t₁ t₂ t₃ n : type_l U) (D H : carrier_l ℳ) (c m q f : type_l U) :
    (body_m B).satisfies
      (((((env_l ω.val e.val T.val t₁.val t₂.val t₃.val n.val U D H).pushFree c.val
        ).pushBound m.val).pushBound q.val).pushBound f.val) ↔
      B.satisfies (PowerlessTruthOracle.env_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ n q c f) := by
  apply PowerlessRelativeParameters.instance_l
  · rfl
  · intro v
    repeat' first | rfl | cases ‹Variable _ _›

attribute [local irreducible] body_m

theorem property_formula_l (B : Formula ℒ [] PowerlessTruthOracle.context_m)
    (ω e T t₁ t₂ t₃ n : type_l U) (D H : carrier_l ℳ) (c : type_l U) :
    (property_m B).satisfies
      ((env_l ω.val e.val T.val t₁.val t₂.val t₃.val n.val U D H).pushFree c.val) ↔
      property_l (hU₀ := hU₀) B ω e T t₁ t₂ t₃ n D H c := by
  simp only [property_m, Formula.satisfies, subset_formula_l, PowerlessLevyEntry.entry_formula_l,
    map_formula_l, PowerlessTruthSign.sign_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval]
  constructor
  · intro h m q hmn he f hf hs
    exact (body_l B ω e T t₁ t₂ t₃ n D H c m q f).mp
      (h m.val q.val f.val ⟨m.property, q.property, f.property⟩ hmn he hf hs)
  · intro h m q f hU hmn he hf hs
    exact (body_l B ω e T t₁ t₂ t₃ n D H c ⟨m, hU.1⟩ ⟨q, hU.2.1⟩ ⟨f, hU.2.2⟩).mpr
      (h ⟨m, hU.1⟩ ⟨q, hU.2.1⟩ hmn he ⟨f, hU.2.2⟩ hf hs)


attribute [local irreducible] property_m

/-- 只沿模型内部代码归纳；调用者仍须证明实际构造子推进条件。 -/
theorem induction_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (B : Formula ℒ [] PowerlessTruthOracle.context_m)
    (ω e T t₁ t₂ t₃ n : type_l U) (D H : carrier_l ℳ)
    (hω : omega_l ω.val) (hU : PowerlessNaturalOrder.transitive_l U)
    (h : ∀ c : type_l U, member_l ℳ c.val ω.val →
      (∀ b : type_l U, member_l ℳ b.val c.val →
        property_l (hU₀ := hU₀) B ω e T t₁ t₂ t₃ n D H b) →
      property_l (hU₀ := hU₀) B ω e T t₁ t₂ t₃ n D H c) :
    ∀ c : type_l U, member_l ℳ c.val ω.val →
      property_l (hU₀ := hU₀) B ω e T t₁ t₂ t₃ n D H c := by
  obtain ⟨η, hη⟩ := PowerlessSourceParameters.env_exists_l
    (env_l ω.val e.val T.val t₁.val t₂.val t₃.val n.val U D H)
  have hφ (c : type_l U) :
      (property_m B).satisfies ((PowerlessComprehension.env_l η).pushFree c.val) ↔
        property_l (hU₀ := hU₀) B ω e T t₁ t₂ t₃ n D H c := by
    rw [hη]
    exact property_formula_l B ω e T t₁ t₂ t₃ n D H c
  have hI := PowerlessOrdinalInduction.induction_l hℳ (property_m B) η
    (PowerlessOmegaOrdinal.ordinal_l hℳ hω) (fun c hc hC => by
      let a : type_l U := ⟨c, hU ω.val c ω.property hc⟩
      apply (hφ a).mpr
      apply h a hc
      intro b hb
      exact (hφ b).mp (hC b.val hb))
  exact fun c hc => (hφ c).mp (hI c.val hc)


/-- 零层的实际分类记录满足上述完备性正文，不把推进条件当作假设。 -/
theorem zero_l {δ R H D : carrier_l ℳ} (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val)
    (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
    (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
    (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val δ U)
    (hδ : PowerlessStagePair.limit_l δ) (hωδ : member_l ℳ ω.val δ)
    (h𝒩 : Theory.Models (structure_l U hU₀) PowerlessFiniteStageEvaluation.theory_m)
    (h₀ : Theory.Models (structure_l U hU₀) PowerlessTruthIntroduction.theory_m)
    (hR : PowerlessEvaluationOperator.assignments_l ω.val U R)
    (hH : PowerlessEvaluationRecursion.evaluation_l ω.val e.val T.val U t₁.val t₂.val t₃.val R H)
    (hD : PowerlessLevyCertificate.certificate_l ω.val e.val T.val t₁.val t₂.val t₃.val D)
    (c : type_l U) :
    property_l (hU₀ := hU₀) (PowerlessPartialTruth.formula_m 0) ω e T t₁ t₂ t₃ e D H c := by
  intro m q hme hc f hf hs
  have hm : m.val = e.val := PowerlessNatural.zero_unique_l hℳ
    (fun x hx => ht.1 x (hme x hx)) ht.1
  rw [hm] at hc
  have hC := PowerlessLevyZero.class_l hℳ hω ht.1 hT ⟨D, hD, hc⟩
  exact (PowerlessPartialTruthZero.source_l hℳ hω ht hT hU hδ hωδ h𝒩 h₀ hR hH q c f hC hf).mpr hs

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessPartialTruthProperty
