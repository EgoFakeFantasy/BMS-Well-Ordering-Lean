import BMSConstructibleBridge.PowerlessRelativeCutoffLocalHistoryBudget
import BMSConstructibleBridge.PowerlessRelativeCutoffHistoryImage
import BMSConstructibleBridge.PowerlessSatisfactionFunctionGraph
import BMSConstructibleBridge.PowerlessRelativeClassInstantiation

/-! # 实际局部前史与同见证截断闭包像的共同装配

对象语言为纯隶属 ℒ，背景为原 Z₂，正式出口为原推导核的图翻译句。
先消费旧局部构造实际给出的 β/U/D/f，再以同一 B/D/A/U 作为指定
参数构造完整原截断闭包像。f 只是装配项，不加入种子；原预算、轻量
历史、捕获证书和全部原图规格保留。历史守卫在共同结论中实际成立，
最内层同一个 I 明确含 f；不把任何 β/U/D/f 的存在、图规格或成员性
加回调用端。原首不可数截断给出 W 的非零极限资格，真实基础闭包
和原 ω 资格保留在共同存在句中，供同一 I 的全部内部有限赋值使用。
原种子公理给出的 B 传递性亦保留，实际末端的同一 I 因此具备已证
坍缩存在的全部资格；不把未知坍缩图或源理论加回调用端。
指定参数另外增加原 X 和 ω；X 的 W 成员资格原本已在输入中，ω 的
资格由同一实际 U 的成员性和 W 传递性给出，故不增加调用假设。
原 X、ω 与 B/D/A/U 及原 Δ 的所有参数共同属于同一个实际 I。
同一 β/U 的完整静态编码包及实际 Sat 图亦在证明内取得，再作为指定
参数进入这一个 I；静态类规格和全部 raw 规范矩阵读数保留为纯对象公式。
不将 G∈Def²(U) 直接认作 G∈U；两次严格较早后继界给出 G∈W。
原包中的旧翻译图 Q 也作为同一实际参数捕获；Q∈U 不被误用为 Q∈I。

本模块尚不完成 Def 截迹、弱凝聚、Collection 或最终候选源存在性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffLocalHistoryImage

open Logic FirstOrder SecondOrderObjectSyntax PowerlessBMSQuotientCoding
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct
  PowerlessRelativeClassStructure.structure_l
attribute [local irreducible] PowerlessRelativeSourceFamilyHistory.family_m

universe u

private abbrev free {Θ : SortContext ℒ} (t : Term ℒ [] Θ .set) :=
  t.weakenFree SetTheory.SetSort.set
/-- 编码槽依次为 G/F/N/T/t₃/t₂/t₁/e/Q，与外层存在量词顺序相反。 -/
abbrev coding_m : SortContext ℒ := [.set, .set, .set, .set, .set, .set, .set, .set, .set]

private abbrev lift₄ {Θ : SortContext ℒ} (t : Term ℒ [] Θ .set) :=
  free (free (free (free t)))
private abbrev frame_m {Θ : SortContext ℒ} (t : Term ℒ [] Θ .set) :=
  lift₄ (_root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m coding_m t)

abbrev context_m (Θ : SortContext ℒ) := .set :: .set :: .set :: .set :: (coding_m ++ Θ)

private def code_m {Θ : SortContext ℒ} (v : Variable coding_m .set) :
    Term ℒ [] (context_m Θ) .set :=
  lift₄ (_root_.YesMetaZFC.Automation.PrefixQuantification.entry_m v)

private def coding_binding_m {Θ Δ : SortContext ℒ} (τ : VariableSubstitution ℒ Δ [] Θ) :
    Variable (coding_m ++ Δ) .set → Term ℒ [] (context_m Θ) .set
  | .here => code_m .here
  | .there .here => code_m (.there .here)
  | .there (.there .here) => code_m (.there (.there .here))
  | .there (.there (.there .here)) => code_m (.there (.there (.there .here)))
  | .there (.there (.there (.there .here))) => code_m (.there (.there (.there (.there .here))))
  | .there (.there (.there (.there (.there .here)))) =>
      code_m (.there (.there (.there (.there (.there .here)))))
  | .there (.there (.there (.there (.there (.there .here))))) =>
      code_m (.there (.there (.there (.there (.there (.there .here))))))
  | .there (.there (.there (.there (.there (.there (.there .here)))))) =>
      code_m (.there (.there (.there (.there (.there (.there (.there .here)))))))
  | .there (.there (.there (.there (.there (.there (.there (.there .here))))))) =>
      code_m (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
  | .there (.there (.there (.there (.there (.there (.there (.there (.there v)))))))) => frame_m (τ v)

private def static_m : Formula ℒ [] (.set :: coding_m) :=
  let c (v : Variable coding_m .set) : Term ℒ [] (.set :: coding_m) .set := .fvar (.there v)
  PowerlessSatisfactionExistenceSyntax.static_m (.fvar .here)
    (c (.there (.there (.there (.there (.there (.there (.there .here))))))))
    (c (.there (.there (.there (.there (.there (.there .here)))))))
    (c (.there (.there (.there (.there (.there .here))))))
    (c (.there (.there (.there (.there .here)))))
    (c (.there (.there (.there .here)))) (c (.there (.there .here))) (c (.there .here))

private def static_binding_m {Θ : SortContext ℒ} (ω : Term ℒ [] Θ .set) :
    VariableSubstitution ℒ (.set :: coding_m) [] (context_m Θ)
  | _, .here => frame_m ω
  | _, .there v => code_m v

def coding_packet_m {Θ : SortContext ℒ} (B ω W : Term ℒ [] Θ .set)
    (U : Term ℒ [] (context_m Θ) .set) :
    Formula ℒ [] (context_m Θ) :=
  .conj (parameters_m coding_m (frame_m W) (fun v => code_m v)) <|
    .conj (parameters_m coding_m.tail U (fun v => code_m (.there v))) <|
      .conj (PowerlessRelativeClassInstantiation.formula_m (frame_m B) static_m
        (static_binding_m ω))
        (PowerlessSatisfactionFunctionGraph.graph_m (frame_m ω)
          (code_m (.there (.there (.there (.there (.there (.there (.there .here))))))))
          (code_m (.there (.there (.there (.there (.there (.there .here)))))))
          (code_m (.there (.there (.there (.there (.there .here))))))
          (code_m (.there (.there (.there (.there .here)))))
          (code_m (.there (.there (.there .here)))) (code_m (.there (.there .here)))
          (code_m (.there .here)) U (code_m .here))

/-- 四个实际见证依次为 β/U/D/f；X、ω 加入参数，f 仍不加入种子。 -/
def binding_m {Θ Δ : SortContext ℒ} (B X ω A : Term ℒ [] Θ .set)
    (τ : VariableSubstitution ℒ Δ [] Θ) :
    Variable (PowerlessRelativeSourceFamilyHistory.context_m (.set :: .set :: (coding_m ++ Δ))) .set →
      Term ℒ [] (context_m Θ) .set
  | .here => frame_m B
  | .there .here => .fvar (.there .here)
  | .there (.there .here) => frame_m A
  | .there (.there (.there .here)) => .fvar (.there (.there .here))
  | .there (.there (.there (.there .here))) => frame_m X
  | .there (.there (.there (.there (.there .here)))) => frame_m ω
  | .there (.there (.there (.there (.there (.there v))))) => coding_binding_m τ v

def history_m {Γ Θ : SortContext ℒ} (B D A U W f : Term ℒ Γ Θ .set) : Formula ℒ Γ Θ :=
  .conj (PowerlessRelativeHierarchySyntax.history_m B A f U) <|
    .conj (PowerlessHierarchyLightHistory.formula_m B D A U f) <|
      .conj (member_m f W) (PowerlessRelativeCutoffLocalHistoryBudget.capture_m B D A U W f)

/-- 完整保留旧局部存在结论的字段，只将同一个历史见证显式开放。 -/
def packet_m {Γ Θ Δ : SortContext ℒ} (B ω Ω W X A β U D f : Term ℒ Γ Θ .set)
    (τ : VariableSubstitution ℒ Δ Γ Θ) : Formula ℒ Γ Θ :=
  .conj (member_m β Ω) <| .conj (member_m A β) <|
    .conj (PowerlessRelativeHierarchySyntax.limit_m β) <|
      .conj (PowerlessRelativeCofinalLimitBounds.cofinal_m β) <|
        .conj (PowerlessRelativeHierarchySyntax.level_m B β U) <|
          .conj (member_m U W) <| .conj (member_m B U) <| .conj (member_m X U) <|
            .conj (member_m ω U) <| .conj (member_m D W) <|
              .conj (PowerlessRelativeCofinalDefGraph.graph_m U D) <|
                .conj (parameters_m Δ U τ) <| .conj (history_m B D A U W f)
                  (PowerlessRelativeCutoffHistoryBudget.result_m B Ω U D β)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem history_formula_l {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
    (K : source_coding_l hℳ) {Γ Θ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Θ) (B D A U W f : Term ℒ Γ Θ .set) :
    (history_m B D A U W f).satisfies η ↔
      PowerlessRelativeHierarchySemantics.history_l hℳ (B.eval η) (A.eval η) (f.eval η) (U.eval η) ∧
        PowerlessHierarchyLightHistory.history_l hℳ
          (B.eval η) (D.eval η) (A.eval η) (U.eval η) (f.eval η) ∧
          SecondOrderQuotient.mem_l hℳ (f.eval η) (W.eval η) ∧
            PowerlessRelativeCutoffLocalHistoryBudget.capture_l hℳ
              (B.eval η) (D.eval η) (A.eval η) (U.eval η) (W.eval η) (f.eval η) := by
  simp only [history_m, Formula.satisfies, PowerlessRelativeHierarchySemantics.history_formula_l K,
    PowerlessHierarchyLightHistory.reading_formula_l hℳ,
    PowerlessRelativeCutoffLocalHistoryBudget.capture_formula_l hℳ,
    member_m, Arguments.eval, SecondOrderQuotient.structure_l]

def payload_m {Θ Δ : SortContext ℒ} (B ω Ω W X A t₀ t₁ t₂ : Term ℒ [] Θ .set)
    (τ : VariableSubstitution ℒ Δ [] Θ) : Formula ℒ [] (context_m Θ) :=
  let β : Term ℒ [] (context_m Θ) .set := .fvar (.there (.there (.there .here)))
  let U := .fvar (.there (.there .here))
  let D := .fvar (.there .here)
  let f := .fvar .here
  .conj (packet_m (frame_m B) (frame_m ω) (frame_m Ω) (frame_m W) (frame_m X) (frame_m A)
    β U D f (fun v => frame_m (τ v))) <|
    .conj (coding_packet_m B ω W U) <|
    .conj (PowerlessRelativeSourceFamilyHistory.guard_m (frame_m B) D (frame_m A) U (frame_m W) f) <|
      .conj (PowerlessRelativeFiniteHullAssignments.closed_m (frame_m W)) <|
        .conj (SecondOrderOmegaSyntax.omega_m (frame_m ω)) <|
          .conj (PowerlessRelativeHierarchyDerives.transitive_m (frame_m B))
          (PowerlessRelativeCutoffHistoryImage.captured_conclusion_m (Δ := .set :: .set :: (coding_m ++ Δ))
        (frame_m B) (frame_m W) (frame_m ω) (frame_m t₀) (frame_m t₁) (frame_m t₂) f (binding_m B X ω A τ))

def conclusion_m {Θ Δ : SortContext ℒ} (B ω Ω W X A t₀ t₁ t₂ : Term ℒ [] Θ .set)
    (τ : VariableSubstitution ℒ Δ [] Θ) : Formula ℒ [] Θ :=
  let φ₀ := payload_m B ω Ω W X A t₀ t₁ t₂ τ
  let φ₁ := φ₀.existsFreeTop SetTheory.SetSort.set
  let φ₂ := φ₁.existsFreeTop SetTheory.SetSort.set
  let φ₃ := φ₂.existsFreeTop SetTheory.SetSort.set
  _root_.YesMetaZFC.Automation.PrefixQuantification.exists_m coding_m
    (φ₃.existsFreeTop SetTheory.SetSort.set)

def schema_m {Θ Δ : SortContext ℒ} (B P₀ ω Ω W X A t₀ t₁ t₂ : Term ℒ [] Θ .set)
    (τ : VariableSubstitution ℒ Δ [] Θ) : Formula ℒ [] Θ :=
  .imp (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_m Θ B (fun v => .fvar v)) <|
    .imp (SecondOrderCanonicalLevelDerives.guard_m B P₀) <|
      .imp (SecondOrderOmegaSyntax.omega_m ω) <|
        .imp (PowerlessRelativeOrdinalCutoff.first_m B ω Ω) <|
          .imp (PowerlessRelativeHierarchySyntax.level_m B Ω W) <|
            .imp (member_m B W) <| .imp (member_m X W) <| .imp (member_m A Ω) <|
              .imp (parameters_m Δ W τ) <| .imp (member_m t₀ W) <|
                .imp (member_m t₁ W) <| .imp (member_m t₂ W) <|
                  .imp (PowerlessRelativeFiniteProgramInstruction.tags_m t₀ t₁ t₂)
                    (conclusion_m B ω Ω W X A t₀ t₁ t₂ τ)

def sentence_m {Θ Δ : SortContext ℒ} (B P₀ ω Ω W X A t₀ t₁ t₂ : Term ℒ [] Θ .set)
    (τ : VariableSubstitution ℒ Δ [] Θ) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B P₀ ω Ω W X A t₀ t₁ t₂ τ)

attribute [local irreducible] static_m code_m PowerlessRelativeClassInstantiation.formula_m

/-- 原编码槽和四个历史槽的弱化读值律不依赖具体模型或类谓词。 -/
private theorem free_eval_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Θ : SortContext ℒ} (η : Env 𝒩 [] Θ)
    (Q e a₁ a₂ a₃ T N F G β U D f : ThirdOrderSemantics.carrier_l 𝒩)
    (t : Term ℒ [] Θ .set) :
    (frame_m t).eval (η |>.pushFree Q |>.pushFree e |>.pushFree a₁ |>.pushFree a₂ |>.pushFree a₃
      |>.pushFree T |>.pushFree N |>.pushFree F |>.pushFree G
      |>.pushFree β |>.pushFree U |>.pushFree D |>.pushFree f) = t.eval η := by
  simp only [frame_m, lift₄, free, coding_m,
    _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree]

private theorem code_eval_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Θ : SortContext ℒ} (η : Env 𝒩 [] Θ)
    (Q e a₁ a₂ a₃ T N F G β U D f : ThirdOrderSemantics.carrier_l 𝒩)
    (v : Variable coding_m .set) :
    (code_m v).eval (η |>.pushFree Q |>.pushFree e |>.pushFree a₁ |>.pushFree a₂ |>.pushFree a₃
      |>.pushFree T |>.pushFree N |>.pushFree F |>.pushFree G
      |>.pushFree β |>.pushFree U |>.pushFree D |>.pushFree f) =
      _root_.YesMetaZFC.Automation.RelationalTranslation.valuesAssignment
        (.cons G (.cons F (.cons N (.cons T (.cons a₃ (.cons a₂ (.cons a₁ (.cons e (.cons Q .nil))))))))) v := by
  let xs : Values 𝒩.Carrier coding_m :=
    .cons G (.cons F (.cons N (.cons T (.cons a₃ (.cons a₂ (.cons a₁ (.cons e (.cons Q .nil))))))))
  simpa only [xs, code_m, lift₄, free, Term.eval_weakenFree,
    _root_.YesMetaZFC.Automation.PrefixQuantification.env_l] using
      _root_.YesMetaZFC.Automation.PrefixQuantification.entry_l η xs v

private theorem static_read_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Θ : SortContext ℒ} (B ω : Term ℒ [] Θ .set)
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] Θ)
    (hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x (B.eval η) → ∀ y,
      SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y (B.eval η))
    (K : source_coding_l hℳ)
    (ω₀ e a₁ a₂ a₃ T N F G Q : PowerlessRelativeClassStructure.type_l hℳ (B.eval η))
    (hωVal : ω₀.val = ω.eval η)
    {β U D f : SecondOrderQuotient.type_l hℳ}
    (h : PowerlessSatisfactionExistenceSyntax.static_l
      (𝒩 := PowerlessRelativeClassStructure.structure_l hℳ (B.eval η) hBase)
      ω₀ e a₁ a₂ a₃ T N F) :
    let η₀ : Env (SecondOrderQuotient.structure_l hℳ) [] (coding_m ++ Θ) :=
      η |>.pushFree Q.val |>.pushFree e.val |>.pushFree a₁.val |>.pushFree a₂.val |>.pushFree a₃.val
        |>.pushFree T.val |>.pushFree N.val |>.pushFree F.val |>.pushFree G.val
    let ζ : Env (SecondOrderQuotient.structure_l hℳ) [] (context_m Θ) :=
      (((η₀.pushFree β).pushFree U).pushFree D).pushFree f
    (PowerlessRelativeClassInstantiation.formula_m (frame_m B) static_m
      (static_binding_m ω)).satisfies ζ := by
  let η₀ : Env (SecondOrderQuotient.structure_l hℳ) [] (coding_m ++ Θ) :=
    η |>.pushFree Q.val |>.pushFree e.val |>.pushFree a₁.val |>.pushFree a₂.val |>.pushFree a₃.val
      |>.pushFree T.val |>.pushFree N.val |>.pushFree F.val |>.pushFree G.val
  let ζ : Env (SecondOrderQuotient.structure_l hℳ) [] (context_m Θ) :=
    (((η₀.pushFree β).pushFree U).pushFree D).pushFree f
  let ξ : Env (PowerlessRelativeClassStructure.structure_l hℳ (B.eval η) hBase)
      [] (.set :: coding_m) :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with
        | .set => match v with
          | .here => ω₀
          | .there (.here) => G
          | .there (.there (.here)) => F
          | .there (.there (.there (.here))) => N
          | .there (.there (.there (.there (.here)))) => T
          | .there (.there (.there (.there (.there (.here))))) => a₃
          | .there (.there (.there (.there (.there (.there (.here)))))) => a₂
          | .there (.there (.there (.there (.there (.there (.there (.here))))))) => a₁
          | .there (.there (.there (.there (.there (.there (.there (.there (.here)))))))) => e
          | .there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))) => Q }
  have hb : (frame_m B).eval ζ = B.eval η := by
    simp only [frame_m, lift₄, free, coding_m,
      _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree, ζ, η₀]
  have hσ (v : Variable (.set :: coding_m) .set) :
      (static_binding_m ω v).eval ζ = (ξ.freeVal v).val := by
    match v with
    | .here =>
        change (frame_m ω).eval ζ = ω₀.val
        exact (free_eval_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
          η Q.val e.val a₁.val a₂.val a₃.val T.val N.val F.val G.val β U D f ω).trans hωVal.symm
    | .there (.here) =>
        exact code_eval_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
          η Q.val e.val a₁.val a₂.val a₃.val T.val N.val F.val G.val β U D f (.here)
    | .there (.there (.here)) =>
        exact code_eval_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
          η Q.val e.val a₁.val a₂.val a₃.val T.val N.val F.val G.val β U D f (.there (.here))
    | .there (.there (.there (.here))) =>
        exact code_eval_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
          η Q.val e.val a₁.val a₂.val a₃.val T.val N.val F.val G.val β U D f (.there (.there (.here)))
    | .there (.there (.there (.there (.here)))) =>
        exact code_eval_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
          η Q.val e.val a₁.val a₂.val a₃.val T.val N.val F.val G.val β U D f (.there (.there (.there (.here))))
    | .there (.there (.there (.there (.there (.here))))) =>
        exact code_eval_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
          η Q.val e.val a₁.val a₂.val a₃.val T.val N.val F.val G.val β U D f (.there (.there (.there (.there (.here)))))
    | .there (.there (.there (.there (.there (.there (.here)))))) =>
        exact code_eval_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
          η Q.val e.val a₁.val a₂.val a₃.val T.val N.val F.val G.val β U D f (.there (.there (.there (.there (.there (.here))))))
    | .there (.there (.there (.there (.there (.there (.there (.here))))))) =>
        exact code_eval_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
          η Q.val e.val a₁.val a₂.val a₃.val T.val N.val F.val G.val β U D f (.there (.there (.there (.there (.there (.there (.here)))))))
    | .there (.there (.there (.there (.there (.there (.there (.there (.here)))))))) =>
        exact code_eval_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
          η Q.val e.val a₁.val a₂.val a₃.val T.val N.val F.val G.val β U D f (.there (.there (.there (.there (.there (.there (.there (.here))))))))
    | .there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))) =>
        exact code_eval_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
          η Q.val e.val a₁.val a₂.val a₃.val T.val N.val F.val G.val β U D f
            (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
  have hStatic : static_m.satisfies ξ := by
    simpa only [static_m, PowerlessSatisfactionExistenceSyntax.static_formula_l,
      ξ, Term.eval, Env.pushFree_here, Env.pushFree_there] using h
  exact (PowerlessRelativeClassInstantiation.formula_l (ℳ := ℳ) (hℳ := hℳ)
    (hBase := hBase) K static_m ξ ζ
    (frame_m B) (static_binding_m ω) hb hσ).mpr hStatic

/-- 完整编码包的纯对象读数单独核验，避免在巨大闭包句中展开静态正文。 -/
private theorem coding_packet_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Θ : SortContext ℒ} (B ω W : Term ℒ [] Θ .set)
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] Θ)
    (hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x (B.eval η) → ∀ y,
      SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y (B.eval η))
    (K : source_coding_l hℳ)
    (ω₀ e a₁ a₂ a₃ T N F G : PowerlessRelativeClassStructure.type_l hℳ (B.eval η))
    (hωVal : ω₀.val = ω.eval η)
    {β U D f : SecondOrderQuotient.type_l hℳ}
    {S : PowerlessRelativeClassStructure.type_l hℳ (B.eval η)}
    {C : SecondOrderModel.set_l ℳ}
    (hCoding : PowerlessRelativeCofinalDefCoding.spec_l (W := U) hBase K
      ω₀ e a₁ a₂ a₃ T N F S G C)
    (hGW : SecondOrderQuotient.mem_l hℳ G.val (W.eval η))
    (hSubU : ∀ x, SecondOrderQuotient.mem_l hℳ x U →
      SecondOrderQuotient.mem_l hℳ x (W.eval η)) :
    let η₀ : Env (SecondOrderQuotient.structure_l hℳ) [] (coding_m ++ Θ) :=
      η |>.pushFree S.val |>.pushFree e.val |>.pushFree a₁.val |>.pushFree a₂.val |>.pushFree a₃.val
        |>.pushFree T.val |>.pushFree N.val |>.pushFree F.val |>.pushFree G.val
    let ζ : Env (SecondOrderQuotient.structure_l hℳ) [] (context_m Θ) :=
      (((η₀.pushFree β).pushFree U).pushFree D).pushFree f
    (coding_packet_m B ω W (.fvar (.there (.there .here)))).satisfies ζ := by
  let η₀ : Env (SecondOrderQuotient.structure_l hℳ) [] (coding_m ++ Θ) :=
    η |>.pushFree S.val |>.pushFree e.val |>.pushFree a₁.val |>.pushFree a₂.val |>.pushFree a₃.val
      |>.pushFree T.val |>.pushFree N.val |>.pushFree F.val |>.pushFree G.val
  let ζ : Env (SecondOrderQuotient.structure_l hℳ) [] (context_m Θ) :=
    (((η₀.pushFree β).pushFree U).pushFree D).pushFree f
  change (parameters_m coding_m (frame_m W) (fun v => code_m v)).satisfies ζ ∧
    (parameters_m coding_m.tail (.fvar (.there (.there .here))) (fun v => code_m (.there v))).satisfies ζ ∧
    (PowerlessRelativeClassInstantiation.formula_m (frame_m B) static_m
      (static_binding_m ω)).satisfies ζ ∧
    (PowerlessSatisfactionFunctionGraph.graph_m (frame_m ω)
      (code_m (.there (.there (.there (.there (.there (.there (.there .here))))))))
      (code_m (.there (.there (.there (.there (.there (.there .here)))))))
      (code_m (.there (.there (.there (.there (.there .here))))))
      (code_m (.there (.there (.there (.there .here)))))
      (code_m (.there (.there (.there .here)))) (code_m (.there (.there .here)))
      (code_m (.there .here)) (.fvar (.there (.there .here))) (code_m .here)).satisfies ζ
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (parameters_formula_l coding_m ζ (frame_m W) (fun v => code_m v)).mpr
    intro s v
    cases s
    match v with
    | .here => simpa only [code_m, frame_m, lift₄, free, coding_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.entry_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree,
        Term.eval, ζ, η₀, Env.pushFree_here, Env.pushFree_there, SecondOrderQuotient.structure_l] using hGW
    | .there (.here) => simpa only [code_m, frame_m, lift₄, free, coding_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.entry_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree,
        Term.eval, ζ, η₀, Env.pushFree_here, Env.pushFree_there, SecondOrderQuotient.structure_l] using (hSubU _ hCoding.validity_mem)
    | .there (.there (.here)) => simpa only [code_m, frame_m, lift₄, free, coding_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.entry_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree,
        Term.eval, ζ, η₀, Env.pushFree_here, Env.pushFree_there, SecondOrderQuotient.structure_l] using (hSubU _ hCoding.numbers_mem)
    | .there (.there (.there (.here))) => simpa only [code_m, frame_m, lift₄, free, coding_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.entry_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree,
        Term.eval, ζ, η₀, Env.pushFree_here, Env.pushFree_there, SecondOrderQuotient.structure_l] using (hSubU _ hCoding.pair_mem)
    | .there (.there (.there (.there (.here)))) => simpa only [code_m, frame_m, lift₄, free, coding_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.entry_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree,
        Term.eval, ζ, η₀, Env.pushFree_here, Env.pushFree_there, SecondOrderQuotient.structure_l] using (hSubU _ hCoding.tag₃_mem)
    | .there (.there (.there (.there (.there (.here))))) => simpa only [code_m, frame_m, lift₄, free, coding_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.entry_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree,
        Term.eval, ζ, η₀, Env.pushFree_here, Env.pushFree_there, SecondOrderQuotient.structure_l] using (hSubU _ hCoding.tag₂_mem)
    | .there (.there (.there (.there (.there (.there (.here)))))) => simpa only [code_m, frame_m, lift₄, free, coding_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.entry_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree,
        Term.eval, ζ, η₀, Env.pushFree_here, Env.pushFree_there, SecondOrderQuotient.structure_l] using (hSubU _ hCoding.tag₁_mem)
    | .there (.there (.there (.there (.there (.there (.there (.here))))))) => simpa only [code_m, frame_m, lift₄, free, coding_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.entry_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree,
        Term.eval, ζ, η₀, Env.pushFree_here, Env.pushFree_there, SecondOrderQuotient.structure_l] using (hSubU _ hCoding.e_mem)
    | .there (.there (.there (.there (.there (.there (.there (.there .here))))))) =>
      simpa only [code_m, frame_m, lift₄, free, coding_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.entry_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree,
        Term.eval, ζ, η₀, Env.pushFree_here, Env.pushFree_there, SecondOrderQuotient.structure_l] using (hSubU _ hCoding.translation_mem)
  · apply (parameters_formula_l coding_m.tail ζ (.fvar (.there (.there .here)))
      (fun v => code_m (.there v))).mpr
    intro s v
    cases s
    match v with
    | .here => simpa only [code_m, lift₄, free,
        _root_.YesMetaZFC.Automation.PrefixQuantification.entry_m, Term.eval_weakenFree,
        Term.eval, ζ, η₀, Env.pushFree_here, Env.pushFree_there, SecondOrderQuotient.structure_l] using hCoding.validity_mem
    | .there (.here) => simpa only [code_m, lift₄, free,
        _root_.YesMetaZFC.Automation.PrefixQuantification.entry_m, Term.eval_weakenFree,
        Term.eval, ζ, η₀, Env.pushFree_here, Env.pushFree_there, SecondOrderQuotient.structure_l] using hCoding.numbers_mem
    | .there (.there (.here)) => simpa only [code_m, lift₄, free,
        _root_.YesMetaZFC.Automation.PrefixQuantification.entry_m, Term.eval_weakenFree,
        Term.eval, ζ, η₀, Env.pushFree_here, Env.pushFree_there, SecondOrderQuotient.structure_l] using hCoding.pair_mem
    | .there (.there (.there (.here))) => simpa only [code_m, lift₄, free,
        _root_.YesMetaZFC.Automation.PrefixQuantification.entry_m, Term.eval_weakenFree,
        Term.eval, ζ, η₀, Env.pushFree_here, Env.pushFree_there, SecondOrderQuotient.structure_l] using hCoding.tag₃_mem
    | .there (.there (.there (.there (.here)))) => simpa only [code_m, lift₄, free,
        _root_.YesMetaZFC.Automation.PrefixQuantification.entry_m, Term.eval_weakenFree,
        Term.eval, ζ, η₀, Env.pushFree_here, Env.pushFree_there, SecondOrderQuotient.structure_l] using hCoding.tag₂_mem
    | .there (.there (.there (.there (.there (.here))))) => simpa only [code_m, lift₄, free,
        _root_.YesMetaZFC.Automation.PrefixQuantification.entry_m, Term.eval_weakenFree,
        Term.eval, ζ, η₀, Env.pushFree_here, Env.pushFree_there, SecondOrderQuotient.structure_l] using hCoding.tag₁_mem
    | .there (.there (.there (.there (.there (.there (.here)))))) => simpa only [code_m, lift₄, free,
        _root_.YesMetaZFC.Automation.PrefixQuantification.entry_m, Term.eval_weakenFree,
        Term.eval, ζ, η₀, Env.pushFree_here, Env.pushFree_there, SecondOrderQuotient.structure_l] using hCoding.e_mem
    | .there (.there (.there (.there (.there (.there (.there .here)))))) =>
      simpa only [code_m, lift₄, free,
        _root_.YesMetaZFC.Automation.PrefixQuantification.entry_m, Term.eval_weakenFree,
        Term.eval, ζ, η₀, Env.pushFree_here, Env.pushFree_there, SecondOrderQuotient.structure_l] using hCoding.translation_mem
  · exact static_read_l hℳ B ω η hBase K ω₀ e a₁ a₂ a₃ T N F G S hωVal
      (β := β) (U := U) (D := D) (f := f) hCoding.static
  · apply (PowerlessSatisfactionFunctionGraph.graph_formula_l ζ _ _ _ _ _ _ _ _ _ _).mpr
    simpa only [code_m, frame_m, lift₄, free, coding_m,
      _root_.YesMetaZFC.Automation.PrefixQuantification.entry_m,
      _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree,
      Term.eval, ζ, η₀, Env.pushFree_here, Env.pushFree_there, hωVal,
      ThirdOrderSemantics.member_l, SecondOrderQuotient.structure_l] using
        And.intro hCoding.sat_map hCoding.sat_read

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Θ Δ : SortContext ℒ} (B P₀ ω Ω W X A t₀ t₁ t₂ : Term ℒ [] Θ .set)
    (τ : VariableSubstitution ℒ Δ [] Θ) :
    (sentence_m B P₀ ω Ω W X A t₀ t₁ t₂ τ).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff
    (ℳ := SecondOrderQuotient.structure_l hℳ) (schema_m B P₀ ω Ω W X A t₀ t₁ t₂ τ)).mpr
  intro η hClass hSeed hω hΩ hW hBW hXW hAΩ hParams h₀ h₁ h₂ ht
  have hSeed' := (SecondOrderCanonicalLevelDerives.guard_formula_l η B P₀).mp hSeed
  have hBase x hx y hy := hSeed'.2.1 x y hx hy
  have hBase' := (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ η B).mpr hBase
  have hOld := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff
    (ℳ := SecondOrderQuotient.structure_l hℳ)
    (PowerlessRelativeCutoffLocalHistoryBudget.schema_m B ω Ω W X A τ)).mp
    (PowerlessRelativeCutoffLocalHistoryBudget.models_l hℳ B ω Ω W X A τ) η
      hBase' hω hΩ hW hBW hXW hAΩ hParams
  simp only [PowerlessRelativeCutoffLocalHistoryBudget.result_m, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.limit_formula_l,
    PowerlessRelativeCofinalLimitBounds.cofinal_formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeCofinalDefGraph.graph_formula_l K, parameters_formula_l,
    PowerlessRelativeCutoffLocalHistoryBudget.history_formula_l K,
    PowerlessRelativeCutoffHistoryBudget.result_formula_l K,
    member_m, Arguments.eval, Term.eval_weakenBound, Term.eval,
    SecondOrderQuotient.structure_l, Env.pushBound_bound_here, Env.pushBound_bound_there] at hOld
  obtain ⟨β, U, D, hβΩ, hAβ, hLimit, hCofinal, hU, hUW, hBU, hXU, hωU,
    hDW, hGraph, hValues, ⟨f, hf, hLight, hfW, hCapture⟩, hBudget⟩ := hOld
  have hΩ' := (PowerlessRelativeOrdinalCutoff.first_formula_l K η B ω Ω).mp hΩ
  have hW' := (PowerlessRelativeHierarchySemantics.level_formula_l K η B Ω W).mp hW
  have hOuter := PowerlessRelativeCutoffLimit.limit_l K hBase
    ((SecondOrderOmegaSyntax.omega_l hℳ η ω).mp hω) hΩ'
  let ω' : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) :=
    ⟨ω.eval η, ⟨β, U, hU, hωU⟩⟩
  have hωEq : ω'.val = K.omega :=
    SecondOrderOmega.unique_l hℳ ((SecondOrderOmegaSyntax.omega_l hℳ η ω).mp hω) K.omega_spec
  obtain ⟨e, a₁, a₂, a₃, T, N, F, S, G, C, hCoding⟩ :=
    PowerlessRelativeCofinalDefCoding.exists_l hBase K hLimit hU hCofinal ω' hωU hωEq
  have hGW := PowerlessRelativeCofinalDefGraph.satisfaction_member_l K hBase
    hLimit hU hOuter hW' hβΩ hωU hCoding
  have hSubU := PowerlessRelativeLevelClosure.subset_l hℳ hBase hβΩ hU hW'
  simp only [conclusion_m, _root_.YesMetaZFC.Automation.PrefixQuantification.exists_m,
    coding_m, Formula.satisfies_existsFreeTop]
  refine ⟨S.val, e.val, a₁.val, a₂.val, a₃.val, T.val, N.val, F.val, G.val, β, U, D, f, ?_⟩
  let η₀ : Env (SecondOrderQuotient.structure_l hℳ) [] (coding_m ++ Θ) :=
    η |>.pushFree S.val |>.pushFree e.val |>.pushFree a₁.val |>.pushFree a₂.val |>.pushFree a₃.val
      |>.pushFree T.val |>.pushFree N.val |>.pushFree F.val |>.pushFree G.val
  let ζ : Env (SecondOrderQuotient.structure_l hℳ) [] (context_m Θ) :=
    (((η₀.pushFree β).pushFree U).pushFree D).pushFree f
  change (packet_m (frame_m B) (frame_m ω) (frame_m Ω) (frame_m W) (frame_m X) (frame_m A)
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there .here)))
    (.fvar (.there .here)) (.fvar .here) (fun v => frame_m (τ v))).satisfies ζ ∧
    (coding_packet_m B ω W (.fvar (.there (.there .here)))).satisfies ζ ∧
    (PowerlessRelativeSourceFamilyHistory.guard_m (frame_m B) (.fvar (.there .here))
      (frame_m A) (.fvar (.there (.there .here))) (frame_m W) (.fvar .here)).satisfies ζ ∧
    (PowerlessRelativeFiniteHullAssignments.closed_m (frame_m W)).satisfies ζ ∧
    (SecondOrderOmegaSyntax.omega_m (frame_m ω)).satisfies ζ ∧
    (PowerlessRelativeHierarchyDerives.transitive_m (frame_m B)).satisfies ζ ∧
    (PowerlessRelativeCutoffHistoryImage.captured_conclusion_m (Δ := .set :: .set :: (coding_m ++ Δ))
      (frame_m B) (frame_m W) (frame_m ω) (frame_m t₀) (frame_m t₁) (frame_m t₂)
      (.fvar .here) (binding_m B X ω A τ)).satisfies ζ
  have hAΩ' : SecondOrderQuotient.mem_l hℳ (A.eval η) (Ω.eval η) := hAΩ
  have hA : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ))
      (A.eval η) := by
    apply SetTheory.Structure.IsOrdinal.mem hΩ'.1
    exact hAΩ'
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hW'
  have hωW : SecondOrderQuotient.mem_l hℳ (ω.eval η) (W.eval η) :=
    hTrans U hUW (ω.eval η) hωU
  have hClassW := PowerlessRelativeLevelClosure.class_l hℳ hBase hW'
  have hAW := PowerlessRelativeOrdinalCoverage.covered_l hℳ K hBase
    (Ω.eval η) (W.eval η) hW' (A.eval η) hAΩ'
  have hGuard : (PowerlessRelativeSourceFamilyHistory.guard_m (frame_m B) (.fvar (.there .here))
      (frame_m A) (.fvar (.there (.there .here))) (frame_m W) (.fvar .here)).satisfies ζ := by
    simp only [PowerlessRelativeSourceFamilyHistory.guard_m, Formula.satisfies,
      PowerlessNaturalOrder.transitive_formula_l, PowerlessRelativeCofinalDefGraph.graph_formula_l K,
      PowerlessRelativeHierarchySemantics.ordinal_formula_l,
      PowerlessRelativeHierarchySemantics.history_formula_l K,
      member_m, Arguments.eval, frame_m, lift₄, free, coding_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree, Term.eval,
      ζ, η₀, SecondOrderQuotient.structure_l]
    exact ⟨(fun x y hx hy => hTrans x hx y hy), hGraph, hA, hf, hfW⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [packet_m, Formula.satisfies,
      PowerlessRelativeHierarchySemantics.limit_formula_l,
      PowerlessRelativeCofinalLimitBounds.cofinal_formula_l,
      PowerlessRelativeHierarchySemantics.level_formula_l K,
      PowerlessRelativeCofinalDefGraph.graph_formula_l K, parameters_formula_l,
      history_formula_l K, PowerlessRelativeCutoffHistoryBudget.result_formula_l K,
      member_m, Arguments.eval, frame_m, lift₄, free, coding_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree, Term.eval,
      ζ, η₀, SecondOrderQuotient.structure_l]
    exact ⟨hβΩ, hAβ, hLimit, hCofinal, hU, hUW, hBU, hXU, hωU, hDW, hGraph,
      hValues, ⟨hf, hLight, hfW, hCapture⟩, hBudget⟩
  · exact coding_packet_l hℳ B ω W η hBase K ω' e a₁ a₂ a₃ T N F G rfl
      hCoding hGW hSubU
  · exact hGuard
  · apply (PowerlessRelativeFiniteHullAssignments.closed_formula_l ζ (frame_m W)).mpr
    simpa only [frame_m, lift₄, free, coding_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree, ζ, η₀] using
      PowerlessRelativeFiniteHullClosure.limit_closed_l hℳ hBase
        (PowerlessRelativeCutoffLimit.limit_l K hBase
          ((SecondOrderOmegaSyntax.omega_l hℳ η ω).mp hω) hΩ') hW'
  · apply (SecondOrderOmegaSyntax.omega_l hℳ ζ (frame_m ω)).mpr
    simpa only [frame_m, lift₄, free, coding_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree, ζ, η₀] using
      (SecondOrderOmegaSyntax.omega_l hℳ η ω).mp hω
  · apply (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ ζ (frame_m B)).mpr
    simpa only [frame_m, lift₄, free, coding_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree, ζ, η₀] using hBase
  · apply PowerlessRelativeCutoffHistoryImage.capture_l hℳ (Δ := .set :: .set :: (coding_m ++ Δ))
      (frame_m B) (frame_m W) (frame_m ω) (frame_m t₀) (frame_m t₁) (frame_m t₂)
      (.fvar .here) (binding_m B X ω A τ) ζ
    · simpa only [PowerlessRelativeCutoffHistoryImage.input_m, binding_m] using hGuard
    have h := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff
      (ℳ := SecondOrderQuotient.structure_l hℳ)
      (PowerlessRelativeCutoffHistoryImage.schema_m (Δ := .set :: .set :: (coding_m ++ Δ))
        (frame_m B) (frame_m P₀) (frame_m ω) (frame_m Ω) (frame_m W) (frame_m t₀) (frame_m t₁)
        (frame_m t₂) (.fvar .here) (binding_m B X ω A τ))).mp
      (PowerlessRelativeCutoffHistoryImage.models_l hℳ (Δ := .set :: .set :: (coding_m ++ Δ))
        (frame_m B) (frame_m P₀) (frame_m ω) (frame_m Ω) (frame_m W) (frame_m t₀) (frame_m t₁)
        (frame_m t₂) (.fvar .here) (binding_m B X ω A τ)) ζ
    apply h
    · apply (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_formula_l K
        (context_m Θ) ζ (frame_m B) (fun v => .fvar v)).mpr
      have hAll := (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_formula_l K
        Θ η B (fun v => .fvar v)).mp hClass
      simp only [frame_m, lift₄, free, coding_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree, ζ, η₀, Term.eval]
      intro s v
      cases s
      match v with
      | .here => exact PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hClassW hfW
      | .there .here => exact PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hClassW hDW
      | .there (.there .here) => exact PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hClassW hUW
      | .there (.there (.there .here)) =>
        exact PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
          (SetTheory.Structure.IsOrdinal.mem hΩ'.1 hβΩ)
      | .there (.there (.there (.there (.here)))) => exact G.property
      | .there (.there (.there (.there (.there (.here))))) => exact F.property
      | .there (.there (.there (.there (.there (.there (.here)))))) => exact N.property
      | .there (.there (.there (.there (.there (.there (.there (.here))))))) => exact T.property
      | .there (.there (.there (.there (.there (.there (.there (.there (.here)))))))) => exact a₃.property
      | .there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))) => exact a₂.property
      | .there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))) => exact a₁.property
      | .there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))) => exact e.property
      | .there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) => exact S.property
      | .there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there v)))))))))))) => exact hAll _ v
    · apply (SecondOrderCanonicalLevelDerives.guard_formula_l ζ (frame_m B) (frame_m P₀)).mpr
      simpa only [frame_m, lift₄, free, coding_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree, ζ, η₀] using hSeed'
    · apply (SecondOrderOmegaSyntax.omega_l hℳ ζ (frame_m ω)).mpr
      simpa only [frame_m, lift₄, free, coding_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree, ζ, η₀] using
        (SecondOrderOmegaSyntax.omega_l hℳ η ω).mp hω
    · apply (PowerlessRelativeOrdinalCutoff.first_formula_l K ζ (frame_m B) (frame_m ω) (frame_m Ω)).mpr
      simpa only [frame_m, lift₄, free, coding_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree, ζ, η₀] using hΩ'
    · apply (PowerlessRelativeHierarchySemantics.level_formula_l K ζ (frame_m B) (frame_m Ω) (frame_m W)).mpr
      simpa only [frame_m, lift₄, free, coding_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree, ζ, η₀] using hW'
    · simpa only [member_m, Formula.satisfies, Arguments.eval, frame_m, lift₄, free, coding_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m,
        Term.eval_weakenFree, ζ, η₀] using hBW
    · apply (parameters_formula_l (PowerlessRelativeSourceFamilyHistory.context_m (.set :: .set :: (coding_m ++ Δ)))
        ζ (frame_m W) (binding_m B X ω A τ)).mpr
      have hAll := (parameters_formula_l Δ η W τ).mp hParams
      intro s v
      cases s
      match v with
      | .here => simpa only [binding_m, frame_m, lift₄, free, coding_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree, ζ, η₀,
          member_m, Formula.satisfies, Arguments.eval] using hBW
      | .there .here => simpa only [binding_m, frame_m, lift₄, free, coding_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree, Term.eval,
          ζ, η₀, SecondOrderQuotient.structure_l, Env.pushFree_here, Env.pushFree_there,
          Env.pushBound_bound_here, Env.pushBound_bound_there] using hDW
      | .there (.there .here) => simpa only [binding_m, frame_m, lift₄, free, coding_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree,
          ζ, η₀, SecondOrderQuotient.structure_l] using hAW
      | .there (.there (.there .here)) => simpa only [binding_m, frame_m, lift₄, free, coding_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree,
          Term.eval, ζ, η₀, SecondOrderQuotient.structure_l, Env.pushFree_here, Env.pushFree_there,
          Env.pushBound_bound_here, Env.pushBound_bound_there] using hUW
      | .there (.there (.there (.there .here))) =>
          simpa only [binding_m, frame_m, lift₄, free, coding_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree, ζ, η₀,
            member_m, Formula.satisfies, Arguments.eval] using hXW
      | .there (.there (.there (.there (.there .here)))) =>
          simpa only [binding_m, frame_m, lift₄, free, coding_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree, ζ, η₀,
            member_m, Formula.satisfies, Arguments.eval, SecondOrderQuotient.structure_l] using hωW
      | .there (.there (.there (.there (.there (.there (.here)))))) =>
          simpa only [binding_m, coding_binding_m, code_m, frame_m, lift₄, free, coding_m,
            _root_.YesMetaZFC.Automation.PrefixQuantification.entry_m,
            _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree,
            Term.eval, ζ, η₀, Env.pushFree_here, Env.pushFree_there, SecondOrderQuotient.structure_l] using hGW
      | .there (.there (.there (.there (.there (.there (.there (.here))))))) =>
          simpa only [binding_m, coding_binding_m, code_m, frame_m, lift₄, free, coding_m,
            _root_.YesMetaZFC.Automation.PrefixQuantification.entry_m,
            _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree,
            Term.eval, ζ, η₀, Env.pushFree_here, Env.pushFree_there, SecondOrderQuotient.structure_l] using (hSubU _ hCoding.validity_mem)
      | .there (.there (.there (.there (.there (.there (.there (.there (.here)))))))) =>
          simpa only [binding_m, coding_binding_m, code_m, frame_m, lift₄, free, coding_m,
            _root_.YesMetaZFC.Automation.PrefixQuantification.entry_m,
            _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree,
            Term.eval, ζ, η₀, Env.pushFree_here, Env.pushFree_there, SecondOrderQuotient.structure_l] using (hSubU _ hCoding.numbers_mem)
      | .there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))) =>
          simpa only [binding_m, coding_binding_m, code_m, frame_m, lift₄, free, coding_m,
            _root_.YesMetaZFC.Automation.PrefixQuantification.entry_m,
            _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree,
            Term.eval, ζ, η₀, Env.pushFree_here, Env.pushFree_there, SecondOrderQuotient.structure_l] using (hSubU _ hCoding.pair_mem)
      | .there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))) =>
          simpa only [binding_m, coding_binding_m, code_m, frame_m, lift₄, free, coding_m,
            _root_.YesMetaZFC.Automation.PrefixQuantification.entry_m,
            _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree,
            Term.eval, ζ, η₀, Env.pushFree_here, Env.pushFree_there, SecondOrderQuotient.structure_l] using (hSubU _ hCoding.tag₃_mem)
      | .there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))) =>
          simpa only [binding_m, coding_binding_m, code_m, frame_m, lift₄, free, coding_m,
            _root_.YesMetaZFC.Automation.PrefixQuantification.entry_m,
            _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree,
            Term.eval, ζ, η₀, Env.pushFree_here, Env.pushFree_there, SecondOrderQuotient.structure_l] using (hSubU _ hCoding.tag₂_mem)
      | .there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))) =>
          simpa only [binding_m, coding_binding_m, code_m, frame_m, lift₄, free, coding_m,
            _root_.YesMetaZFC.Automation.PrefixQuantification.entry_m,
            _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree,
            Term.eval, ζ, η₀, Env.pushFree_here, Env.pushFree_there, SecondOrderQuotient.structure_l] using (hSubU _ hCoding.tag₁_mem)
      | .there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))) =>
          simpa only [binding_m, coding_binding_m, code_m, frame_m, lift₄, free, coding_m,
            _root_.YesMetaZFC.Automation.PrefixQuantification.entry_m,
            _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree,
            Term.eval, ζ, η₀, Env.pushFree_here, Env.pushFree_there, SecondOrderQuotient.structure_l] using (hSubU _ hCoding.e_mem)
      | .there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) =>
          simpa only [binding_m, coding_binding_m, code_m, frame_m, lift₄, free, coding_m,
            _root_.YesMetaZFC.Automation.PrefixQuantification.entry_m,
            _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree,
            Term.eval, ζ, η₀, Env.pushFree_here, Env.pushFree_there, SecondOrderQuotient.structure_l]
            using (hSubU _ hCoding.translation_mem)
      | .there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there v)))))))))))))) =>
          simpa only [binding_m, coding_binding_m, frame_m, lift₄, free, coding_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree, ζ, η₀] using hAll _ v
    · simpa only [member_m, Formula.satisfies, Arguments.eval, frame_m, lift₄, free, coding_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m,
        Term.eval_weakenFree, ζ, η₀] using h₀
    · simpa only [member_m, Formula.satisfies, Arguments.eval, frame_m, lift₄, free, coding_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m,
        Term.eval_weakenFree, ζ, η₀] using h₁
    · simpa only [member_m, Formula.satisfies, Arguments.eval, frame_m, lift₄, free, coding_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m,
        Term.eval_weakenFree, ζ, η₀] using h₂
    · simpa only [PowerlessRelativeFiniteProgramInstruction.tags_m, Formula.satisfies,
        frame_m, lift₄, free, coding_m,
        _root_.YesMetaZFC.Automation.PrefixQuantification.weaken_m, Term.eval_weakenFree, ζ, η₀] using ht

theorem derives_m {Θ Δ : SortContext ℒ} (B P₀ ω Ω W X A t₀ t₁ t₂ : Term ℒ [] Θ .set)
    (τ : VariableSubstitution ℒ Δ [] Θ) : Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m B P₀ ω Ω W X A t₀ t₁ t₂ τ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B P₀ ω Ω W X A t₀ t₁ t₂ τ)

#print axioms history_formula_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffLocalHistoryImage
