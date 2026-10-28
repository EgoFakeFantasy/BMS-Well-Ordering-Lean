import BMSConstructibleBridge.PowerlessRelativeSourceFamilyClosedImage
import BMSConstructibleBridge.PowerlessRelativeSourceFamilyGraphExtension
import BMSConstructibleBridge.PowerlessRelativeFiniteRequestFamilyClosure
import BMSConstructibleBridge.PowerlessRelativeSourceFamilyTransport

/-! # 原有限公式族与同一个有限元素性闭包像

对象语言为纯隶属 ℒ，背景为原 Z₂；正式出口为原 Derives 的图翻译句。
实际请求包含存在矩阵与全称反例矩阵，各原公式可有不同绑定上下文。
F 与标签槽 T 由原 Φ 的全部请求内部生成，标签实值仍保留原种子守卫。
沿同一原图族构造同一个 I，在原八项完整 payload 后追加有限元素性。
全部原指定参数同时进入此 I；参数成员性保留在同一末端存在结论中。
I 与 W 只作相对化域参数，不要求 I∈W、W∈I 或原图属于 W。
本出口仍有实际层、种子与程序域守卫；真实 numeral 标签的守卫消去
及完整源模型公理不是本模块已完成的结论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceFamilyElementaryImage

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_empty_l)
open PowerlessRelativeSourceFamilyClosedImage (term_m term_formula_l frame_m frame_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l

universe u

private abbrev Entry (Ε : SortContext ℒ) := Term ℒ [] Ε .set × Term ℒ [] Ε .set
private abbrev up {Γ Ε : SortContext ℒ} (t : Term ℒ Γ Ε .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev free {Ε : SortContext ℒ} (t : Term ℒ [] Ε .set) :=
  t.weakenFree SetTheory.SetSort.set

abbrev context_m {Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ) :=
  List.replicate (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length .set ++ Δ

/-- 同一旧 I 的八项完整正文，不删去原像或原图读数的任何规格。 -/
def body_m {Ε : SortContext ℒ} (J : List (Entry Ε))
    (B C W ω Q e t₀ t₁ t₂ a P : Term ℒ [] Ε .set) : Formula ℒ [.set] Ε :=
  let φ := PowerlessRelativeFiniteProgramTaggedOperator.relation_m W J
  let I : Term ℒ [.set] Ε .set := .bvar .here
  let G := J.map (fun p => (up p.1, up p.2))
  .conj (PowerlessRelativeHierarchySyntax.class_m (up B) I) <|
    .conj (PowerlessRelativeOrdinalCutoff.countable_m (up B) (up ω) I) <|
      .conj (ThirdOrderTheory.subset_m I (up W)) <|
        .conj (PowerlessRelativeFiniteProgramEvaluationGraph.image_m φ
          (up B) (up C) (up ω) (up Q) (up e) (up t₀) (up t₁) (up t₂) (up a) (up P) I) <|
          .conj (PowerlessRelativeFiniteProgramImageRealization.conclusion_m φ
            (up B) (up C) (up ω) (up Q) (up e) (up t₀) (up t₁) (up t₂) (up a) (up P) I) <|
            .conj (PowerlessRelativeFiniteProgramImageClosure.closure_m φ (up B) I)
              (.conj (PowerlessRelativeTaggedImageClosure.tags_m I G)
                (PowerlessRelativeTaggedImageClosure.family_m I G))

/-- 实际常量程序使同一个求值像包含整个种子，不假设种子传递。 -/
theorem seed_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Ε : SortContext ℒ}
    (J : List (Entry Ε)) (B C W ω Q e t₀ t₁ t₂ a P : Term ℒ [] Ε .set)
    (ζ : Env 𝒩 [] Ε) (I : carrier_l 𝒩)
    (h : (body_m J B C W ω Q e t₀ t₁ t₂ a P).satisfies (ζ.pushBound I)) :
    subset_l (ℳ := 𝒩) (C.eval ζ) I := by
  simpa only [Formula.satisfies, SecondOrderObjectSyntax.member_m, Arguments.eval,
    up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here,
    Env.pushBound_bound_there, subset_l, ThirdOrderSemantics.member_l] using h.2.2.2.2.1.1

private def binding_m {Ε : SortContext ℒ} : Substitution ℒ [] (.set :: Ε) [.set] Ε :=
  .map (fun v => nomatch v) (fun {s} v => match s with
    | .set => match v with
      | .here => .bvar .here
      | .there v => .fvar v)

/-- 只把新增自由域槽送到旧 bound I，原装配自由参数逐项保持。 -/
def elementary_m {Δ Ε : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ) (W : Term ℒ [] Ε .set)
    (τ : Variable Δ .set → Term ℒ [] Ε .set) : Formula ℒ [.set] Ε :=
  (PowerlessRelativeFiniteElementarity.form_m Φ (.fvar .here) (free W)
    (fun v => free (τ v))).substitute binding_m

theorem elementary_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (ζ : Env 𝒩 [] Ε) (I : 𝒩.Carrier .set) :
    (elementary_m Φ W τ).satisfies (ζ.pushBound I) ↔
      (PowerlessRelativeFiniteElementarity.form_m Φ (.fvar .here) (free W)
        (fun v => free (τ v))).satisfies (ζ.pushFree I) := by
  rw [elementary_m, Formula.satisfies_substitute]
  have h : (ζ.pushBound I).pullback binding_m = ζ.pushFree I := by
    apply Env.ext
    · intro s v; nomatch v
    · intro s v; cases s; cases v <;> rfl
  rw [h]

def terminal_m {Θ Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B C W ω Q e t₀ t₁ t₂ a P : Term ℒ [] Θ .set)
    (τ : Variable (context_m Φ) .set → Term ℒ [] Θ .set)
    (σ : Variable Θ .set → Term ℒ [] Ε .set) (J : List (Entry Ε)) : Formula ℒ [] Ε :=
  let m := (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length
  .existsE .set <| .conj
    (body_m J (term_m B σ) (term_m C σ) (term_m W σ) (term_m ω σ) (term_m Q σ)
      (term_m e σ) (term_m t₀ σ) (term_m t₁ σ) (term_m t₂ σ) (term_m a σ) (term_m P σ))
    (.conj (elementary_m Φ (term_m W σ)
      (fun v => term_m (τ (PowerlessSourceOpening.skip_m m v)) σ))
      (parameters_m Δ (.bvar .here)
        (fun v => up (term_m (τ (PowerlessSourceOpening.skip_m m v)) σ))))

/-- 读取同一实际末端的元素性与参数成员性，不重新构造闭包像。 -/
theorem terminal_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Θ Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B C W ω Q e t₀ t₁ t₂ a P : Term ℒ [] Θ .set)
    (τ : Variable (context_m Φ) .set → Term ℒ [] Θ .set)
    (σ : Variable Θ .set → Term ℒ [] Ε .set) (J : List (Entry Ε)) (ζ : Env 𝒩 [] Ε) :
    (terminal_m Φ B C W ω Q e t₀ t₁ t₂ a P τ σ J).satisfies ζ ↔
      ∃ I, (body_m J (term_m B σ) (term_m C σ) (term_m W σ) (term_m ω σ)
        (term_m Q σ) (term_m e σ) (term_m t₀ σ) (term_m t₁ σ) (term_m t₂ σ)
        (term_m a σ) (term_m P σ)).satisfies (ζ.pushBound I) ∧
        (PowerlessRelativeFiniteElementarity.form_m Φ (.fvar .here) (free (term_m W σ))
          (fun v => free (term_m (τ (PowerlessSourceOpening.skip_m
            (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length v)) σ))).satisfies
          (ζ.pushFree I) ∧
        ∀ v : Variable Δ .set, member_l 𝒩
          ((term_m (τ (PowerlessSourceOpening.skip_m
            (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length v)) σ).eval ζ) I := by
  let ρ := fun v => term_m (τ (PowerlessSourceOpening.skip_m
    (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length v)) σ
  change (∃ I, (body_m J (term_m B σ) (term_m C σ) (term_m W σ) (term_m ω σ)
    (term_m Q σ) (term_m e σ) (term_m t₀ σ) (term_m t₁ σ) (term_m t₂ σ)
    (term_m a σ) (term_m P σ)).satisfies (ζ.pushBound I) ∧
    (elementary_m Φ (term_m W σ) ρ).satisfies (ζ.pushBound I) ∧
    (parameters_m Δ (.bvar .here) (fun v => up (ρ v))).satisfies (ζ.pushBound I)) ↔ _
  constructor
  · rintro ⟨I, hBody, hElem, hParams⟩
    refine ⟨I, hBody, (elementary_formula_l Φ (term_m W σ) ρ ζ I).mp hElem, ?_⟩
    have h := (parameters_formula_l Δ (ζ.pushBound I) (.bvar .here)
      (fun v => up (ρ v))).mp hParams
    intro v
    simpa only [up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, ρ, member_l] using h .set v
  · rintro ⟨I, hBody, hElem, hParams⟩
    refine ⟨I, hBody, (elementary_formula_l Φ (term_m W σ) ρ ζ I).mpr hElem, ?_⟩
    apply (parameters_formula_l Δ (ζ.pushBound I) (.bvar .here)
      (fun v => up (ρ v))).mpr
    intro s v
    cases s
    simpa only [up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, ρ, member_l] using hParams v

def conclusion_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B C W ω Q e t₀ t₁ t₂ a P R : Term ℒ [] Θ .set)
    (τ : Variable (context_m Φ) .set → Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  let Ψ := PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ
  let m := Ψ.length
  PowerlessRelativeSourceFamilyExtension.extension_m
    (terminal_m Φ B C W ω Q e t₀ t₁ t₂ a P τ)
    (PowerlessRelativeFiniteRequestFamilyClosure.family_m m Ψ)
    (PowerlessSourceRequestParameters.tags_m Δ m) B W R τ [] (fun v => .fvar v)

/-- 先对抽象公式族传输完整存在树，再实例化具体大公式族。 -/
theorem transport_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B C W ω Q e t₀ t₁ t₂ a P R : Term ℒ [] Θ .set)
    (τ : Variable (context_m Φ) .set → Term ℒ [] Θ .set)
    (ψ : ∀ {Ε : SortContext ℒ}, (Variable Θ .set → Term ℒ [] Ε .set) →
      List (Entry Ε) → Formula ℒ [] Ε)
    (hψ : ∀ {Ε : SortContext ℒ} (ζ : Env 𝒩 [] Ε)
      (σ : Variable Θ .set → Term ℒ [] Ε .set) (J : List (Entry Ε)),
      (terminal_m Φ B C W ω Q e t₀ t₁ t₂ a P τ σ J).satisfies ζ → (ψ σ J).satisfies ζ)
    (η : Env 𝒩 [] Θ) (h : (conclusion_m Φ B C W ω Q e t₀ t₁ t₂ a P R τ).satisfies η) :
    (PowerlessRelativeSourceFamilyExtension.extension_m ψ
      (PowerlessRelativeFiniteRequestFamilyClosure.family_m
        (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length
        (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ))
      (PowerlessSourceRequestParameters.tags_m Δ
        (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length)
      B W R τ [] (fun v => .fvar v)).satisfies η := by
  exact PowerlessRelativeSourceFamilyTransport.imp_l
    (terminal_m Φ B C W ω Q e t₀ t₁ t₂ a P τ) ψ hψ
    (PowerlessRelativeFiniteRequestFamilyClosure.family_m
      (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length
      (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ))
    (PowerlessSourceRequestParameters.tags_m Δ
      (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length)
    η B W R τ [] (fun v => .fvar v) h

/-- 完整闭句包装也先在抽象公式族上核验，避免装配时展开具体请求树。 -/
theorem transport_closed_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B C W ω Q e t₀ t₁ t₂ a P R : Term ℒ [] Θ .set)
    (τ : Variable (context_m Φ) .set → Term ℒ [] Θ .set)
    (ψ : ∀ {Ε : SortContext ℒ}, (Variable Θ .set → Term ℒ [] Ε .set) →
      List (Entry Ε) → Formula ℒ [] Ε)
    (hψ : ∀ {Ε : SortContext ℒ} (ζ : Env 𝒩 [] Ε)
      (σ : Variable Θ .set → Term ℒ [] Ε .set) (J : List (Entry Ε)),
      (terminal_m Φ B C W ω Q e t₀ t₁ t₂ a P τ σ J).satisfies ζ → (ψ σ J).satisfies ζ) :
    (Metatheory.Formula.forall_close (.imp (conclusion_m Φ B C W ω Q e t₀ t₁ t₂ a P R τ)
      (PowerlessRelativeSourceFamilyExtension.extension_m ψ
        (PowerlessRelativeFiniteRequestFamilyClosure.family_m
          (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length
          (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ))
        (PowerlessSourceRequestParameters.tags_m Δ
          (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length)
        B W R τ [] (fun v => .fvar v)))).TrueIn 𝒩 := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η h
  exact transport_l Φ B C W ω Q e t₀ t₁ t₂ a P R τ ψ hψ η h

def schema_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B β C W ω Q G e t₀ t₁ t₂ a S P R : Term ℒ [] Θ .set)
    (τ : Variable (context_m Φ) .set → Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  let m := (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length
  .imp (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_m Θ B (fun v => .fvar v)) <|
    .imp (frame_m B β C W ω Q e t₀ t₁ t₂ a) <|
      .imp (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m W R) <|
        .imp (parameters_m (context_m Φ) W τ) <| .imp (parameters_m (context_m Φ) C τ) <|
          .imp (PowerlessRelativeSourceSkolemFamily.distinct_m
            (PowerlessSourceRequestParameters.tags_m Δ m) τ) <|
            .imp (PowerlessRelativeFiniteProgramDomain.domain_m B ω Q S P) <|
              .imp (SecondOrderObjectSyntax.map_m G ω C) <|
                .imp (PowerlessRelativeClassEnumerationSectionDerives.onto_m G ω C) <|
                  .imp (PowerlessRelativeFiniteProgramAlphabet.alphabet_m C ω t₀ t₁ t₂ Q) <|
                    .imp (SecondOrderObjectSyntax.member_m B C)
                      (conclusion_m Φ B C W ω Q e t₀ t₁ t₂ a P R τ)

def sentence_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B β C W ω Q G e t₀ t₁ t₂ a S P R : Term ℒ [] Θ .set)
    (τ : Variable (context_m Φ) .set → Term ℒ [] Θ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m Φ B β C W ω Q G e t₀ t₁ t₂ a S P R τ)

private def tail_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (η : Env 𝒩 [] (.set :: Δ)) : Env 𝒩 [] Δ where
  boundVal v := nomatch v
  freeVal v := η.freeVal (.there v)

/-- 从实际增广环境读取全部标签值，不选择新的模型元素。 -/
private def values_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ} :
    (m : Nat) → Env 𝒩 [] (List.replicate m .set ++ Δ) →
      Values 𝒩.Carrier (List.replicate m SetTheory.SetSort.set)
  | 0, _ => .nil
  | m + 1, η => .cons (η.freeVal .here) (values_l m (tail_l η))

private theorem values_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ : SortContext ℒ} (m : Nat) :
    ∀ (ξ : Env 𝒩 [] (List.replicate m .set ++ Δ)) (η : Env 𝒩 [] Δ),
      (∀ v, η.freeVal v = ξ.freeVal (PowerlessSourceOpening.skip_m m v)) →
      ∀ (v : Variable (List.replicate m .set ++ Δ) .set),
        (PowerlessSourceTuple.env_l η m (values_l m ξ)).freeVal v = ξ.freeVal v := by
  induction m with
  | zero => intro ξ η h v; exact h v
  | succ m ih =>
    intro ξ η h v
    cases v with
    | here => rfl
    | there v => exact ih (tail_l ξ) η (fun v => h v) v

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Θ Δ : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B β C W ω Q G e t₀ t₁ t₂ a S P R : Term ℒ [] Θ .set)
    (τ : Variable (context_m Φ) .set → Term ℒ [] Θ .set) :
    (sentence_m Φ B β C W ω Q G e t₀ t₁ t₂ a S P R τ).TrueIn
      (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hParams hFrame hOrder hParamsW hParamsC hDistinct hDomain hMap hOnto hAlphabet hBC
  let Ψ := PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ
  let m := Ψ.length
  let F := PowerlessRelativeFiniteRequestFamilyClosure.family_m m Ψ
  let T := PowerlessSourceRequestParameters.tags_m Δ m
  have hLength : T.length = F.length :=
    (PowerlessSourceRequestParameters.tags_length_m Δ m).trans
      (PowerlessRelativeFiniteRequestFamilyClosure.family_length_m m Ψ).symm
  let ν : Env (SecondOrderQuotient.structure_l hℳ) [] (context_m Φ) :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with | .set => (τ v).eval η }
  have hClass := (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_formula_l
    K Θ η B (fun v => .fvar v)).mp hParams
  have hTerm (t : Term ℒ [] Θ .set) :
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (t.eval η) := by
    match t with
    | .bvar v => nomatch v
    | .fvar v => exact hClass _ v
    | .app f _ => nomatch f
  obtain ⟨hB, hβ, hW, hBW, hC, hCW, hω, hωW, hQW, he, ha, ht⟩ :=
    (frame_formula_l K η B β C W ω Q e t₀ t₁ t₂ a).mp hFrame
  have hWC := PowerlessRelativeLevelClosure.class_l hℳ hB hW
  have h := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
    (PowerlessRelativeSourceSkolemFamily.models_l hℳ F T hLength B W R τ) η
  simp only [PowerlessRelativeSourceSkolemFamily.schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval] at h
  have hAssembly := h hB hWC (hTerm R) hOrder hBW hParamsW hDistinct
  have hDomain' := (PowerlessRelativeFiniteProgramDomain.domain_formula_l K η B ω Q S P).mp hDomain
  have hMap' := (map_formula_l η G ω C).mp hMap
  have hOnto' := (PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l η G ω C).mp hOnto
  have hAlphabet' := (PowerlessRelativeFiniteProgramAlphabet.alphabet_formula_l η C ω t₀ t₁ t₂ Q).mp hAlphabet
  have hτW := (parameters_formula_l (context_m Φ) η W τ).mp hParamsW
  have hτC := (parameters_formula_l (context_m Φ) η C τ).mp hParamsC
  let χ : ∀ {Ε : SortContext ℒ}, (Variable Θ .set → Term ℒ [] Ε .set) →
      List (Entry Ε) → Formula ℒ [] Ε :=
    terminal_m Φ B C W ω Q e t₀ t₁ t₂ a P τ
  have hχ {Ε : SortContext ℒ} (ζ : Env (SecondOrderQuotient.structure_l hℳ) [] Ε)
      (B' W' R' : Term ℒ [] Ε .set)
      (τ' : Variable (context_m Φ) .set → Term ℒ [] Ε .set)
      (J : List (Entry Ε)) (σ : Variable Θ .set → Term ℒ [] Ε .set)
      (hσ : ∀ v, (σ v).eval ζ = η.freeVal v)
      (hτ' : ∀ v, (τ' v).eval ζ = ν.freeVal v)
      (hB' : B'.eval ζ = B.eval η) (hW' : W'.eval ζ = W.eval η)
      (hClass' : ∀ s (v : Variable Ε s), PowerlessRelativeClassCorrespondence.member_l hℳ
        (B'.eval ζ) (ζ.freeVal v))
      (hTags : ∀ p ∈ J, mem_l hℳ (p.1.eval ζ) (C.eval η))
      (hGraphs : List.Forall₂ (fun φ p =>
        (PowerlessRelativeSourceSkolemGraph.graph_m φ B' W' R' p.2 τ').satisfies ζ)
        (F.reverse ++ []) J)
      (hResult : (PowerlessRelativeSourceSkolemFamily.result_m B' W' J).satisfies ζ) :
      (χ σ J).satisfies ζ := by
    have hv (t : Term ℒ [] Θ .set) := term_formula_l t σ ζ η hσ
    have hMaps := (PowerlessRelativeFiniteProgramTaggedOperator.maps_formula_l W' J ζ).mp hResult.1
    have hCoherent := (PowerlessRelativeFiniteProgramTaggedOperator.coherent_formula_l J ζ).mp hResult.2.1
    have hMaps' : ∀ p ∈ J, map_l (ℳ := SecondOrderQuotient.structure_l hℳ) (p.2.eval ζ)
        ((term_m W σ).eval ζ) ((term_m W σ).eval ζ) := by
      simpa only [hv, hW'] using hMaps
    let δ := PowerlessRelativeFiniteProgramTaggedOperator.relation_m (term_m W σ) J
    have hFunctional := PowerlessRelativeFiniteProgramTaggedOperator.functional_l (term_m W σ) J ζ
      ((term_m B σ).eval ζ) hMaps' hCoherent
    have hClosed := PowerlessRelativeFiniteProgramTaggedOperator.closed_l (term_m W σ) J ζ
      ((term_m B σ).eval ζ) hMaps'
    have hGuard := (PowerlessRelativeFiniteProgramEvaluationBounded.guard_formula_l K δ ζ
      (term_m B σ) (term_m β σ) (term_m C σ) (term_m W σ) (term_m ω σ) (term_m Q σ)
      (term_m e σ) (term_m t₀ σ) (term_m t₁ σ) (term_m t₂ σ) (term_m a σ)).mpr
      (by
        simp only [PowerlessRelativeFiniteProgramEvaluationBounded.guard_l, parameters_empty_l, hv]
        exact ⟨hB, hβ, hW, hBW, hC, hCW, hω, hωW, hQW, he, ha, ht,
          by simpa only [hv] using hFunctional, by simpa only [hv] using hClosed⟩)
    have hParams' := (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_formula_l K Ε ζ
      (term_m B σ) (fun v => .fvar v)).mpr (by
        intro s v
        simpa only [hv, hB', Term.eval] using hClass' s v)
    have hDomain'' := (PowerlessRelativeFiniteProgramDomain.domain_formula_l K ζ
      (term_m B σ) (term_m ω σ) (term_m Q σ) (term_m S σ) (term_m P σ)).mpr
      (by simpa only [hv] using hDomain')
    have hMap'' := (map_formula_l ζ (term_m G σ) (term_m ω σ) (term_m C σ)).mpr
      (by simpa only [hv] using hMap')
    have hOnto'' := (PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l ζ
      (term_m G σ) (term_m ω σ) (term_m C σ)).mpr (by simpa only [hv] using hOnto')
    have hAlphabet'' := (PowerlessRelativeFiniteProgramAlphabet.alphabet_formula_l ζ
      (term_m C σ) (term_m ω σ) (term_m t₀ σ) (term_m t₁ σ) (term_m t₂ σ) (term_m Q σ)).mpr
      (by simpa only [hv] using hAlphabet')
    have hTags' := (PowerlessRelativeTaggedImageClosure.tags_formula_l ζ (term_m C σ) J).mpr
      (by simpa only [hv] using hTags)
    have hBC' : (SecondOrderObjectSyntax.member_m (term_m B σ) (term_m C σ)).satisfies ζ := by
      simpa only [SecondOrderObjectSyntax.member_m, Formula.satisfies, Arguments.eval, hv] using hBC
    have h := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
      (PowerlessRelativeTaggedSeedClosedImage.models_l hℳ J
        (term_m B σ) (term_m β σ) (term_m C σ) (term_m W σ) (term_m ω σ) (term_m Q σ)
        (term_m G σ) (term_m e σ) (term_m t₀ σ) (term_m t₁ σ) (term_m t₂ σ) (term_m a σ)
        (term_m S σ) (term_m P σ)) ζ
    simp only [PowerlessRelativeTaggedSeedClosedImage.schema_m, Formula.satisfies] at h
    have hI := h ((PowerlessRelativeFiniteProgramTaggedOperator.maps_formula_l (term_m W σ) J ζ).mpr hMaps')
      hTags' hParams' hGuard hDomain'' hMap'' hOnto'' hAlphabet'' hBC'
    change ∃ I, (body_m J (term_m B σ) (term_m C σ) (term_m W σ) (term_m ω σ)
      (term_m Q σ) (term_m e σ) (term_m t₀ σ) (term_m t₁ σ) (term_m t₂ σ)
      (term_m a σ) (term_m P σ)).satisfies (ζ.pushBound I) at hI
    obtain ⟨I, hI⟩ := hI
    have hBound : ∀ x, mem_l hℳ x I → mem_l hℳ x (W.eval η) := by
      simpa only [subset_formula_l, subset_l, ThirdOrderSemantics.member_l,
        SecondOrderQuotient.structure_l, up, Term.eval_weakenBound, Term.eval,
        Env.pushBound_bound_here, hv] using hI.2.2.1
    have hSeed : ∀ x, mem_l hℳ x (C.eval η) → mem_l hℳ x I := by
      simpa only [hv, subset_l, ThirdOrderSemantics.member_l, SecondOrderQuotient.structure_l]
        using seed_l J (term_m B σ) (term_m C σ) (term_m W σ)
        (term_m ω σ) (term_m Q σ) (term_m e σ) (term_m t₀ σ) (term_m t₁ σ)
        (term_m t₂ σ) (term_m a σ) (term_m P σ) ζ I hI
    have hClosure := (PowerlessRelativeFiniteProgramImageClosure.closure_formula_l K δ
      (ζ.pushBound I) (up (term_m B σ)) (.bvar .here)).mp hI.2.2.2.2.2.1
    have hPairI : ∀ x y, mem_l hℳ x I → mem_l hℳ y I →
        ∃ p, mem_l hℳ p I ∧ ordered_l (ℳ := SecondOrderQuotient.structure_l hℳ) x y p := by
      simpa only [Term.eval, Env.pushBound_bound_here] using hClosure.1
    have hFamily := (PowerlessRelativeTaggedImageClosure.family_formula_l (ζ.pushBound I)
      (.bvar .here) (J.map (fun p => (up p.1, up p.2)))).mp hI.2.2.2.2.2.2.2
    have hGraphClosed : ∀ p ∈ J, ∀ x, mem_l hℳ x I → ∃ y, mem_l hℳ y I ∧
        value_l (ℳ := SecondOrderQuotient.structure_l hℳ) (p.2.eval ζ) x y := by
      intro p hp x hx
      have h := (hFamily (up p.1, up p.2) (List.mem_map.mpr ⟨p, hp, rfl⟩)).1 x hx
      simpa only [up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here] using h
    have hBI : mem_l hℳ (B.eval η) I := hSeed _ hBC
    have hNonemptyI : ∃ x, mem_l hℳ x I := ⟨B.eval η, hBI⟩
    have hNonemptyW : ∃ x, mem_l hℳ x (W.eval η) := ⟨B.eval η, hBW⟩
    let ηI : Env (PowerlessMemberStructure.structure_l
        (ℳ := SecondOrderQuotient.structure_l hℳ) I hNonemptyI) [] Δ :=
      { boundVal := fun v => nomatch v
        freeVal := fun {s} v => match s with
          | .set => ⟨(τ (PowerlessSourceOpening.skip_m m v)).eval η,
              hSeed _ (hτC _ (PowerlessSourceOpening.skip_m m v))⟩ }
    let ηW := PowerlessSourceInclusion.env_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) (A := I) (U := W.eval η)
      (hA := hNonemptyI) (hU := hNonemptyW) hBound ηI
    let ξ : Env (PowerlessMemberStructure.structure_l
        (ℳ := SecondOrderQuotient.structure_l hℳ) (W.eval η) hNonemptyW) [] (context_m Φ) :=
      { boundVal := fun v => nomatch v
        freeVal := fun {s} v => match s with | .set => ⟨(τ v).eval η, hτW _ v⟩ }
    let t := values_l m ξ
    have hη : ∀ v, ηW.freeVal v = ξ.freeVal (PowerlessSourceOpening.skip_m m v) := by
      intro v
      apply Subtype.ext
      rfl
    have hRead : ∀ v, (τ' v).eval ζ = ((PowerlessSourceTuple.env_l ηW m t).freeVal v).val := by
      intro v
      rw [values_formula_l m ξ ηW hη v]
      exact hτ' v
    let d : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      (W.eval η) := ⟨B.eval η, hBW⟩
    have hRequests := PowerlessRelativeFiniteRequestFamilyClosure.closed_l
      (hW := hNonemptyW) Ψ m ζ B' (term_m β σ) W' (term_m ω σ) R' τ' J ηW t d
      (by simpa only [hB'] using hB) (by simpa only [hv] using hβ)
      (by simpa only [hB', hv] using hW) (by simpa only [hv] using hωW)
      hB' hW' hRead (by simpa only [List.append_nil] using hGraphs)
      I hBound hBI hPairI hGraphClosed
    have hOriginal := PowerlessRelativeFiniteRequestFamilyClosure.requests_l
      (hW := hNonemptyW) Φ ηW I hRequests
    have hFree : PowerlessSourceClass.free_l ηW = ηW := by
      apply Env.ext
      · intro s v; nomatch v
      · intro s v; rfl
    have hElementary := PowerlessRelativeFiniteElementarity.formula_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) (I₀ := I) (W₀ := W.eval η)
      (hI := hNonemptyI) (hW := hNonemptyW)
      Φ (ζ.pushFree I) (.fvar .here) (free (term_m W σ))
      (fun v => free (term_m (τ (PowerlessSourceOpening.skip_m m v)) σ)) ηI hBound rfl
      (by simp only [free, Term.eval_weakenFree, hv])
      (fun v => by simp only [free, Term.eval_weakenFree, hv]; rfl)
      (by
        intro p hp
        change PowerlessSourcePredicateRequests.closed_l
          (PowerlessSourceRequests.requests_m .truth p.2) (PowerlessSourceClass.free_l ηW)
          (fun x => mem_l hℳ x.val I)
        rw [hFree]
        exact hOriginal p hp)
    change ∃ I, (body_m J (term_m B σ) (term_m C σ) (term_m W σ) (term_m ω σ)
      (term_m Q σ) (term_m e σ) (term_m t₀ σ) (term_m t₁ σ) (term_m t₂ σ)
      (term_m a σ) (term_m P σ)).satisfies (ζ.pushBound I) ∧
      (elementary_m Φ (term_m W σ)
        (fun v => term_m (τ (PowerlessSourceOpening.skip_m m v)) σ)).satisfies (ζ.pushBound I) ∧
      (parameters_m Δ (.bvar .here)
        (fun v => up (term_m (τ (PowerlessSourceOpening.skip_m m v)) σ))).satisfies
          (ζ.pushBound I)
    refine ⟨I, hI, (elementary_formula_l Φ (term_m W σ)
      (fun v => term_m (τ (PowerlessSourceOpening.skip_m m v)) σ) ζ I).mpr hElementary, ?_⟩
    apply (parameters_formula_l Δ (ζ.pushBound I) (.bvar .here)
      (fun v => up (term_m (τ (PowerlessSourceOpening.skip_m m v)) σ))).mpr
    intro s v
    cases s
    simpa only [up, Term.eval_weakenBound, hv, Term.eval, Env.pushBound_bound_here,
      SecondOrderQuotient.structure_l]
      using hSeed _ (hτC _ (PowerlessSourceOpening.skip_m m v))
  change (PowerlessRelativeSourceFamilyExtension.extension_m χ F T B W R τ []
    (fun v => .fvar v)).satisfies η
  exact PowerlessRelativeSourceFamilyGraphExtension.extension_l K η ν
    (B.eval η) (W.eval η) (C.eval η) χ F [] hχ T η B W R τ [] (fun v => .fvar v)
    (fun _ => rfl) (fun _ => rfl) rfl rfl hClass
    (fun v _ => hτC _ v) (by simp) List.Forall₂.nil hAssembly

theorem derives_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B β C W ω Q G e t₀ t₁ t₂ a S P R : Term ℒ [] Θ .set)
    (τ : Variable (context_m Φ) .set → Term ℒ [] Θ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m Φ B β C W ω Q G e t₀ t₁ t₂ a S P R τ)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ hℳ => models_l hℳ Φ B β C W ω Q G e t₀ t₁ t₂ a S P R τ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceFamilyElementaryImage
