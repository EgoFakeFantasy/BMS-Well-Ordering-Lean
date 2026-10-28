import BMSConstructibleBridge.PowerlessRelativeSourceSkolemGraph
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramTaggedOperator

/-! # 同一有限源公式族的共同 Skolem 图绑定

原公式族和标签槽均为外部有限模式索引；背景为原 Z₂、语言为纯隶属 ℒ。
逐图存在性在 Prop 中作有限装配，输出为同时绑定全部实际图的对象句子。
每张图保留原矩阵的完整规格，末端同一标签算子单值、保层且有效输入总。
原参数 Δ 固定；递归增加的图变量只改变装配上下文，不进入原参数种子。
不使用 Type 选择，也不把模式索引当作内部统一真值或内部 ω 归纳。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceSkolemFamily

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev Entry (Ε : SortContext ℒ) := Term ℒ [] Ε .set × Term ℒ [] Ε .set

private abbrev free {Ε : SortContext ℒ} (t : Term ℒ [] Ε .set) :=
  t.weakenFree SetTheory.SetSort.set

private def apart_m {Ε Δ : SortContext ℒ} (t : Term ℒ [] Ε .set)
    (T : List (Variable Δ .set)) (τ : Variable Δ .set → Term ℒ [] Ε .set) : Formula ℒ [] Ε :=
  match T with
  | [] => .truth
  | v :: T => .conj (.neg (.equal t (τ v))) (apart_m t T τ)

private theorem apart_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Ε Δ : SortContext ℒ} (t : Term ℒ [] Ε .set) (T : List (Variable Δ .set))
    (τ : Variable Δ .set → Term ℒ [] Ε .set) (ζ : Env 𝒩 [] Ε) :
    (apart_m t T τ).satisfies ζ ↔ ∀ v ∈ T, t.eval ζ ≠ (τ v).eval ζ := by
  induction T with
  | nil => simp [apart_m, Formula.satisfies]
  | cons v T ih => simp [apart_m, Formula.satisfies, ih]

def distinct_m {Ε Δ : SortContext ℒ} (T : List (Variable Δ .set))
    (τ : Variable Δ .set → Term ℒ [] Ε .set) : Formula ℒ [] Ε :=
  match T with
  | [] => .truth
  | v :: T => .conj (apart_m (τ v) T τ) (distinct_m T τ)

theorem distinct_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Ε Δ : SortContext ℒ} (T : List (Variable Δ .set))
    (τ : Variable Δ .set → Term ℒ [] Ε .set) (ζ : Env 𝒩 [] Ε) :
    (distinct_m T τ).satisfies ζ ↔ List.Pairwise (fun v w => (τ v).eval ζ ≠ (τ w).eval ζ) T := by
  induction T with
  | nil => simp [distinct_m, Formula.satisfies]
  | cons v T ih => simp [distinct_m, Formula.satisfies, apart_formula_l, ih, List.pairwise_cons]

def result_m {Ε : SortContext ℒ} (B W : Term ℒ [] Ε .set) (G : List (Entry Ε)) : Formula ℒ [] Ε :=
  let δ := PowerlessRelativeFiniteProgramTaggedOperator.relation_m W G
  .conj (PowerlessRelativeFiniteProgramTaggedOperator.maps_m W G) <|
    .conj (PowerlessRelativeFiniteProgramTaggedOperator.coherent_m G) <|
      .conj (PowerlessRelativeFiniteProgramInstruction.functional_m δ B) <|
        .conj (PowerlessRelativeFiniteProgramLimitStep.closed_m δ B W)
          (PowerlessRelativeFiniteProgramTaggedOperator.total_m W G)

def assemble_m {Ε Δ : SortContext ℒ}
    (F : List (Formula ℒ [] (.set :: .set :: Δ))) (T : List (Variable Δ .set))
    (B W R : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (G : List (Entry Ε)) : Formula ℒ [] Ε :=
  match F, T with
  | List.nil, _ => result_m B W G
  | List.cons _ _, List.nil => .falsum
  | List.cons φ F, List.cons v T =>
    let J : Term ℒ [] (.set :: Ε) .set := .fvar .here
    (Formula.conj (PowerlessRelativeSourceSkolemGraph.graph_m φ (free B) (free W) (free R) J
        (fun w => free (τ w)))
      (assemble_m F T (free B) (free W) (free R) (fun w => free (τ w))
        ((free (τ v), J) :: G.map (fun p => (free p.1, free p.2))))).existsFreeTop .set

def conclusion_m {Ε Δ : SortContext ℒ}
    (F : List (Formula ℒ [] (.set :: .set :: Δ))) (T : List (Variable Δ .set))
    (B W R : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) : Formula ℒ [] Ε :=
  assemble_m F T B W R τ []

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

private theorem assemble_l {Δ : SortContext ℒ} (η : Env 𝒱 [] Δ)
    (b w r : SecondOrderQuotient.type_l hℳ)
    (hWitness : ∀ φ : Formula ℒ [] (.set :: .set :: Δ), ∃ j,
      (PowerlessRelativeSourceSkolemGraph.payload_m φ).satisfies
        ((((η.pushFree b).pushFree r).pushFree w).pushFree j))
    (F : List (Formula ℒ [] (.set :: .set :: Δ))) :
    ∀ (T : List (Variable Δ .set)) {Ε : SortContext ℒ} (ζ : Env 𝒱 [] Ε)
      (B W R : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
      (G : List (Entry Ε)), T.length = F.length → B.eval ζ = b → W.eval ζ = w → R.eval ζ = r →
      (∀ v, (τ v).eval ζ = η.freeVal v) →
      List.Pairwise (fun v u => η.freeVal v ≠ η.freeVal u) T →
      (∀ p ∈ G, map_l (ℳ := 𝒱) (p.2.eval ζ) w w) →
      (∀ p ∈ G, ∀ q ∈ G, p.1.eval ζ = q.1.eval ζ → p.2.eval ζ = q.2.eval ζ) →
      (∀ v ∈ T, ∀ p ∈ G, η.freeVal v ≠ p.1.eval ζ) →
      (assemble_m F T B W R τ G).satisfies ζ := by
  induction F with
  | nil =>
    intro T Ε ζ B W R τ G _ _ hW _ _ _ hMaps hCoherent _
    change (result_m B W G).satisfies ζ
    have hm := (PowerlessRelativeFiniteProgramTaggedOperator.maps_formula_l W G ζ).mpr
      (by simpa only [hW] using hMaps)
    have hc := (PowerlessRelativeFiniteProgramTaggedOperator.coherent_formula_l G ζ).mpr hCoherent
    have h := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
      (PowerlessRelativeFiniteProgramTaggedOperator.models_l hℳ B W G) ζ
    simp only [PowerlessRelativeFiniteProgramTaggedOperator.schema_m, Formula.satisfies] at h
    exact ⟨hm, hc, h hm hc⟩
  | cons φ F ih =>
    intro T Ε ζ B W R τ G hLength hB hW hR hτ hDistinct hMaps hCoherent hCross
    cases T with
    | nil => simp at hLength
    | cons v T =>
      have hLength' : T.length = F.length := Nat.succ.inj hLength
      obtain ⟨j, hj⟩ := hWitness φ
      let ξ : Env 𝒱 [] (.set :: Ε) := ζ.pushFree j
      let J : Term ℒ [] (.set :: Ε) .set := .fvar .here
      let G' : List (Entry (.set :: Ε)) :=
        (free (τ v), J) :: G.map (fun p => (free p.1, free p.2))
      have hf (t : Term ℒ [] Ε .set) : (free t).eval ξ = t.eval ζ := by
        simp only [free, Term.eval_weakenFree, ξ]
      have hGraph : (PowerlessRelativeSourceSkolemGraph.graph_m φ
          (free B) (free W) (free R) J (fun u => free (τ u))).satisfies ξ := by
        apply (PowerlessRelativeSourceSkolemGraph.graph_formula_l φ ξ
          (free B) (free W) (free R) J (fun u => free (τ u)) η
          (fun u => (hf (τ u)).trans (hτ u))).mpr
        simpa only [hf, hB, hW, hR, J, Term.eval, ξ, Env.pushFree_here] using hj
      have hMapj : map_l (ℳ := 𝒱) j w w :=
        (map_formula_l
          (show Env 𝒱 [] ([.set, .set, .set, .set] ++ Δ) from
            (((η.pushFree b).pushFree r).pushFree w).pushFree j)
          (.fvar .here) (.fvar (.there .here)) (.fvar (.there .here))).mp hj.2.1
      have hMaps' : ∀ p ∈ G', map_l (ℳ := 𝒱) (p.2.eval ξ) w w := by
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · simpa only [J, Term.eval, ξ, Env.pushFree_here] using hMapj
        · obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.mp hp
          simpa only [hf] using hMaps p₀ hp₀
      have hCoherent' : ∀ p ∈ G', ∀ q ∈ G',
          p.1.eval ξ = q.1.eval ξ → p.2.eval ξ = q.2.eval ξ := by
        intro p hp q hq hEq
        rcases List.mem_cons.mp hp with rfl | hp
        · rcases List.mem_cons.mp hq with rfl | hq
          · rfl
          · obtain ⟨q₀, hq₀, rfl⟩ := List.mem_map.mp hq
            exact (hCross v (by simp) q₀ hq₀ (by simpa only [hf, hτ] using hEq)).elim
        · obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.mp hp
          rcases List.mem_cons.mp hq with rfl | hq
          · exact (hCross v (by simp) p₀ hp₀ (by simpa only [hf, hτ] using hEq.symm)).elim
          · obtain ⟨q₀, hq₀, rfl⟩ := List.mem_map.mp hq
            simpa only [hf] using hCoherent p₀ hp₀ q₀ hq₀ (by simpa only [hf] using hEq)
      have hD := List.pairwise_cons.mp hDistinct
      have hCross' : ∀ u ∈ T, ∀ p ∈ G', η.freeVal u ≠ p.1.eval ξ := by
        intro u hu p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · intro hEq
          exact hD.1 u hu (by simpa only [hf, hτ] using hEq.symm)
        · obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.mp hp
          simpa only [hf] using hCross u (by simp [hu]) p₀ hp₀
      rw [assemble_m, Formula.satisfies_existsFreeTop]
      refine ⟨j, hGraph, ?_⟩
      exact ih T ξ (free B) (free W) (free R) (fun u => free (τ u)) G' hLength'
        ((hf B).trans hB) ((hf W).trans hW) ((hf R).trans hR)
        (fun u => (hf (τ u)).trans (hτ u)) hD.2 hMaps' hCoherent' hCross'

def schema_m {Ε Δ : SortContext ℒ}
    (F : List (Formula ℒ [] (.set :: .set :: Δ))) (T : List (Variable Δ .set))
    (B W R : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) : Formula ℒ [] Ε :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B W) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B R) <|
        .imp (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m W R) <|
          .imp (SecondOrderObjectSyntax.member_m B W) <|
            .imp (parameters_m Δ W τ) <| .imp (distinct_m T τ) (conclusion_m F T B W R τ)

def sentence_m {Ε Δ : SortContext ℒ}
    (F : List (Formula ℒ [] (.set :: .set :: Δ))) (T : List (Variable Δ .set))
    (B W R : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m F T B W R τ)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Ε Δ : SortContext ℒ} (F : List (Formula ℒ [] (.set :: .set :: Δ)))
    (T : List (Variable Δ .set)) (hLength : T.length = F.length)
    (B W R : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) :
    (sentence_m F T B W R τ).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  intro ζ hBase hW hR hOrder hBW hParams hDistinct
  let η : Env (SecondOrderQuotient.structure_l h𝒩) [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with | .set => (τ v).eval ζ }
  let ξ : Env (SecondOrderQuotient.structure_l h𝒩) [] (.set :: .set :: .set :: Δ) :=
    ((η.pushFree (B.eval ζ)).pushFree (R.eval ζ)).pushFree (W.eval ζ)
  have hParams' := (parameters_formula_l Δ ζ W τ).mp hParams
  have hParameters : (parameters_m Δ (.fvar .here)
      (fun v => .fvar (.there (.there (.there v))))).satisfies ξ := by
    apply (parameters_formula_l Δ ξ (.fvar .here)
      (fun v => .fvar (.there (.there (.there v))))).mpr
    intro s v; cases s
    exact hParams' _ v
  have hWitness (φ : Formula ℒ [] (.set :: .set :: Δ)) : ∃ j,
      (PowerlessRelativeSourceSkolemGraph.payload_m φ).satisfies (ξ.pushFree j) := by
    have h := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
      (PowerlessRelativeSourceSkolemGraph.models_l h𝒩 φ) ξ
    simp only [PowerlessRelativeSourceSkolemGraph.schema_m, Formula.satisfies,
      PowerlessRelativeHierarchyDerives.transitive_formula_l,
      PowerlessRelativeHierarchySemantics.class_formula_l K,
      PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
      SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval] at h
    simpa only [PowerlessRelativeSourceSkolemGraph.conclusion_m, Formula.satisfies_existsFreeTop]
      using h hBase hW hR hOrder hBW hParameters
  have hD : List.Pairwise (fun v u => η.freeVal v ≠ η.freeVal u) T :=
    (distinct_formula_l T τ ζ).mp hDistinct
  exact assemble_l η (B.eval ζ) (W.eval ζ) (R.eval ζ) hWitness F T ζ B W R τ [] hLength
    rfl rfl rfl (fun _ => rfl) hD (by simp) (by simp) (by simp)

theorem derives_m {Ε Δ : SortContext ℒ}
    (F : List (Formula ℒ [] (.set :: .set :: Δ))) (T : List (Variable Δ .set))
    (hLength : T.length = F.length) (B W R : Term ℒ [] Ε .set)
    (τ : Variable Δ .set → Term ℒ [] Ε .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m F T B W R τ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 F T hLength B W R τ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceSkolemFamily
