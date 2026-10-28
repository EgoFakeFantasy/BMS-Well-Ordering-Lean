import BMSConstructibleBridge.PowerlessRelativeClassRowFamilyWellOrder
import BMSConstructibleBridge.PowerlessAssignmentUpdateBounded
import BMSConstructibleBridge.PowerlessRelativeClassAssignmentUpdate
import BMSConstructibleBridge.PowerlessFiniteSequencesSyntax

/-! # 完整内部 Sat 的单变量子集查询图

指标为实际有序对 (公式码, 有限赋值)。更新见证有全赋值集的界，
图的正文是 Δ₀；同域映射和变量域守卫把有界更新精确接回全坐标更新。
本模块保留给定实际 Sat 图，不以宿主 Formula 枚举替代内部公式码。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSatisfactionRows

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private abbrev up₄ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up (up (up t)))

def query_m {Γ Δ : SortContext ℒ} (ω A S e R p x : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| membershipLevyBound.boundedExists (up S) <|
    membershipLevyBound.boundedExists (up (up ω)) <|
      membershipLevyBound.boundedExists (up (up (up S))) <|
        let c : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there (.there .here)))
        let f : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
        let n : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
        let g : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar .here
        .conj (PowerlessPairBounded.ordered_m c f (up₄ p)) <|
          .conj (PowerlessMapBounded.formula_m f n (up₄ A)) <|
            .conj (PowerlessMapBounded.formula_m g n (up₄ A)) <|
              .conj (member_m (up₄ e) n) <|
                .conj (PowerlessAssignmentUpdateBounded.formula_m n (up₄ A) f (up₄ e) (up₄ x) g)
                  (PowerlessValueBounded.formula_m (up₄ R) c g)

theorem query_delta_l {Γ Δ : SortContext ℒ} (ω A S e R p x : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (query_m ω A S e R p x) :=
  .bounded_exists _ (.bounded_exists _ (.bounded_exists _ (.bounded_exists _
    (.conj (PowerlessPairBounded.ordered_delta_l _ _ _)
      (.conj (PowerlessMapBounded.delta_l _ _ _)
        (.conj (PowerlessMapBounded.delta_l _ _ _)
          (.conj (.rel _ _) (.conj (PowerlessAssignmentUpdateBounded.delta_l _ _ _ _ _ _)
            (PowerlessValueBounded.delta_l _ _ _)))))))))

def query_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω A S e R p x : carrier_l ℳ₀) : Prop :=
  ∃ c f n g, member_l ℳ₀ c ω ∧ member_l ℳ₀ f S ∧ member_l ℳ₀ n ω ∧ member_l ℳ₀ g S ∧
    ordered_l c f p ∧ map_l f n A ∧ map_l g n A ∧ member_l ℳ₀ e n ∧
      PowerlessAssignmentUpdateBounded.holds_l n A f e x g ∧ value_l R c g

theorem query_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (ω A S e R p x : Term ℒ Γ Δ .set) :
    (query_m ω A S e R p x).satisfies η ↔
      query_l (ω.eval η) (A.eval η) (S.eval η) (e.eval η) (R.eval η) (p.eval η) (x.eval η) := by
  simp only [query_m, query_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessPairBounded.ordered_formula_l, PowerlessMapBounded.formula_l,
    PowerlessAssignmentUpdateBounded.formula_l, PowerlessValueBounded.formula_l,
    member_m, Arguments.eval, up₄, up, Term.eval_weakenBound, Term.eval]
  exact ⟨fun ⟨c, hc, f, hf, n, hn, g, hg, h⟩ => ⟨c, f, n, g, hc, hf, hn, hg, h⟩,
    fun ⟨c, f, n, g, hc, hf, hn, hg, h⟩ => ⟨c, hc, f, hf, n, hn, g, hg, h⟩⟩

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒩" => structure_l hℳ B hBase

theorem update_iff_l {n A f e x g : type_l hℳ B}
    (hf : map_l (ℳ := 𝒩) f n A) (hg : map_l (ℳ := 𝒩) g n A)
    (he : mem_l hℳ e.val n.val) (hx : mem_l hℳ x.val A.val) :
    @PowerlessAssignmentUpdateBounded.holds_l 𝒩 n A f e x g ↔
      PowerlessAssignmentUpdate.update_l (ℳ := 𝒩) f e x g := by
  constructor
  · intro h i y
    constructor
    · intro hValue
      have hBounds := PowerlessRelativeClassFunctionProperties.value_mem_l hg hValue
      exact (h i hBounds.1 y hBounds.2).mp hValue
    · intro hValue
      have hBounds : mem_l hℳ i.val n.val ∧ mem_l hℳ y.val A.val := by
        rcases hValue with ⟨rfl, rfl⟩ | ⟨_, hValue⟩
        · exact ⟨he, hx⟩
        · exact PowerlessRelativeClassFunctionProperties.value_mem_l hf hValue
      exact (h i hBounds.1 y hBounds.2).mpr hValue
  · intro h i _ y _
    exact h i y

theorem read_l {ω A S e R p c f n x : type_l hℳ B}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒩) ω A S)
    (hp : ordered_l (ℳ := 𝒩) c f p) (hc : mem_l hℳ c.val ω.val)
    (hn : mem_l hℳ n.val ω.val) (hf : map_l (ℳ := 𝒩) f n A)
    (he : mem_l hℳ e.val n.val) (hx : mem_l hℳ x.val A.val) :
    query_l (ℳ₀ := 𝒩) ω A S e R p x ↔
      ∃ g : type_l hℳ B, map_l (ℳ := 𝒩) g n A ∧
        PowerlessAssignmentUpdate.update_l (ℳ := 𝒩) f e x g ∧ value_l (ℳ := 𝒩) R c g := by
  constructor
  · rintro ⟨c', f', n', g, _, _, _, _, hp', hf', hg, he', hUpdate, hValue⟩
    have hEq := (SecondOrderPairObjects.ordered_eq_l hℳ
      ((PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) c' f' p).mp hp')
      ((PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) c f p).mp hp)).mp rfl
    have hc' : c' = c := Subtype.ext hEq.1
    have hfEq : f' = f := Subtype.ext hEq.2
    subst c'
    subst f'
    have hn' := PowerlessRelativeClassFunctionProperties.domain_unique_l hf' hf
    subst n'
    exact ⟨g, hg, (update_iff_l hf hg he hx).mp hUpdate, hValue⟩
  · rintro ⟨g, hg, hUpdate, hValue⟩
    exact ⟨c, f, n, g, hc, (hS f).mpr ⟨n, hn, hf⟩, hn, (hS g).mpr ⟨n, hn, hg⟩,
      hp, hf, hg, he, (update_iff_l hf hg he hx).mpr hUpdate, hValue⟩

theorem exists_l (ω A S e R I : type_l hℳ B) :
    ∃ Q : type_l hℳ B, ∀ p x : type_l hℳ B, value_l (ℳ := 𝒩) Q p x ↔
      mem_l hℳ p.val I.val ∧ mem_l hℳ x.val A.val ∧ query_l (ℳ₀ := 𝒩) ω A S e R p x := by
  let η : Env 𝒩 [] [.set, .set, .set, .set, .set] :=
    (((((Env.empty).pushFree R).pushFree e).pushFree S).pushFree A).pushFree ω
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set] := query_m
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
    (.fvar .here) (.fvar (.there .here))
  obtain ⟨Q, hQ⟩ := PowerlessRelativeClassRelationalGraph.exists_l
    (φ := φ) (query_delta_l _ _ _ _ _ _ _) η I A
  exact ⟨Q, fun p x => (hQ p x).trans
    (and_congr Iff.rfl (and_congr Iff.rfl (query_formula_l _ _ _ _ _ _ _ _)))⟩

def specification_m {Γ Δ : SortContext ℒ} (ω A S e R I Q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <|
    .iff (value_m (up (up Q)) (.bvar (.there .here)) (.bvar .here)) <|
      .conj (member_m (.bvar (.there .here)) (up (up I))) <|
        .conj (member_m (.bvar .here) (up (up A)))
          (query_m (up (up ω)) (up (up A)) (up (up S)) (up (up e)) (up (up R))
            (.bvar (.there .here)) (.bvar .here))

theorem specification_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (ω A S e R I Q : Term ℒ Γ Δ .set) :
    (specification_m ω A S e R I Q).satisfies η ↔ ∀ p x,
      value_l (Q.eval η) p x ↔ member_l ℳ₀ p (I.eval η) ∧ member_l ℳ₀ x (A.eval η) ∧
        query_l (ω.eval η) (A.eval η) (S.eval η) (e.eval η) (R.eval η) p x := by
  simp only [specification_m, Formula.satisfies, value_formula_l, query_formula_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m : Formula ℒ [] [.set, .set, .set, .set, .set, .set] :=
  let ω : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar .here
  let A : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let S : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let e : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let R : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  let I : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there .here)))))
  .existsE .set (specification_m (up ω) (up A) (up S) (up e) (up R) (up I) (.bvar .here))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    sentence_m.TrueIn (structure_l hℳ B hBase) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, specification_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  exact exists_l (hBase := hBase) _ _ _ _ _ _

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m _ (fun _ h𝒩 B hBase => models_l h𝒩 B hBase)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSatisfactionRows
