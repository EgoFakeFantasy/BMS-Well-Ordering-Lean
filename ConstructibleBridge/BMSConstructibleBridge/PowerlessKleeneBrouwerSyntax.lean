import BMSConstructibleBridge.PowerlessRelativeClassSequenceSplitDerives
import BMSConstructibleBridge.PowerlessMapBounded
import BMSConstructibleBridge.SecondOrderFoundation

/-! # 反向前缀的 Kleene–Brouwer 比较式

纯隶属 ℒ。较长的真扩展先于其前缀；否则在共同定义域的第一个
差异位置按数值隶属比较。全部长度和坐标都有界，故可用于 Class 分离。
这里只证明实际 AST、读数及非自返性，不把该关系在全部序列上称作良序：
良序性必须另外限制到根良基下降路径树并证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerSyntax

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderObjectSyntax (member_m)
open PowerlessRelativeClassSequenceSplit (prefix_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def difference_m {Γ Δ : SortContext ℒ} (n m I f g : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up (up t))
  membershipLevyBound.boundedExists n <| membershipLevyBound.boundedExists (up I) <|
    membershipLevyBound.boundedExists (up (up I)) <|
      let i : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
      let a : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
      let b : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar .here
      .conj (member_m i (w m)) <|
        .conj (PowerlessValueBounded.formula_m (w f) i a) <|
          .conj (PowerlessValueBounded.formula_m (w g) i b) <|
            .conj (member_m a b) (PowerlessRelativeClassSequenceSplitDerives.prefix_m i (w I) (w f) (w g))

theorem difference_delta_l {Γ Δ : SortContext ℒ} (n m I f g : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (difference_m n m I f g) :=
  .bounded_exists _ (.bounded_exists _ (.bounded_exists _
    (.conj (.rel _ _) (.conj (PowerlessValueBounded.delta_l _ _ _)
      (.conj (PowerlessValueBounded.delta_l _ _ _)
        (.conj (.rel _ _) (PowerlessRelativeClassSequenceSplitDerives.prefix_delta_l _ _ _ _)))))))

def difference_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (n m I f g : carrier_l 𝒩) : Prop :=
  ∃ i a b, member_l 𝒩 i n ∧ member_l 𝒩 i m ∧ member_l 𝒩 a I ∧ member_l 𝒩 b I ∧
    value_l f i a ∧ value_l g i b ∧ member_l 𝒩 a b ∧ prefix_l i I f g

theorem difference_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (n m I f g : Term ℒ Γ Δ .set) :
    (difference_m n m I f g).satisfies η ↔
      difference_l (n.eval η) (m.eval η) (I.eval η) (f.eval η) (g.eval η) := by
  simp only [difference_m, difference_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessValueBounded.formula_l, PowerlessRelativeClassSequenceSplitDerives.prefix_formula_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  exact ⟨fun ⟨i, hi, a, ha, b, hb, him, hfa, hgb, hab, hPrefix⟩ =>
    ⟨i, a, b, hi, him, ha, hb, hfa, hgb, hab, hPrefix⟩,
    fun ⟨i, a, b, hi, him, ha, hb, hfa, hgb, hab, hPrefix⟩ =>
      ⟨i, hi, a, ha, b, hb, him, hfa, hgb, hab, hPrefix⟩⟩

def compare_m {Γ Δ : SortContext ℒ} (ω I f g : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up t)
  membershipLevyBound.boundedExists ω <| membershipLevyBound.boundedExists (up ω) <|
    let n : Term ℒ (.set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let m : Term ℒ (.set :: .set :: Γ) Δ .set := .bvar .here
    .conj (PowerlessMapBounded.formula_m (w f) n (w I)) <|
      .conj (PowerlessMapBounded.formula_m (w g) m (w I)) <|
        .disj (.conj (member_m m n) (PowerlessRelativeClassSequenceSplitDerives.prefix_m m (w I) (w f) (w g)))
          (difference_m n m (w I) (w f) (w g))

theorem compare_delta_l {Γ Δ : SortContext ℒ} (ω I f g : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (compare_m ω I f g) :=
  .bounded_exists _ (.bounded_exists _ (.conj (PowerlessMapBounded.delta_l _ _ _)
    (.conj (PowerlessMapBounded.delta_l _ _ _)
      (.disj (.conj (.rel _ _) (PowerlessRelativeClassSequenceSplitDerives.prefix_delta_l _ _ _ _))
        (difference_delta_l _ _ _ _ _)))))

def compare_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω I f g : carrier_l 𝒩) : Prop :=
  ∃ n m, member_l 𝒩 n ω ∧ member_l 𝒩 m ω ∧ map_l f n I ∧ map_l g m I ∧
    ((member_l 𝒩 m n ∧ prefix_l m I f g) ∨ difference_l n m I f g)

theorem compare_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω I f g : Term ℒ Γ Δ .set) :
    (compare_m ω I f g).satisfies η ↔ compare_l (ω.eval η) (I.eval η) (f.eval η) (g.eval η) := by
  simp only [compare_m, compare_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessMapBounded.formula_l, PowerlessRelativeClassSequenceSplitDerives.prefix_formula_l,
    difference_formula_l, member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  exact ⟨fun ⟨n, hn, m, hm, hf, hg, hCompare⟩ => ⟨n, m, hn, hm, hf, hg, hCompare⟩,
    fun ⟨n, m, hn, hm, hf, hg, hCompare⟩ => ⟨n, hn, m, hm, hf, hg, hCompare⟩⟩

/-- 真扩展先于前缀，方向与旧 shortlex 相反。 -/
theorem extension_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {ω I f g n m : carrier_l 𝒩}
    (hn : member_l 𝒩 n ω) (hm : member_l 𝒩 m ω)
    (hf : map_l f n I) (hg : map_l g m I)
    (hLength : member_l 𝒩 m n) (hPrefix : prefix_l m I f g) : compare_l ω I f g :=
  ⟨n, m, hn, hm, hf, hg, Or.inl ⟨hLength, hPrefix⟩⟩

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem irreflexive_l {ω I f : SecondOrderQuotient.type_l hℳ} : ¬compare_l (𝒩 := 𝒱) ω I f f := by
  rintro ⟨n, m, _hn, _hm, hf, hg, hCompare⟩
  have hDomain : n = m := by
    apply SecondOrderQuotient.ext_l hℳ n m
    intro i
    constructor
    · intro hi
      obtain ⟨a, ha, _⟩ := hf.2 i hi
      exact (SecondOrderFunctionProperties.value_mem_l hℳ hg ha.2).1
    · intro hi
      obtain ⟨a, ha, _⟩ := hg.2 i hi
      exact (SecondOrderFunctionProperties.value_mem_l hℳ hf ha.2).1
  have hIrrefl (x : SecondOrderQuotient.type_l hℳ) : ¬SecondOrderQuotient.mem_l hℳ x x := by
    obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
    exact SecondOrderFoundation.irrefl_l hℳ X
  rcases hCompare with ⟨hmn, _⟩ | ⟨_i, a, b, _hin, _him, _ha, _hb, hfa, hfb, hab, _hPrefix⟩
  · exact hIrrefl m (hDomain ▸ hmn)
  · have hEq := SecondOrderFunctionProperties.value_unique_l hℳ hf hfa hfb
    exact hIrrefl b (hEq ▸ hab)

def irreflexive_m {Δ : SortContext ℒ} (ω I : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close <| .forallE .set <|
    .neg (compare_m (up ω) (up I) (.bvar .here) (.bvar .here))

theorem irreflexive_models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (ω I : Term ℒ [] Δ .set) : (irreflexive_m ω I).TrueIn 𝒱 := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η f
  exact fun h => irreflexive_l (hℳ := hℳ) ((compare_formula_l (η.pushBound f) _ _ _ _).mp h)

theorem irreflexive_derives_m {Δ : SortContext ℒ} (ω I : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (irreflexive_m ω I)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => irreflexive_models_l hℳ ω I)

#print axioms difference_formula_l
#print axioms compare_formula_l
#print axioms irreflexive_l
#print axioms irreflexive_derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerSyntax
