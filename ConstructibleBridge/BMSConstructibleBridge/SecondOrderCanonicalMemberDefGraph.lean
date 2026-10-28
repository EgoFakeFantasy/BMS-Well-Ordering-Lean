import BMSConstructibleBridge.SecondOrderMemberDefPacket
import BMSConstructibleBridge.SecondOrderCanonicalSubsetLayer
import BMSConstructibleBridge.SecondOrderCanonicalGraft
import BMSConstructibleBridge.SecondOrderLegalMemberCollection
import BMSConstructibleBridge.SecondOrderMemberDefault

/-! # 给定原图、根及正规化参数的唯一 Def 输出图

证书和中间图都有完整实数规格，因此输出在原模型实数层唯一。此处尚未
隐藏正规化参数，也未构造相对层次；不把唯一商对象当作唯一实数代表。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalMemberDefGraph

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

structure spec_l (A : set_l ℳ) (r a : num_l ℳ) (V E D Q R T F G P W : set_l ℳ) : Prop where
  packet : SecondOrderMemberDefPacket.spec_l A r a V E D Q R T F
  layer : SecondOrderCanonicalSubsetLayer.spec_l A F r G
  selection : ∀ c, mem_l c P ↔ ∃ i, SecondOrderSubsetLayer.root_l i = c ∧
    SecondOrderLegalFormulaIndex.spec_l V E i
  graft : SecondOrderGraft.spec_l G P W

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (A : set_l ℳ) (r a : num_l ℳ) :
    ∃ V E D Q R T F G P W, spec_l A r a V E D Q R T F G P W := by
  obtain ⟨V, E, D, Q, R, T, F, hPacket⟩ := SecondOrderMemberDefPacket.exists_l hℳ A r a
  obtain ⟨G, hG, _⟩ := SecondOrderCanonicalSubsetLayer.exists_l hℳ A F r
  let η := ((Env.empty (M := ℳ)).pushFree E).pushFree V
  obtain ⟨P, hP⟩ := comprehension_l hℳ
    (SecondOrderSelectedSubsetCollection.selector_m SecondOrderLegalFormulaIndex.formula_m)
    (SecondOrderSelectedSubsetCollection.pure_m _ SecondOrderLegalFormulaIndex.pure_m) η
  have hSelection c : mem_l c P ↔ ∃ i, SecondOrderSubsetLayer.root_l i = c ∧
      SecondOrderLegalFormulaIndex.spec_l V E i := by
    refine (hP c).trans ((SecondOrderSelectedSubsetCollection.selector_l _ η c).trans ?_)
    exact exists_congr (fun i => and_congr Iff.rfl (SecondOrderLegalFormulaIndex.formula_l _))
  obtain ⟨W, hW⟩ := SecondOrderGraft.exists_l hℳ G P
  exact ⟨V, E, D, Q, R, T, F, G, P, W, hPacket, hG, hSelection, hW⟩

theorem unique_l (hℳ : Theory.Models ℳ theory_m) {A : set_l ℳ} {r a : num_l ℳ}
    {V E D Q R T F G P W V' E' D' Q' R' T' F' G' P' W' : set_l ℳ}
    (h : spec_l A r a V E D Q R T F G P W)
    (h' : spec_l A r a V' E' D' Q' R' T' F' G' P' W') : W = W' := by
  obtain ⟨hV, hE, hD, hQ, hR, hT, hF⟩ := SecondOrderMemberDefPacket.unique_l hℳ h.packet h'.packet
  subst V' E' D' Q' R' T' F'
  have hG := SecondOrderCanonicalSubsetLayer.unique_l hℳ h.layer h'.layer
  have hP := SecondOrderModel.ext_l hℳ P P'
    (fun c => (h.selection c).trans (h'.selection c).symm)
  subst G' P'
  exact SecondOrderCanonicalGraft.unique_l hℳ h.graft h'.graft

def output_l (A : set_l ℳ) (r a : num_l ℳ) (W : set_l ℳ) : Prop :=
  ∃ V E D Q R T F G P, spec_l A r a V E D Q R T F G P W

theorem output_exists_l (hℳ : Theory.Models ℳ theory_m) (A : set_l ℳ) (r a : num_l ℳ) :
    ∃! W, output_l A r a W := by
  obtain ⟨V, E, D, Q, R, T, F, G, P, W, hW⟩ := exists_l hℳ A r a
  refine ⟨W, ⟨V, E, D, Q, R, T, F, G, P, hW⟩, ?_⟩
  rintro W' ⟨V', E', D', Q', R', T', F', G', P', hW'⟩
  exact unique_l hℳ hW' hW

/-- 隐藏唯一默认成员编号后的全域原图操作。 -/
def canonical_l (A : set_l ℳ) (r : num_l ℳ) (W : set_l ℳ) : Prop :=
  ∃ a, SecondOrderMemberDefault.spec_l A r a ∧ output_l A r a W

theorem canonical_exists_l (hℳ : Theory.Models ℳ theory_m) (A : set_l ℳ) (r : num_l ℳ) :
    ∃! W, canonical_l A r W := by
  obtain ⟨a, ha⟩ := SecondOrderMemberDefault.exists_l hℳ A r
  obtain ⟨W, hW, hUnique⟩ := output_exists_l hℳ A r a
  refine ⟨W, ⟨a, ha, hW⟩, ?_⟩
  rintro W' ⟨b, hb, hW'⟩
  have hba := SecondOrderMemberDefault.unique_l hℳ hb ha
  subst b
  exact hUnique W' hW'

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalMemberDefGraph
