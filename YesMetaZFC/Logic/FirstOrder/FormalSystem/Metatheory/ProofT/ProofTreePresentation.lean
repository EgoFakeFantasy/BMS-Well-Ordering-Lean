import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ProofTreeCheck
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Delta1ProofPresentation

/-! # 从局部对象测试装配完整证明树表示

本模块完成根结论从自然数到当前 quotation 的对象等式传输，并把整树的
可靠性、完备性及正负递归推导装配为标准接口。局部测试作为显式参数保留；
只有具体构造该参数后才能称为对应理论的具体证明表示。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ProofTreeCode
open Nonlogical.BasicSetTheory QuineEncoding IntrinsicQuotation
open _root_.YesMetaZFC.Automation ObjectHorn
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

private theorem root_quote {T : SetTheory} (C : CertificateCore T) (code : Nat) (formula : SetSentence) :
    Derives T [] (IntrinsicQuotation.node 1 [numₘ(code), numₘ(treeValue (SyntaxEncode.formula formula))] ≐ₘ
      IntrinsicQuotation.node 1 [numₘ(code), IntrinsicQuotation.quote formula]) :=
  node_congr 1 (.cons (Metatheory.Derives.equality_refl _)
    (.cons (FirstOrder.Derives.eq_symm (quote_evaluate C formula)) .nil))

/-- 对完整局部表示的单一装配入口；它不自行提供局部表示。 -/
def ofLocalTest {Traw Thilbert : SetTheory} {axioms : AxiomPresentation Thilbert}
    {decoder : AxiomDecoder axioms} (codec : AxiomCodec decoder)
    (C : CertificateCore Traw) (S : FiniteSequenceGraphSupport Traw)
    (hPower : ∀ {φ}, power_set_operator_theory φ → Traw φ)
    (hInfinity : ∀ {φ}, infinity_theory φ → Traw φ)
    (localTest : ObjectCheckedTrace.LocalTest Traw)
    (hTest : localTest.checked = ObjectProofTree.rowCheck (localCheck decoder)) :
    Delta1ProofPresentation Traw Thilbert where
  graph := ObjectProofTree.graph localTest.condition localTest.delta0
  checked := checked decoder
  checked_sound := checked_sound decoder
  checked_complete := checked_complete codec
  condition_positive {proofCode} {formula} h := by
    change Derives Traw [] (ObjectProofTree.template localTest.condition (numₘ(proofCode)) (IntrinsicQuotation.quote formula))
    rw [ObjectProofTree.template_apply]
    exact ObjectCheckedTrace.transport ObjectProofTree.rules localTest.condition
      (root_quote C proofCode formula)
      (ObjectProofTree.positive C S hPower hInfinity localTest (localCheck decoder) hTest _ _ h)
  condition_negative {proofCode} {formula} h := by
    change Derives Traw [] (¬ₘ ObjectProofTree.template localTest.condition (numₘ(proofCode)) (IntrinsicQuotation.quote formula))
    rw [ObjectProofTree.template_apply]
    exact ObjectCheckedTrace.transport_negative ObjectProofTree.rules localTest.condition
      (root_quote C proofCode formula)
      (ObjectProofTree.negative C S.toArithmeticSupport localTest (localCheck decoder) hTest _ _ h)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ProofTreeCode
