import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SupportParameters
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SyntaxSubstitution
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicQuotation

/-! # 十一类参数支撑公理的类型化装配

参数直接进入既有分离谓词，再沿公共分离外壳关闭全部自由上下文。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.SupportAssembly
open Nonlogical.BasicSetTheory NatPacket SupportParameters
set_option autoImplicit false

def predicate {free : SetContext} : (kind : Kind) →
    Arguments signature [] free (List.replicate kind.arity SetSort.set) → SetPredicate free
  | .domain, .cons relation .nil => relation_coordinate_predicate .domain relation
  | .range, .cons relation .nil => relation_coordinate_predicate .range relation
  | .cartesianProduct, .cons left (.cons right .nil) => cartesian_product_predicate left right
  | .converse, .cons relation .nil => relation_converse_predicate relation
  | .composition, .cons first (.cons second .nil) => relation_composition_predicate first second
  | .identity, .cons source .nil => identity_predicate source
  | .mappingCollection, .cons source (.cons target .nil) => mapping_collection_predicate source target
  | .indexOrder, .cons sourceRelation (.cons sourceCarrier (.cons targetRelation (.cons targetCarrier .nil))) =>
      index_order_predicate sourceRelation sourceCarrier targetRelation targetCarrier
  | .powerSetBijection, .cons natural .nil => power_set_bijection_predicate natural
  | .symmetricDifference, .cons left (.cons right .nil) => symmetric_difference_predicate left right
  | .inductiveCore, .cons source .nil => inductive_core_predicate source

def openAxiom (kind : Kind) (parameters : SyntaxParameters.Parameters kind.arity) : SetOpenFormula parameters.free :=
  (predicate kind parameters.args).separation_open_axiom

def sentence (kind : Kind) (parameters : SyntaxParameters.Parameters kind.arity) : SetSentence :=
  (predicate kind parameters.args).separation_axiom

/-- 每个族只有一份固定开放公式，其自由槽恰好是原证书中的项参数。 -/
def template (kind : Kind) : SetOpenFormula (List.replicate kind.arity SetSort.set) :=
  (predicate kind (SyntaxEncode.substitutionArguments _ VariableSubstitution.freeId)).separation_open_axiom

def instantiate (kind : Kind) (parameters : SyntaxParameters.Parameters kind.arity) : SetOpenFormula parameters.free :=
  (template kind).substituteFree (SyntaxDecode.substitution parameters.args)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.SupportAssembly
