| \    | 0x0 | 0x1 | 0x2 | 0x3 |
| ---: | :-- | :-- | :-- | :-- |
| **0x00** | [`ResForAll`] | [`And3`] | [`CondEq`] | [`CarryFromAdder`] |
| **0x04** | [`SubClassInCls`] | [`NotElementOf`] | [`Subset`] | [`ProperSubset`] |
| **0x08** | [`SumFromAdder`] | [`LogicalIf`] | [`DiffOp`] | [`UnionOp`] |
| **0x0C** | [`IntersectionOp`] | [`ResExAtMostOne`] | [`SymDiffOp`] | [`Or3`] |
| **0x10** | [`PowerCls`] | [`NotEquals`] | [`UniversalCls`] | [`ResExExactlyOne`] |
| **0x14** | [`TransCls`] | [`Singleton`] | [`UnorderdPair`] | [`UnorderdTriple`] |
| **0x18** | [`ClassUnion`] | [`ClassIntersection`] | [`IndexedUnion`] | [`SubSetInWff`] |
| **0x1C** | [`SubClassInWff`] | [`ResExists`] | [`SetNotFreeInWff`] | [`SetNotFreeInCls`] |
| **0x20** | [`BinaryRelation`] | [`Not`] | [`IndexedIntersection`] | [`DisjointFamily`] |
| **0x24** | [`SupportOperator`] | [`OperatorToFuns`] | [`And`] | [`RelationToFuns`] |
| **0x28** | [`ProperSubsetRel`] | [`ApplyOperator`] | [`Multiplication`] | [`Addition`] |
| **0x2C** | [`OrdPairsBuilder`] | [`Subtraction`] | [`DisjointUnion`] | [`Division`] |
| **0x30** | [`False`] | [`True`] | [`OrderedPair`] | [`ExistsExactlyOne`] |
| **0x34** | [`OrderedTriple`] | [`OneToOneFun`] | [`OntoFun`] | [`OneToOneOntoFun`] |
| **0x38** | [`Omega`] | [`OperatorMapsTo`] | [`Biimp`] | [`OperatorBuilder`] |
| **0x3C** | [`LessThan`] | [`Equals`] | [`Implies`] | [`ClassIf`] |
| **0x40** | [`ForAll`] | Class <span style="color: #C3C">A</span> | Class <span style="color: #C3C">B</span> | Class <span style="color: #C3C">C</span> |
| **0x44** | Class <span style="color: #C3C">D</span> | [`MembershipRelation`] | Class <span style="color: #C3C">F</span> | Class <span style="color: #C3C">G</span> |
| **0x48** | Class <span style="color: #C3C">H</span> | [`IdentityRelation`] | Class <span style="color: #C3C">J</span> | Class <span style="color: #C3C">K</span> |
| **0x4C** | Class <span style="color: #C3C">L</span> | Class <span style="color: #C3C">M</span> | [`OrdNaturalAdd`] | [`EmptyCls`] |
| **0x50** | Boolean <span style="color: blue">P</span> | Boolean <span style="color: blue">Q</span> | Boolean <span style="color: blue">R</span> | Boolean <span style="color: blue">S</span> |
| **0x54** | Boolean <span style="color: blue">T</span> | Boolean <span style="color: blue">U</span> | Boolean <span style="color: blue">V</span> | Boolean <span style="color: blue">W</span> |
| **0x58** | Boolean <span style="color: blue">X</span> | Boolean <span style="color: blue">Y</span> | Boolean <span style="color: blue">Z</span> | [`EquivalenceCls`] |
| **0x5C** | [`NonnegativeIntegers`] | [`Exists`] | [`Supremum`] | [`Infimum`] |
| **0x60** | [`ApplyFun`] | Setvar <span style="color: red">a</span> | Setvar <span style="color: red">b</span> | Setvar <span style="color: red">c</span> |
| **0x64** | Setvar <span style="color: red">d</span> | [`IsElementOf`] | Setvar <span style="color: red">f</span> | Setvar <span style="color: red">g</span> |
| **0x68** | [`ResIota`] | [`Iota`] | [`CumulativeHierarchy`] | [`FiniteIntersection`] |
| **0x6C** | [`Rank`] | [`ExistsAtMostOne`] | [`NotAnd`] | [`ExclusiveOr`] |
| **0x70** | [`NotOr`] | [`FiniteSets`] | [`RecursiveGenerator`] | [`IndexAwareRecGen`] |
| **0x74** | [`FunTranspose`] | Setvar <span style="color: red">u</span> | Setvar <span style="color: red">v</span> | Setvar <span style="color: red">w</span> |
| **0x78** | Setvar <span style="color: red">x</span> | Setvar <span style="color: red">y</span> | Setvar <span style="color: red">z</span> | [`ClassBuilder`] |
| **0x7C** | [`Or`] | [`PositiveIntegers`] | [`RelationIsometry`] | [`ChoiceAxiomHolds`] |
| **0x80** | [`AlephFun`] | [`ExtractFirst`] | [`ExtractSecond`] | [`CantorNormalForm`] |
| **0x84** | [`TarskiClasses`] | [`EquivalenceRelPred`] | [`WellFounded`] | [`GenContinuumHyp`] |
| **0x88** | [`HartogsFun`] | [`OrdinalIsomorphism`] | [`LeftInjection`] | [`RightInjection`] |
| **0x8C** | [`WeakInaccessibles`] | [`StrongInaccessibles`] | [`GrothendieckUnis`] | [`CompleteOrder`] |
| **0x90** | [`PartialOrder`] | [`FiniteSupport`] | [`StrongTfinRecGen`] | [`SetLike`] |
| **0x94** | [`TransClassClosure`] | [`UndefinedFun`] | [`TransClosureFun`] | [`WellOrdering`] |
| **0x98** | [`IndexedCartProduct`] | [`WeakUnis`] | [`WeakUniClosure`] | [`WeakDominance`] |
| **0x9C** | [`SetPosInts`] | [`AddPosInts`] | [`MulPosInts`] | [`LtPosInts`] |
| **0xA0** | [`AddPosFracs`] | [`MulPosFracs`] | [`Image`] | [`Cardinality`] |
| **0xA4** | [`TarskiClassClosure`] | [`LtPosFracs`] | [`PositiveReals`] | [`EqPosFracs`] |
| **0xA8** | [`Dominance`] | [`ExtendedReals`] | [`OrdMult`] | [`OrdAdd`] |
| **0xAC** | [`ExtendedNonnegInts`] | [`UnaryMinus`] | [`DecimalConstructor`] | [`QuotientSets`] |
| **0xB0** | [`Zero`] | [`One`] | [`Two`] | [`Three`] |
| **0xB4** | [`Four`] | [`Five`] | [`Six`] | [`Seven`] |
| **0xB8** | [`Eight`] | [`Nine`] | [`FunWDomAndCodom`] | [`SqrtMinusOne`] |
| **0xBC** | [`StrictDominance`] | [`NegInfinity`] | [`MapsTo`] | [`UpperIntegers`] |
| **0xC0** | [`SetPosRats`] | [`OnePosRats`] | [`ReducePosRats`] | [`Curry`] |
| **0xC4** | [`Domain`] | [`AddPosRats`] | [`FunPred`] | [`MulPosRats`] |
| **0xC8** | [`OrdOne`] | [`OrdTwo`] | [`OrdThree`] | [`OrdFour`] |
| **0xCC** | [`LimitOrdinalPred`] | [`MappingOp`] | [`Ordinals`] | [`OrdinalPred`] |
| **0xD0** | [`PartialMappingOp`] | [`InvPosRats`] | [`Range`] | [`SmoFunPred`] |
| **0xD4** | [`LtPosRats`] | [`Uncurry`] | [`SetPosReals`] | [`OnePosReals`] |
| **0xD8** | [`CartesianProduct`] | [`AddPosReals`] | [`MulPosReals`] | [`ComplexNumbers`] |
| **0xDC** | [`Integers`] | [`RealNumbers`] | [`Restriction`] | [`LtReals`] |
| **0xE0** | [`Converse`] | [`LocalAxiomChoice`] | [`LtPosReals`] | [`Cofinality`] |
| **0xE4** | [`EqTmpReals`] | [`OrdExp`] | [`WellFoundRecGen`] | [`Finite1a`] |
| **0xE8** | [`Finite2`] | [`Finite4`] | [`Finite3`] | [`Finite5`] |
| **0xEC** | [`Finite6`] | [`Finite7`] | [`FunWDom`] | [`Compose`] |
| **0xF0** | [`PredecessorCls`] | [`SetTmpReals`] | [`RelationPred`] | [`Successor`] |
| **0xF4** | [`ZeroTmpReals`] | [`OneTmpReals`] | [`MinusOneTmpReals`] | [`WellOrderRecGen`] |
| **0xF8** | [`AddTmpReals`] | [`MulTmpReals`] | [`LtTmpReals`] | [`ResClassBuilder`] |
| **0xFC** | [`PosInfinity`] | [`LessOrEqual`] | [`Equinumerous`] | [`Rationals`] |

[`True`]: crate::NodeByte::True
[`False`]: crate::NodeByte::False
[`ChoiceAxiomHolds`]: crate::NodeByte::ChoiceAxiomHolds
[`Not`]: crate::NodeByte::Not
[`TransCls`]: crate::NodeByte::TransCls
[`RelationPred`]: crate::NodeByte::RelationPred
[`OrdinalPred`]: crate::NodeByte::OrdinalPred
[`LimitOrdinalPred`]: crate::NodeByte::LimitOrdinalPred
[`FunPred`]: crate::NodeByte::FunPred
[`SmoFunPred`]: crate::NodeByte::SmoFunPred
[`Implies`]: crate::NodeByte::Implies
[`Biimp`]: crate::NodeByte::Biimp
[`And`]: crate::NodeByte::And
[`Or`]: crate::NodeByte::Or
[`NotAnd`]: crate::NodeByte::NotAnd
[`ExclusiveOr`]: crate::NodeByte::ExclusiveOr
[`NotOr`]: crate::NodeByte::NotOr
[`ForAll`]: crate::NodeByte::ForAll
[`Exists`]: crate::NodeByte::Exists
[`ExistsAtMostOne`]: crate::NodeByte::ExistsAtMostOne
[`ExistsExactlyOne`]: crate::NodeByte::ExistsExactlyOne
[`SetNotFreeInWff`]: crate::NodeByte::SetNotFreeInWff
[`SetNotFreeInCls`]: crate::NodeByte::SetNotFreeInCls
[`Equals`]: crate::NodeByte::Equals
[`IsElementOf`]: crate::NodeByte::IsElementOf
[`NotEquals`]: crate::NodeByte::NotEquals
[`NotElementOf`]: crate::NodeByte::NotElementOf
[`Subset`]: crate::NodeByte::Subset
[`ProperSubset`]: crate::NodeByte::ProperSubset
[`PartialOrder`]: crate::NodeByte::PartialOrder
[`CompleteOrder`]: crate::NodeByte::CompleteOrder
[`WellFounded`]: crate::NodeByte::WellFounded
[`SetLike`]: crate::NodeByte::SetLike
[`WellOrdering`]: crate::NodeByte::WellOrdering
[`FunWDom`]: crate::NodeByte::FunWDom
[`EquivalenceRelPred`]: crate::NodeByte::EquivalenceRelPred
[`And3`]: crate::NodeByte::And3
[`Or3`]: crate::NodeByte::Or3
[`SumFromAdder`]: crate::NodeByte::SumFromAdder
[`CarryFromAdder`]: crate::NodeByte::CarryFromAdder
[`LogicalIf`]: crate::NodeByte::LogicalIf
[`SubSetInWff`]: crate::NodeByte::SubSetInWff
[`CondEq`]: crate::NodeByte::CondEq
[`ResForAll`]: crate::NodeByte::ResForAll
[`ResExists`]: crate::NodeByte::ResExists
[`ResExAtMostOne`]: crate::NodeByte::ResExAtMostOne
[`ResExExactlyOne`]: crate::NodeByte::ResExExactlyOne
[`DisjointFamily`]: crate::NodeByte::DisjointFamily
[`SubClassInWff`]: crate::NodeByte::SubClassInWff
[`BinaryRelation`]: crate::NodeByte::BinaryRelation
[`FunWDomAndCodom`]: crate::NodeByte::FunWDomAndCodom
[`OneToOneFun`]: crate::NodeByte::OneToOneFun
[`OntoFun`]: crate::NodeByte::OntoFun
[`OneToOneOntoFun`]: crate::NodeByte::OneToOneOntoFun
[`RelationIsometry`]: crate::NodeByte::RelationIsometry
[`UniversalCls`]: crate::NodeByte::UniversalCls
[`EmptyCls`]: crate::NodeByte::EmptyCls
[`IdentityRelation`]: crate::NodeByte::IdentityRelation
[`MembershipRelation`]: crate::NodeByte::MembershipRelation
[`Ordinals`]: crate::NodeByte::Ordinals
[`ProperSubsetRel`]: crate::NodeByte::ProperSubsetRel
[`Omega`]: crate::NodeByte::Omega
[`ExtractFirst`]: crate::NodeByte::ExtractFirst
[`ExtractSecond`]: crate::NodeByte::ExtractSecond
[`SupportOperator`]: crate::NodeByte::SupportOperator
[`UndefinedFun`]: crate::NodeByte::UndefinedFun
[`OrdOne`]: crate::NodeByte::OrdOne
[`OrdTwo`]: crate::NodeByte::OrdTwo
[`OrdThree`]: crate::NodeByte::OrdThree
[`OrdFour`]: crate::NodeByte::OrdFour
[`OrdAdd`]: crate::NodeByte::OrdAdd
[`OrdMult`]: crate::NodeByte::OrdMult
[`OrdExp`]: crate::NodeByte::OrdExp
[`OrdNaturalAdd`]: crate::NodeByte::OrdNaturalAdd
[`MappingOp`]: crate::NodeByte::MappingOp
[`PartialMappingOp`]: crate::NodeByte::PartialMappingOp
[`Equinumerous`]: crate::NodeByte::Equinumerous
[`Dominance`]: crate::NodeByte::Dominance
[`StrictDominance`]: crate::NodeByte::StrictDominance
[`FiniteSets`]: crate::NodeByte::FiniteSets
[`FiniteSupport`]: crate::NodeByte::FiniteSupport
[`FiniteIntersection`]: crate::NodeByte::FiniteIntersection
[`HartogsFun`]: crate::NodeByte::HartogsFun
[`WeakDominance`]: crate::NodeByte::WeakDominance
[`CantorNormalForm`]: crate::NodeByte::CantorNormalForm
[`TransClosureFun`]: crate::NodeByte::TransClosureFun
[`CumulativeHierarchy`]: crate::NodeByte::CumulativeHierarchy
[`Rank`]: crate::NodeByte::Rank
[`LeftInjection`]: crate::NodeByte::LeftInjection
[`RightInjection`]: crate::NodeByte::RightInjection
[`Cardinality`]: crate::NodeByte::Cardinality
[`AlephFun`]: crate::NodeByte::AlephFun
[`Cofinality`]: crate::NodeByte::Cofinality
[`Finite1a`]: crate::NodeByte::Finite1a
[`Finite2`]: crate::NodeByte::Finite2
[`Finite4`]: crate::NodeByte::Finite4
[`Finite3`]: crate::NodeByte::Finite3
[`Finite5`]: crate::NodeByte::Finite5
[`Finite6`]: crate::NodeByte::Finite6
[`Finite7`]: crate::NodeByte::Finite7
[`GenContinuumHyp`]: crate::NodeByte::GenContinuumHyp
[`WeakInaccessibles`]: crate::NodeByte::WeakInaccessibles
[`StrongInaccessibles`]: crate::NodeByte::StrongInaccessibles
[`WeakUnis`]: crate::NodeByte::WeakUnis
[`WeakUniClosure`]: crate::NodeByte::WeakUniClosure
[`TarskiClasses`]: crate::NodeByte::TarskiClasses
[`GrothendieckUnis`]: crate::NodeByte::GrothendieckUnis
[`TarskiClassClosure`]: crate::NodeByte::TarskiClassClosure
[`SetPosInts`]: crate::NodeByte::SetPosInts
[`AddPosInts`]: crate::NodeByte::AddPosInts
[`MulPosInts`]: crate::NodeByte::MulPosInts
[`LtPosInts`]: crate::NodeByte::LtPosInts
[`AddPosFracs`]: crate::NodeByte::AddPosFracs
[`MulPosFracs`]: crate::NodeByte::MulPosFracs
[`LtPosFracs`]: crate::NodeByte::LtPosFracs
[`EqPosFracs`]: crate::NodeByte::EqPosFracs
[`SetPosRats`]: crate::NodeByte::SetPosRats
[`OnePosRats`]: crate::NodeByte::OnePosRats
[`ReducePosRats`]: crate::NodeByte::ReducePosRats
[`AddPosRats`]: crate::NodeByte::AddPosRats
[`MulPosRats`]: crate::NodeByte::MulPosRats
[`InvPosRats`]: crate::NodeByte::InvPosRats
[`LtPosRats`]: crate::NodeByte::LtPosRats
[`SetPosReals`]: crate::NodeByte::SetPosReals
[`OnePosReals`]: crate::NodeByte::OnePosReals
[`AddPosReals`]: crate::NodeByte::AddPosReals
[`MulPosReals`]: crate::NodeByte::MulPosReals
[`LtPosReals`]: crate::NodeByte::LtPosReals
[`EqTmpReals`]: crate::NodeByte::EqTmpReals
[`SetTmpReals`]: crate::NodeByte::SetTmpReals
[`ZeroTmpReals`]: crate::NodeByte::ZeroTmpReals
[`OneTmpReals`]: crate::NodeByte::OneTmpReals
[`MinusOneTmpReals`]: crate::NodeByte::MinusOneTmpReals
[`AddTmpReals`]: crate::NodeByte::AddTmpReals
[`MulTmpReals`]: crate::NodeByte::MulTmpReals
[`LtTmpReals`]: crate::NodeByte::LtTmpReals
[`ComplexNumbers`]: crate::NodeByte::ComplexNumbers
[`RealNumbers`]: crate::NodeByte::RealNumbers
[`Zero`]: crate::NodeByte::Zero
[`One`]: crate::NodeByte::One
[`SqrtMinusOne`]: crate::NodeByte::SqrtMinusOne
[`Addition`]: crate::NodeByte::Addition
[`LtReals`]: crate::NodeByte::LtReals
[`Multiplication`]: crate::NodeByte::Multiplication
[`PosInfinity`]: crate::NodeByte::PosInfinity
[`NegInfinity`]: crate::NodeByte::NegInfinity
[`ExtendedReals`]: crate::NodeByte::ExtendedReals
[`LessThan`]: crate::NodeByte::LessThan
[`LessOrEqual`]: crate::NodeByte::LessOrEqual
[`Subtraction`]: crate::NodeByte::Subtraction
[`Division`]: crate::NodeByte::Division
[`PositiveIntegers`]: crate::NodeByte::PositiveIntegers
[`Two`]: crate::NodeByte::Two
[`Three`]: crate::NodeByte::Three
[`Four`]: crate::NodeByte::Four
[`Five`]: crate::NodeByte::Five
[`Six`]: crate::NodeByte::Six
[`Seven`]: crate::NodeByte::Seven
[`Eight`]: crate::NodeByte::Eight
[`Nine`]: crate::NodeByte::Nine
[`NonnegativeIntegers`]: crate::NodeByte::NonnegativeIntegers
[`ExtendedNonnegInts`]: crate::NodeByte::ExtendedNonnegInts
[`Integers`]: crate::NodeByte::Integers
[`UpperIntegers`]: crate::NodeByte::UpperIntegers
[`Rationals`]: crate::NodeByte::Rationals
[`PositiveReals`]: crate::NodeByte::PositiveReals
[`PowerCls`]: crate::NodeByte::PowerCls
[`Singleton`]: crate::NodeByte::Singleton
[`ClassUnion`]: crate::NodeByte::ClassUnion
[`ClassIntersection`]: crate::NodeByte::ClassIntersection
[`Converse`]: crate::NodeByte::Converse
[`Domain`]: crate::NodeByte::Domain
[`Range`]: crate::NodeByte::Range
[`Successor`]: crate::NodeByte::Successor
[`OperatorToFuns`]: crate::NodeByte::OperatorToFuns
[`RelationToFuns`]: crate::NodeByte::RelationToFuns
[`FunTranspose`]: crate::NodeByte::FunTranspose
[`Curry`]: crate::NodeByte::Curry
[`Uncurry`]: crate::NodeByte::Uncurry
[`StrongTfinRecGen`]: crate::NodeByte::StrongTfinRecGen
[`TransClassClosure`]: crate::NodeByte::TransClassClosure
[`LocalAxiomChoice`]: crate::NodeByte::LocalAxiomChoice
[`UnaryMinus`]: crate::NodeByte::UnaryMinus
[`ClassBuilder`]: crate::NodeByte::ClassBuilder
[`Iota`]: crate::NodeByte::Iota
[`DiffOp`]: crate::NodeByte::DiffOp
[`UnionOp`]: crate::NodeByte::UnionOp
[`IntersectionOp`]: crate::NodeByte::IntersectionOp
[`SymDiffOp`]: crate::NodeByte::SymDiffOp
[`UnorderdPair`]: crate::NodeByte::UnorderdPair
[`OrderedPair`]: crate::NodeByte::OrderedPair
[`CartesianProduct`]: crate::NodeByte::CartesianProduct
[`Restriction`]: crate::NodeByte::Restriction
[`Image`]: crate::NodeByte::Image
[`Compose`]: crate::NodeByte::Compose
[`ApplyFun`]: crate::NodeByte::ApplyFun
[`RecursiveGenerator`]: crate::NodeByte::RecursiveGenerator
[`IndexAwareRecGen`]: crate::NodeByte::IndexAwareRecGen
[`EquivalenceCls`]: crate::NodeByte::EquivalenceCls
[`QuotientSets`]: crate::NodeByte::QuotientSets
[`OrdinalIsomorphism`]: crate::NodeByte::OrdinalIsomorphism
[`DisjointUnion`]: crate::NodeByte::DisjointUnion
[`DecimalConstructor`]: crate::NodeByte::DecimalConstructor
[`ClassIf`]: crate::NodeByte::ClassIf
[`OrdPairsBuilder`]: crate::NodeByte::OrdPairsBuilder
[`ResClassBuilder`]: crate::NodeByte::ResClassBuilder
[`ResIota`]: crate::NodeByte::ResIota
[`IndexedUnion`]: crate::NodeByte::IndexedUnion
[`IndexedIntersection`]: crate::NodeByte::IndexedIntersection
[`MapsTo`]: crate::NodeByte::MapsTo
[`IndexedCartProduct`]: crate::NodeByte::IndexedCartProduct
[`SubClassInCls`]: crate::NodeByte::SubClassInCls
[`UnorderdTriple`]: crate::NodeByte::UnorderdTriple
[`OrderedTriple`]: crate::NodeByte::OrderedTriple
[`PredecessorCls`]: crate::NodeByte::PredecessorCls
[`ApplyOperator`]: crate::NodeByte::ApplyOperator
[`WellFoundRecGen`]: crate::NodeByte::WellFoundRecGen
[`WellOrderRecGen`]: crate::NodeByte::WellOrderRecGen
[`Supremum`]: crate::NodeByte::Supremum
[`Infimum`]: crate::NodeByte::Infimum
[`OperatorBuilder`]: crate::NodeByte::OperatorBuilder
[`OperatorMapsTo`]: crate::NodeByte::OperatorMapsTo