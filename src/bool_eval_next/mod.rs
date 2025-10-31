//! Next-gen Boolean evaluation.

use crate::{EnumTerm, Metavariable, MguError, Node, NodeByte, SimpleType, Type};
use std::convert::TryInto;
use std::fmt::{Debug as DebugTrait, Display};
use std::marker::PhantomData;
use std::ops::{BitAnd, BitOr, BitXor, Not};
use strum::{
    Display, EnumCount, EnumDiscriminants, EnumString, FromRepr, VariantArray, VariantNames,
};

/// Represent all 278 operations defined on 3 or less Boolean variables.
///
/// `278 = 2^(2^0) + 2^(2^1) + 2^(2^2) + 2^(2^3)`.
#[derive(
    Clone,
    Copy,
    Debug,
    PartialEq,
    Eq,
    Hash,
    Display,
    EnumCount,
    EnumDiscriminants,
    EnumString,
    FromRepr,
    VariantArray,
    VariantNames,
)]
pub enum BooleanSimpleOp {
    /// `False` nullary Boolean operator.
    False0 = 0x0_00,

    /// `True` nullary Boolean operator.
    True0 = 0x0_ff,

    /// `False` unary Boolean operator.
    ///
    /// But see `False0`
    False1 = 0x1_00,
    /// `Not` unary Boolean operator.
    NotA1 = 0x1_55,
    /// `Identity` unary Boolean operator.
    IdA1 = 0x1_aa,
    /// `True` unary Boolean operator.
    ///
    /// But see `True0`
    True1 = 0x1_ff,

    /// `False` binary Boolean operator.
    ///
    /// But see `False0`
    False2 = 0x2_00,
    /// `NotOr` binary Boolean operator.
    NotOrAB2 = 0x2_11,

    /// `NotImplies` binary Boolean operator.
    NotImpliesAB2 = 0x2_22,
    /// Not binary Boolean operator for second argument.
    ///
    /// But see `NotA1`, `NotA2`.
    NotB2 = 0x2_33,
    /// `NotRevImplies` (not-implied-by?) binary Boolean operator.
    NotImpliesBA2 = 0x2_44,

    /// Not binary Boolean operator for first argument.
    ///
    /// But see `NotA1`.
    NotA2 = 0x2_55,
    /// `ExclusiveOr` binary Boolean operator.
    XorAB2 = 0x2_66,
    /// `NotAnd` binary Boolean operator.
    NotAndAB2 = 0x2_77,

    /// `And` binary Boolean operator.
    AndAB2 = 0x2_88,
    /// `NotExclusiveOr` binary Boolean operator. Also known as `Biimplication`.
    NotXorAB2 = 0x2_99,

    /// Identity binary Boolean operator for first argument.
    ///
    /// But see `IdA1`
    IdA2 = 0x2_aa,
    /// `RevImplies` (implied-by?) binary Boolean operator.
    ImpliesBA2 = 0x2_bb,

    /// `Identity` binary Boolean operator for second argument.
    ///
    /// But see `IdA1`
    IdB2 = 0x2_cc,
    /// `Implies` binary Boolean operator.
    ImpliesAB2 = 0x2_dd,
    /// `Or` binary Boolean operator.
    OrAB2 = 0x2_ee,
    /// `True` binary Boolean operator.
    ///
    /// But see `True0`
    True2 = 0x2_ff,

    /// False ternary Boolean operator.
    ///
    /// But see `False0`
    False3 = 0x3_00,
    /// `NotOr3` ternary Boolean operator.
    NotOrABC3 = 0x3_01,
    /// Complicated ternary Boolean operator. `a & !(b | c)`
    AndANotOrBC3 = 0x3_02,
    /// Complicated ternary Boolean operator. `!(b | c)`
    NorOrBC3 = 0x3_03,
    /// Complicated ternary Boolean operator. `b & !(a | c)`
    AndBNotOrAC3 = 0x3_04,
    /// Complicated ternary Boolean operator. `!(a | c)`
    NotOrAC3 = 0x3_05,
    /// Complicated ternary Boolean operator. `c & !(a | b)`
    AndCNotOrAB3 = 0x3_06,
    /// Complicated ternary Boolean operator. `!(c | (a & b))`
    NotOrCAndAB3 = 0x3_07,
    /// Complicated ternary Boolean operator. `a & b & ! c`
    And3ABNotC3 = 0x3_08,
    /// Complicated ternary Boolean operator. `!(c | (a ^ b))`
    NotOrCXOrAB3 = 0x3_09,
    /// TODO. This ternary Boolean operator.
    ABCOp0ATodo3 = 0x3_0a,
    /// TODO. This ternary Boolean operator.
    ABCOp0BTodo3 = 0x3_0b,
    /// TODO. This ternary Boolean operator.
    ABCOp0CTodo3 = 0x3_0c,
    /// TODO. This ternary Boolean operator.
    ABCOp0DTodo3 = 0x3_0d,
    /// TODO. This ternary Boolean operator.
    ABCOp0ETodo3 = 0x3_0e,
    /// Not binary Boolean operator for third argument.
    ///
    /// But see `NotA1`, `NotA3`.
    NotC3 = 0x3_0f,

    /// TODO. This ternary Boolean operator.
    ABCOp10Todo3 = 0x3_10,

    /// `NorOr` ternary Boolean operator operating on first two arguments.
    ///
    /// But see `NotOrAB2`
    NotOrAB3 = 0x3_11,
    /// TODO. This ternary Boolean operator.
    ABCOp12Todo3 = 0x3_12,
    /// TODO. This ternary Boolean operator.
    ABCOp13Todo3 = 0x3_13,
    /// TODO. This ternary Boolean operator.
    ABCOp14Todo3 = 0x3_14,
    /// TODO. This ternary Boolean operator.
    ABCOp15Todo3 = 0x3_15,
    /// TODO. This ternary Boolean operator.
    ABCOp16Todo3 = 0x316,
    /// TODO. This ternary Boolean operator.
    ABCOp17Todo3 = 0x3_17,
    /// TODO. This ternary Boolean operator.
    ABCOp18Todo3 = 0x3_18,
    /// TODO. This ternary Boolean operator.
    ABCOp19Todo3 = 0x3_19,
    /// TODO. This ternary Boolean operator.
    ABCOp1ATodo3 = 0x3_1a,
    /// `NotLogicalIf` ternary Boolean operator on first, third, and second arguments.
    NotIfACB3 = 0x3_1b,
    /// TODO. This ternary Boolean operator.
    ABCOp1CTodo3 = 0x3_1c,
    /// `NotLogicalIf` ternary Boolean operator on second, third, and first arguments.
    NotIfBCA3 = 0x3_1d,
    /// TODO. This ternary Boolean operator.
    ABCOp1ETodo3 = 0x3_1e,
    /// TODO. This ternary Boolean operator.
    ABCOp1FTodo3 = 0x3_1f,

    /// TODO. This ternary Boolean operator.
    ABCOp20Todo3 = 0x3_20,
    /// TODO. This ternary Boolean operator.
    ABCOp21Todo3 = 0x3_21,
    /// TODO. This ternary Boolean operator.
    NotImpliesAB3 = 0x3_22,
    /// TODO. This ternary Boolean operator.
    ABCOp23Todo3 = 0x3_23,
    /// TODO. This ternary Boolean operator.
    ABCOp24Todo3 = 0x3_24,
    /// TODO. This ternary Boolean operator.
    ABCOp25Todo3 = 0x3_25,
    /// TODO. This ternary Boolean operator.
    ABCOp26Todo3 = 0x3_26,
    /// `NotLogicalIf` ternary Boolean operator on first, second, and third arguments.
    NotIfABC3 = 0x3_27,
    /// TODO. This ternary Boolean operator.
    ABCOp28Todo3 = 0x3_28,
    /// TODO. This ternary Boolean operator.
    ABCOp29Todo3 = 0x3_29,
    /// TODO. This ternary Boolean operator.
    ABCOp2ATodo3 = 0x3_2a,
    /// TODO. This ternary Boolean operator.
    ABCOp2BTodo3 = 0x3_2b,
    /// TODO. This ternary Boolean operator.
    ABCOp2CTodo3 = 0x3_2c,
    /// TODO. This ternary Boolean operator.
    ABCOp2DTodo3 = 0x3_2d,
    /// TODO. This ternary Boolean operator.
    ABCOp2ETodo3 = 0x3_2e,
    /// TODO. This ternary Boolean operator.
    ABCOp2FTodo3 = 0x3_2f,

    /// TODO. This ternary Boolean operator.
    ABCOp30Todo3 = 0x3_30,
    /// TODO. This ternary Boolean operator.
    ABCOp31Todo3 = 0x3_31,
    /// TODO. This ternary Boolean operator.
    ABCOp32Todo3 = 0x332,
    /// `Not` ternary Boolean operator operating on second argument.
    ///
    /// But see `IdA1`, `IdB2`
    NotB3 = 0x3_33,
    /// TODO. This ternary Boolean operator.
    ABCOp34Todo3 = 0x3_34,
    /// TODO. This ternary Boolean operator.
    ABCOp35Todo3 = 0x3_35,
    /// TODO. This ternary Boolean operator.
    ABCOp36Todo3 = 0x3_36,
    /// TODO. This ternary Boolean operator.
    ABCOp37Todo3 = 0x3_37,
    /// TODO. This ternary Boolean operator.
    ABCOp38Todo3 = 0x3_38,
    /// TODO. This ternary Boolean operator.
    ABCOp39Todo3 = 0x3_39,
    /// TODO. This ternary Boolean operator.
    ABCOp3ATodo3 = 0x3_3a,
    /// TODO. This ternary Boolean operator.
    ABCOp3BTodo3 = 0x3_3b,
    /// TODO. This ternary Boolean operator.
    ABCOp3CTodo3 = 0x3_3c,
    /// TODO. This ternary Boolean operator.
    ABCOp3DTodo3 = 0x3_3d,
    /// TODO. This ternary Boolean operator.
    ABCOp3ETodo3 = 0x3_3e,
    /// TODO. This ternary Boolean operator.
    ABCOp3FTodo3 = 0x3_3f,

    /// TODO. This ternary Boolean operator.
    ABCOp40Todo3 = 0x3_40,
    /// TODO. This ternary Boolean operator.
    ABCOp41Todo3 = 0x3_41,
    /// TODO. This ternary Boolean operator.
    ABCOp42Todo3 = 0x3_42,
    /// TODO. This ternary Boolean operator.
    ABCOp43Todo3 = 0x3_43,
    /// TODO. This ternary Boolean operator.
    NotImpliesBA3 = 0x3_44,
    /// `NotLogicalIf` ternary Boolean operator on third, second, and first arguments.
    NotIfCBA3 = 0x3_45,
    /// TODO. This ternary Boolean operator.
    ABCOp46Todo3 = 0x3_46,
    /// `NotLogicalIf` ternary Boolean operator on second, first, and third arguments.
    NotIfBAC3 = 0x3_47,
    /// TODO. This ternary Boolean operator.
    ABCOp48Todo3 = 0x3_48,
    /// TODO. This ternary Boolean operator.
    ABCOp49Todo3 = 0x3_49,
    /// TODO. This ternary Boolean operator.
    ABCOp4ATodo3 = 0x3_4a,
    /// TODO. This ternary Boolean operator.
    ABCOp4BTodo3 = 0x3_4b,
    /// TODO. This ternary Boolean operator.
    ABCOp4CTodo3 = 0x3_4c,
    /// TODO. This ternary Boolean operator.
    ABCOp4DTodo3 = 0x3_4d,
    /// TODO. This ternary Boolean operator.
    ABCOp4ETodo3 = 0x3_4e,
    /// TODO. This ternary Boolean operator.
    ABCOp4FTodo3 = 0x3_4f,

    /// TODO. This ternary Boolean operator.
    ABCOp50Todo3 = 0x3_50,
    /// TODO. This ternary Boolean operator.
    ABCOp51Todo3 = 0x3_51,
    /// TODO. This ternary Boolean operator.
    ABCOp52Todo3 = 0x3_52,
    /// `NotLogicalIf` ternary Boolean operator on third, first, and second arguments.
    NotIfCAB3 = 0x3_53,
    /// TODO. This ternary Boolean operator.
    ABCOp54Todo3 = 0x3_54,
    /// `Not` ternary Boolean operator operating on first argument.
    ///
    /// But see `IdA1`
    NotA3 = 0x3_55,
    /// TODO. This ternary Boolean operator.
    ABCOp56Todo3 = 0x3_56,
    /// TODO. This ternary Boolean operator.
    ABCOp57Todo3 = 0x3_57,
    /// TODO. This ternary Boolean operator.
    ABCOp58Todo3 = 0x3_58,
    /// TODO. This ternary Boolean operator.
    ABCOp59Todo3 = 0x3_59,
    /// TODO. This ternary Boolean operator.
    ABCOp5ATodo3 = 0x3_5a,
    /// TODO. This ternary Boolean operator.
    ABCOp5BTodo3 = 0x3_5b,
    /// TODO. This ternary Boolean operator.
    ABCOp5CTodo3 = 0x3_5c,
    /// TODO. This ternary Boolean operator.
    ABCOp5DTodo3 = 0x3_5d,
    /// TODO. This ternary Boolean operator.
    ABCOp5ETodo3 = 0x3_5e,
    /// TODO. This ternary Boolean operator.
    ABCOp5FTodo3 = 0x3_5f,

    /// TODO. This ternary Boolean operator.
    ABCOp60Todo3 = 0x3_60,
    /// TODO. This ternary Boolean operator.
    ABCOp61Todo3 = 0x3_61,
    /// TODO. This ternary Boolean operator.
    ABCOp62Todo3 = 0x3_62,
    /// TODO. This ternary Boolean operator.
    ABCOp63Todo3 = 0x3_63,
    /// TODO. This ternary Boolean operator.
    ABCOp64Todo3 = 0x364,
    /// TODO. This ternary Boolean operator.
    ABCOp65Todo3 = 0x3_65,
    /// `ExclusiveOr` ternary Boolean operator on the first two arguments.
    XorAB3 = 0x3_66,
    /// TODO. This ternary Boolean operator.
    ABCOp67Todo3 = 0x3_67,
    /// TODO. This ternary Boolean operator.
    ABCOp68Todo3 = 0x3_68,
    /// `NotExclusiveOr3` ternary Boolean operator.
    NotXorABC3 = 0x3_69,
    /// TODO. This ternary Boolean operator.
    ABCOp6ATodo3 = 0x3_6a,
    /// TODO. This ternary Boolean operator.
    ABCOp6BTodo3 = 0x3_6b,
    /// TODO. This ternary Boolean operator.
    ABCOp6CTodo3 = 0x3_6c,
    /// TODO. This ternary Boolean operator.
    ABCOp6DTodo3 = 0x3_6d,
    /// TODO. This ternary Boolean operator.
    ABCOp6ETodo3 = 0x3_6e,
    /// TODO. This ternary Boolean operator.
    ABCOp6FTodo3 = 0x3_6f,

    /// TODO. This ternary Boolean operator.
    ABCOp70Todo3 = 0x3_70,
    /// TODO. This ternary Boolean operator.
    ABCOp71Todo3 = 0x3_71,
    /// TODO. This ternary Boolean operator.
    ABCOp72Todo3 = 0x3_72,
    /// TODO. This ternary Boolean operator.
    ABCOp73Todo3 = 0x3_73,
    /// TODO. This ternary Boolean operator.
    ABCOp74Todo3 = 0x3_74,
    /// TODO. This ternary Boolean operator.
    ABCOp75Todo3 = 0x3_75,
    /// TODO. This ternary Boolean operator.
    ABCOp76Todo3 = 0x3_76,
    /// `NotAnd` ternary Boolean operator on the first two arguments.
    ///
    /// But see `NotAndAB2`
    NotAndAB3 = 0x3_77,
    /// TODO. This ternary Boolean operator.
    ABCOp78Todo3 = 0x3_78,
    /// TODO. This ternary Boolean operator.
    ABCOp79Todo3 = 0x3_79,
    /// TODO. This ternary Boolean operator.
    ABCOp7ATodo3 = 0x3_7a,
    /// TODO. This ternary Boolean operator.
    ABCOp7BTodo3 = 0x3_7b,
    /// TODO. This ternary Boolean operator.
    ABCOp7CTodo3 = 0x3_7c,
    /// TODO. This ternary Boolean operator.
    ABCOp7DTodo3 = 0x3_7d,
    /// TODO. This ternary Boolean operator.
    ABCOp7ETodo3 = 0x3_7e,
    /// `NotAnd3` ternary Boolean operator.
    NotAndABC3 = 0x3_7f,

    /// `And3` ternary Boolean operator.
    AndABC3 = 0x3_80,
    /// TODO. This ternary Boolean operator.
    ABCOp81Todo3 = 0x3_81,
    /// TODO. This ternary Boolean operator.
    ABCOp82Todo3 = 0x3_82,
    /// TODO. This ternary Boolean operator.
    ABCOp83Todo3 = 0x3_83,
    /// TODO. This ternary Boolean operator.
    ABCOp84Todo3 = 0x3_84,
    /// TODO. This ternary Boolean operator.
    ABCOp85Todo3 = 0x3_85,
    /// TODO. This ternary Boolean operator.
    ABCOp86Todo3 = 0x3_86,
    /// TODO. This ternary Boolean operator.
    ABCOp87Todo3 = 0x3_87,
    /// `And` ternary Boolean operator on first two arguments.
    ///
    /// But see `AndAB2`
    AndAB3 = 0x3_88,
    /// TODO. This ternary Boolean operator.
    ABCOp89Todo3 = 0x3_89,
    /// TODO. This ternary Boolean operator.
    ABCOp8ATodo3 = 0x3_8a,
    /// TODO. This ternary Boolean operator.
    ABCOp8BTodo3 = 0x3_8b,
    /// TODO. This ternary Boolean operator.
    ABCOp8CTodo3 = 0x3_8c,
    /// TODO. This ternary Boolean operator.
    ABCOp8DTodo3 = 0x3_8d,
    /// TODO. This ternary Boolean operator.
    ABCOp8ETodo3 = 0x3_8e,
    /// TODO. This ternary Boolean operator.
    ABCOp8FTodo3 = 0x3_8f,

    /// TODO. This ternary Boolean operator.
    ABCOp90Todo3 = 0x3_90,
    /// TODO. This ternary Boolean operator.
    ABCOp91Todo3 = 0x3_91,
    /// TODO. This ternary Boolean operator.
    ABCOp92Todo3 = 0x3_92,
    /// TODO. This ternary Boolean operator.
    ABCOp93Todo3 = 0x3_93,
    /// TODO. This ternary Boolean operator.
    ABCOp94Todo3 = 0x3_94,
    /// TODO. This ternary Boolean operator.
    ABCOp95Todo3 = 0x3_95,

    /// `ExclusiveOr3` (`SumFromAdder`) ternary Boolean operator.
    XorABC3 = 0x3_96,
    /// TODO. This ternary Boolean operator.
    ABCOp97Todo3 = 0x3_97,
    /// TODO. This ternary Boolean operator.
    ABCOp98Todo3 = 0x3_98,
    /// `NotXor` ternary Boolean operator on first two arguments.
    ///
    /// But see `NotXorAB2`
    NotXorAB3 = 0x3_99,
    /// TODO. This ternary Boolean operator.
    ABCOp9ATodo3 = 0x3_9a,
    /// TODO. This ternary Boolean operator.
    ABCOp9BTodo3 = 0x3_9b,
    /// TODO. This ternary Boolean operator.
    ABCOp9CTodo3 = 0x3_9c,
    /// TODO. This ternary Boolean operator.
    ABCOp9DTodo3 = 0x3_9d,
    /// TODO. This ternary Boolean operator.
    ABCOp9ETodo3 = 0x3_9e,
    /// TODO. This ternary Boolean operator.
    ABCOp9FTodo3 = 0x3_9f,

    /// TODO. This ternary Boolean operator.
    ABCOpA0Todo3 = 0x3_a0,
    /// TODO. This ternary Boolean operator.
    ABCOpA1Todo3 = 0x3_a1,
    /// TODO. This ternary Boolean operator.
    ABCOpA2Todo3 = 0x3_a2,
    /// TODO. This ternary Boolean operator.
    ABCOpA3Todo3 = 0x3_a3,
    /// TODO. This ternary Boolean operator.
    ABCOpA4Todo3 = 0x3_a4,
    /// TODO. This ternary Boolean operator.
    ABCOpA5Todo3 = 0x3_a5,
    /// TODO. This ternary Boolean operator.
    ABCOpA6Todo3 = 0x3_a6,
    /// TODO. This ternary Boolean operator.
    ABCOpA7Todo3 = 0x3_a7,
    /// TODO. This ternary Boolean operator.
    ABCOpA8Todo3 = 0x3_a8,
    /// TODO. This ternary Boolean operator.
    ABCOpA9Todo3 = 0x3_a9,
    /// Identity ternary Boolean operator operating on first argument.
    ///
    /// But see `IdA1`
    IdA3 = 0x3_aa,
    /// TODO. This ternary Boolean operator.
    ABCOpABTodo3 = 0x3_ab,
    /// `LogicalIf` ternary Boolean operator on third, first, and first arguments.
    IfCAB3 = 0x3_ac,
    /// TODO. This ternary Boolean operator.
    ABCOpADTodo3 = 0x3_ad,
    /// TODO. This ternary Boolean operator.
    ABCOpAETodo3 = 0x3_ae,
    /// TODO. This ternary Boolean operator.
    ABCOpAFTodo3 = 0x3_af,

    /// TODO. This ternary Boolean operator.
    ABCOpB0Todo3 = 0x3_b0,
    /// TODO. This ternary Boolean operator.
    ABCOpB1Todo3 = 0x3_b1,
    /// TODO. This ternary Boolean operator.
    ABCOpB2Todo3 = 0x3_b2,
    /// TODO. This ternary Boolean operator.
    ABCOpB3Todo3 = 0x3_b3,
    /// TODO. This ternary Boolean operator.
    ABCOpB4Todo3 = 0x3_b4,
    /// TODO. This ternary Boolean operator.
    ABCOpB5Todo3 = 0x3_b5,
    /// TODO. This ternary Boolean operator.
    ABCOpB6Todo3 = 0x3_b6,
    /// TODO. This ternary Boolean operator.
    ABCOpB7Todo3 = 0x3_b7,
    /// `LogicalIf` ternary Boolean operator on second, first, and third arguments.
    IfBAC3 = 0x3_b8,
    /// TODO. This ternary Boolean operator.
    ABCOpB9Todo3 = 0x3_b9,
    /// TODO. This ternary Boolean operator.
    ABCOpBATodo3 = 0x3_ba,
    /// `RevImplies` ternary Boolean operator on first two arguments.
    ///
    /// But see `ImpliesBA2`
    ImpliesBA3 = 0x3_bb,
    /// TODO. This ternary Boolean operator.
    ABCOpBCTodo3 = 0x3_bc,
    /// TODO. This ternary Boolean operator.
    ABCOpBDTodo3 = 0x3_bd,
    /// TODO. This ternary Boolean operator.
    ABCOpBETodo3 = 0x3_be,
    /// TODO. This ternary Boolean operator.
    ABCOpBFTodo3 = 0x3_bf,

    /// TODO. This ternary Boolean operator.
    ABCOpC0Todo3 = 0x3_c0,
    /// TODO. This ternary Boolean operator.
    ABCOpC1Todo3 = 0x3_c1,
    /// TODO. This ternary Boolean operator.
    ABCOpC2Todo3 = 0x3_c2,
    /// TODO. This ternary Boolean operator.
    ABCOpC3Todo3 = 0x3_c3,
    /// TODO. This ternary Boolean operator.
    ABCOpC4Todo3 = 0x3_c4,
    /// TODO. This ternary Boolean operator.
    ABCOpC5Todo3 = 0x3_c5,
    /// TODO. This ternary Boolean operator.
    ABCOpC6Todo3 = 0x3_c6,
    /// TODO. This ternary Boolean operator.
    ABCOpC7Todo3 = 0x3_c7,
    /// TODO. This ternary Boolean operator.
    ABCOpC8Todo3 = 0x3_c8,
    /// TODO. This ternary Boolean operator.
    ABCOpC9Todo3 = 0x3_c9,
    /// `LogicalIf` ternary Boolean operator on third, second, and first arguments.
    IfCBA3 = 0x3_ca,
    /// TODO. This ternary Boolean operator.
    ABCOpCBTodo3 = 0x3_cb,
    /// Identity ternary Boolean operator operating on second argument.
    ///
    /// But see `IdA1`, `IdB2`
    IdB3 = 0x3_cc,
    /// TODO. This ternary Boolean operator.
    ABCOpCDTodo3 = 0x3_cd,
    /// TODO. This ternary Boolean operator.
    ABCOpCETodo3 = 0x3_ce,
    /// TODO. This ternary Boolean operator.
    ABCOpCFTodo3 = 0x3_cf,

    /// TODO. This ternary Boolean operator.
    ABCOpD0Todo3 = 0x3_d0,
    /// TODO. This ternary Boolean operator.
    ABCOpD1Todo3 = 0x3_d1,
    /// TODO. This ternary Boolean operator.
    ABCOpD2Todo3 = 0x3_d2,
    /// TODO. This ternary Boolean operator.
    ABCOpD3Todo3 = 0x3_d3,
    /// TODO. This ternary Boolean operator.
    ABCOpD4Todo3 = 0x3_d4,
    /// TODO. This ternary Boolean operator.
    ABCOpD5Todo3 = 0x3_d5,
    /// TODO. This ternary Boolean operator.
    ABCOpD6Todo3 = 0x3_d6,
    /// TODO. This ternary Boolean operator.
    ABCOpD7Todo3 = 0x3_d7,

    /// `LogicalIf` ternary Boolean operator on first, second, and third arguments.
    IfABC3 = 0x3_d8,
    /// TODO. This ternary Boolean operator.
    ABCOpD9Todo3 = 0x3_d9,
    /// TODO. This ternary Boolean operator.
    ABCOpDATodo3 = 0x3_da,
    /// TODO. This ternary Boolean operator.
    ABCOpDBTodo3 = 0x3_db,
    /// TODO. This ternary Boolean operator.
    ABCOpDCTodo3 = 0x3_dc,
    /// `Implies` ternary Boolean operator on first two arguments.
    ///
    /// But see `ImpliesAB2`
    ImpliesAB3 = 0x3_dd,
    /// TODO. This ternary Boolean operator.
    ABCOpDETodo3 = 0x3_de,
    /// TODO. This ternary Boolean operator.
    ABCOpDFTodo3 = 0x3_df,

    /// TODO. This ternary Boolean operator.
    ABCOpE0Todo3 = 0x3_e0,
    /// TODO. This ternary Boolean operator.
    ABCOpE1Todo3 = 0x3_e1,

    /// `LogicalIf` ternary Boolean operator on second, third, and first arguments.
    IfBCA3 = 0x3_e2,
    /// TODO. This ternary Boolean operator.
    ABCOpE3Todo3 = 0x3_e3,
    /// `LogicalIf` ternary Boolean operator on first, third, and second arguments.
    IfACB3 = 0x3_e4,
    /// TODO. This ternary Boolean operator.
    ABCOpE5Todo3 = 0x3_e5,
    /// TODO. This ternary Boolean operator.
    ABCOpE6Todo3 = 0x3_e6,
    /// TODO. This ternary Boolean operator.
    ABCOpE7Todo3 = 0x3_e7,
    /// TODO. This ternary Boolean operator.
    ABCOpE8Todo3 = 0x3_e8,
    /// TODO. This ternary Boolean operator.
    ABCOpE9Todo3 = 0x3_e9,
    /// TODO. This ternary Boolean operator.
    ABCOpEATodo3 = 0x3_ea,
    /// TODO. This ternary Boolean operator.
    ABCOpEBTodo3 = 0x3_eb,
    /// TODO. This ternary Boolean operator.
    ABCOpECTodo3 = 0x3_ec,
    /// TODO. This ternary Boolean operator.
    ABCOpEDTodo3 = 0x3_ed,
    /// `Or` ternary Boolean operator on first two arguments.
    ///
    /// But see `OrAB2`
    OrAB3 = 0x3_ee,
    /// TODO. This ternary Boolean operator.
    ABCOpEFTodo3 = 0x3_ef,

    /// Identity ternary Boolean operator operating on third argument.
    ///
    /// But see `IdA1`, `IdB2`
    IdC3 = 0x3_f0,
    /// TODO. This ternary Boolean operator.
    ABCOpF1Todo3 = 0x3_f1,
    /// TODO. This ternary Boolean operator.
    ABCOpF2Todo3 = 0x3_f2,
    /// TODO. This ternary Boolean operator.
    ABCOpF3Todo3 = 0x3_f3,
    /// TODO. This ternary Boolean operator.
    ABCOpF4Todo3 = 0x3_f4,
    /// TODO. This ternary Boolean operator.
    ABCOpF5Todo3 = 0x3_f5,
    /// TODO. This ternary Boolean operator.
    ABCOpF6Todo3 = 0x3_f6,
    /// TODO. This ternary Boolean operator.
    ABCOpF7Todo3 = 0x3_f7,
    /// TODO. This ternary Boolean operator.
    ABCOpF8Todo3 = 0x3_f8,
    /// TODO. This ternary Boolean operator.
    ABCOpF9Todo3 = 0x3_f9,
    /// TODO. This ternary Boolean operator.
    ABCOpFATodo3 = 0x3_fa,
    /// TODO. This ternary Boolean operator.
    ABCOpFBTodo3 = 0x3_fb,
    /// TODO. This ternary Boolean operator.
    ABCOpFCTodo3 = 0x3_fc,
    /// TODO. This ternary Boolean operator.
    ABCOpFDTodo3 = 0x3_fd,
    /// `Or3` ternary Boolean operator.
    OrABC3 = 0x3_fe,
    /// True binary ternary operator.
    ///
    /// But see `True0`
    True3 = 0x3_ff,
}

/// A Node wrapper for `BooleanSimpleOp` which works with any Type that implements Boolean.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct BooleanSimpleNode<Ty: Type>(BooleanSimpleOp, PhantomData<Ty>);

impl<Ty: Type> Display for BooleanSimpleNode<Ty> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&(self.0), f)
    }
}

impl<Ty: Type> Node for BooleanSimpleNode<Ty> {
    type Type = Ty;

    fn get_type_and_index(&self) -> Result<(Self::Type, usize), MguError> {
        Ok((Self::Type::try_boolean()?, (self.0) as usize))
    }

    fn get_arity(&self) -> Result<usize, MguError> {
        Ok(((self.0) as usize) >> 8)
    }

    fn get_slot_type(&self, index: usize) -> Result<Self::Type, MguError> {
        let n = ((self.0) as usize) >> 8;
        if index < n {
            Ok(Self::Type::try_boolean()?)
        } else {
            Err(MguError::from_index_and_len::<SimpleType, usize, usize>(
                None, index, n,
            ))
        }
    }
}

impl BooleanSimpleOp {
    /// Get the arity of the operator.
    #[inline]
    pub fn get_arity(&self) -> u8 {
        ((*self as u16 >> 8) & 0x3) as u8
    }

    /// Get the truth table of the operator as if it applied to 3 variables.
    ///
    /// This is compatible with Mathematica's `BooleanFunction[code3,  {a, b, c}]`.
    ///
    /// The reduced truth table is `code_n = (code3 as u16) & ((1u16<<(1<<n))-1)` where `n` is the arity.
    /// where `n` is the arity.
    #[inline]
    pub fn get_code3(&self) -> u8 {
        (*self as u16 & 0xff) as u8
    }

    /// Evaluate the Boolean operator on 0 inputs.
    ///
    /// This works only for `BooleanSimpleOp::True0 `and `BooleanSimpleOp::False0` and returns None for operators with higher arities.
    pub fn eval0<B, U, const N: usize>(&self) -> Option<B>
    where
        B: UnsignedBits<U, N>,
        U: Clone + BitAnd<Output = U> + BitOr<Output = U> + BitXor<Output = U>,
    {
        if self.get_arity() > 0 {
            return None;
        }
        Self::eval1::<B, U, N>(self, &(B::from_bool(false))) // TODO: replace this with a 2-branch match.
    }

    /// Evaluate the Boolean operator on 1 input.
    ///
    /// This works for `BooleanSimpleOp::True0` and `BooleanSimpleOp::False0`. but ignores the argument.
    /// This works similarly for `BooleanSimpleOp::True1` and `BooleanSimpleOp::False1` and as expected for `BooleanSimpleOp::NotA1` and `BooleanSimpleOp::IdA1`
    /// and returns None for operators with higher arities.
    pub fn eval1<B, U, const N: usize>(&self, a: &B) -> Option<B>
    where
        B: UnsignedBits<U, N>,
        U: Clone + BitAnd<Output = U> + BitOr<Output = U> + BitXor<Output = U>,
    {
        if self.get_arity() > 1 {
            return None;
        }
        Self::eval2::<B, U, N>(self, a, &(B::from_bool(false))) // TODO: replace this with a 4-branch match.
    }

    /// Evaluate the Boolean operator on 2 inputs.
    ///
    /// This silently ignores the last arguments if the operator has arity lower than 2
    /// and returns None for higher arities.
    pub fn eval2<B, U, const N: usize>(&self, a: &B, b: &B) -> Option<B>
    where
        B: UnsignedBits<U, N>,
        U: Clone + BitAnd<Output = U> + BitOr<Output = U> + BitXor<Output = U>,
    {
        if self.get_arity() > 2 {
            return None;
        }
        Self::eval3::<B, U, N>(self, a, b, &(B::from_bool(false))) // TODO: replace this with a 16-branch match.
    }

    /// Evaluate the Boolean operator on 3 inputs.
    ///
    /// This silently ignores the last arguments if the operator has arity lower than 3
    /// and returns None for higher arities, if any are ever defined.
    pub fn eval3<B, U, const N: usize>(&self, a: &B, b: &B, c: &B) -> Option<B>
    where
        B: UnsignedBits<U, N>,
        U: Clone + BitAnd<Output = U> + BitOr<Output = U> + BitXor<Output = U>,
    {
        use BooleanSimpleOp::*;
        if self.get_arity() > 3 {
            return None;
        }
        Some(match self {
            False0 | False1 | False2 | False3 => B::from_bool(false),
            NotOrABC3 => !((a.clone()) | (b.clone()) | (c.clone())),
            AndANotOrBC3 => (a.clone()) & !((b.clone()) | (c.clone())),
            NorOrBC3 => !((b.clone()) | (c.clone())),
            AndBNotOrAC3 => todo!(),
            NotOrAC3 => todo!(),
            AndCNotOrAB3 => todo!(),
            NotOrCAndAB3 => todo!(),
            And3ABNotC3 => todo!(),
            NotOrCXOrAB3 => todo!(),
            ABCOp0ATodo3 => todo!(),
            ABCOp0BTodo3 => todo!(),
            ABCOp0CTodo3 => todo!(),
            ABCOp0DTodo3 => todo!(),
            ABCOp0ETodo3 => todo!(),
            NotC3 => !(c.clone()),

            ABCOp10Todo3 => todo!(),
            NotOrAB2 | NotOrAB3 => !(a.clone() | b.clone()),
            ABCOp12Todo3 => todo!(),
            ABCOp13Todo3 => todo!(),
            ABCOp14Todo3 => todo!(),
            ABCOp15Todo3 => todo!(),
            ABCOp16Todo3 => todo!(),
            ABCOp17Todo3 => todo!(),
            ABCOp18Todo3 => todo!(),
            ABCOp19Todo3 => todo!(),
            ABCOp1ATodo3 => todo!(),
            NotIfACB3 => todo!(),
            ABCOp1CTodo3 => todo!(),
            NotIfBCA3 => todo!(),
            ABCOp1ETodo3 => todo!(),
            ABCOp1FTodo3 => todo!(),

            ABCOp20Todo3 => todo!(),
            ABCOp21Todo3 => todo!(),
            NotImpliesAB2 | NotImpliesAB3 => !(!(a.clone()) | b.clone()),
            ABCOp23Todo3 => todo!(),
            ABCOp24Todo3 => todo!(),
            ABCOp25Todo3 => todo!(),
            ABCOp26Todo3 => todo!(),
            NotIfABC3 => todo!(),
            ABCOp28Todo3 => todo!(),
            ABCOp29Todo3 => todo!(),
            ABCOp2ATodo3 => todo!(),
            ABCOp2BTodo3 => todo!(),
            ABCOp2CTodo3 => todo!(),
            ABCOp2DTodo3 => todo!(),
            ABCOp2ETodo3 => todo!(),
            ABCOp2FTodo3 => todo!(),

            ABCOp30Todo3 => todo!(),
            ABCOp31Todo3 => todo!(),
            ABCOp32Todo3 => todo!(),
            NotB2 | NotB3 => !(b.clone()),
            ABCOp34Todo3 => todo!(),
            ABCOp35Todo3 => todo!(),
            ABCOp36Todo3 => todo!(),
            ABCOp37Todo3 => todo!(),
            ABCOp38Todo3 => todo!(),
            ABCOp39Todo3 => todo!(),
            ABCOp3ATodo3 => todo!(),
            ABCOp3BTodo3 => todo!(),
            ABCOp3CTodo3 => todo!(),
            ABCOp3DTodo3 => todo!(),
            ABCOp3ETodo3 => todo!(),
            ABCOp3FTodo3 => todo!(),

            ABCOp40Todo3 => todo!(),
            ABCOp41Todo3 => todo!(),
            ABCOp42Todo3 => todo!(),
            ABCOp43Todo3 => todo!(),
            NotImpliesBA2 | NotImpliesBA3 => !((a.clone()) | !(b.clone())),
            NotIfCBA3 => todo!(),
            ABCOp46Todo3 => todo!(),
            NotIfBAC3 => todo!(),
            ABCOp48Todo3 => todo!(),
            ABCOp49Todo3 => todo!(),
            ABCOp4ATodo3 => todo!(),
            ABCOp4BTodo3 => todo!(),
            ABCOp4CTodo3 => todo!(),
            ABCOp4DTodo3 => todo!(),
            ABCOp4ETodo3 => todo!(),
            ABCOp4FTodo3 => todo!(),

            ABCOp50Todo3 => todo!(),
            ABCOp51Todo3 => todo!(),
            ABCOp52Todo3 => todo!(),
            NotIfCAB3 => todo!(),
            ABCOp54Todo3 => todo!(),
            NotA1 | NotA2 | NotA3 => !(a.clone()),
            ABCOp56Todo3 => todo!(),
            ABCOp57Todo3 => todo!(),
            ABCOp58Todo3 => todo!(),
            ABCOp59Todo3 => todo!(),
            ABCOp5ATodo3 => todo!(),
            ABCOp5BTodo3 => todo!(),
            ABCOp5CTodo3 => todo!(),
            ABCOp5DTodo3 => todo!(),
            ABCOp5ETodo3 => todo!(),
            ABCOp5FTodo3 => todo!(),

            ABCOp60Todo3 => todo!(),
            ABCOp61Todo3 => todo!(),
            ABCOp62Todo3 => todo!(),
            ABCOp63Todo3 => todo!(),
            ABCOp64Todo3 => todo!(),
            ABCOp65Todo3 => todo!(),
            XorAB2 | XorAB3 => (a.clone()) ^ (b.clone()),
            ABCOp67Todo3 => todo!(),
            ABCOp68Todo3 => todo!(),
            NotXorABC3 => todo!(),
            ABCOp6ATodo3 => todo!(),
            ABCOp6BTodo3 => todo!(),
            ABCOp6CTodo3 => todo!(),
            ABCOp6DTodo3 => todo!(),
            ABCOp6ETodo3 => todo!(),
            ABCOp6FTodo3 => todo!(),

            ABCOp70Todo3 => todo!(),
            ABCOp71Todo3 => todo!(),
            ABCOp72Todo3 => todo!(),
            ABCOp73Todo3 => todo!(),
            ABCOp74Todo3 => todo!(),
            ABCOp75Todo3 => todo!(),
            ABCOp76Todo3 => todo!(),
            NotAndAB2 | NotAndAB3 => !((a.clone()) & (b.clone())),
            ABCOp78Todo3 => todo!(),
            ABCOp79Todo3 => todo!(),
            ABCOp7ATodo3 => todo!(),
            ABCOp7BTodo3 => todo!(),
            ABCOp7CTodo3 => todo!(),
            ABCOp7DTodo3 => todo!(),
            ABCOp7ETodo3 => todo!(),
            NotAndABC3 => todo!(),

            AndABC3 => todo!(),
            ABCOp81Todo3 => todo!(),
            ABCOp82Todo3 => todo!(),
            ABCOp83Todo3 => todo!(),
            ABCOp84Todo3 => todo!(),
            ABCOp85Todo3 => todo!(),
            ABCOp86Todo3 => todo!(),
            ABCOp87Todo3 => todo!(),
            AndAB2 | AndAB3 => (a.clone()) & (b.clone()),
            ABCOp89Todo3 => todo!(),
            ABCOp8ATodo3 => todo!(),
            ABCOp8BTodo3 => todo!(),
            ABCOp8CTodo3 => todo!(),
            ABCOp8DTodo3 => todo!(),
            ABCOp8ETodo3 => todo!(),
            ABCOp8FTodo3 => todo!(),

            ABCOp90Todo3 => todo!(),
            ABCOp91Todo3 => todo!(),
            ABCOp92Todo3 => todo!(),
            ABCOp93Todo3 => todo!(),
            ABCOp94Todo3 => todo!(),
            ABCOp95Todo3 => todo!(),
            XorABC3 => todo!(),
            ABCOp97Todo3 => todo!(),
            ABCOp98Todo3 => todo!(),
            NotXorAB2 | NotXorAB3 => !((a.clone()) ^ (b.clone())),
            ABCOp9ATodo3 => todo!(),
            ABCOp9BTodo3 => todo!(),
            ABCOp9CTodo3 => todo!(),
            ABCOp9DTodo3 => todo!(),
            ABCOp9ETodo3 => todo!(),
            ABCOp9FTodo3 => todo!(),

            ABCOpA0Todo3 => todo!(),
            ABCOpA1Todo3 => todo!(),
            ABCOpA2Todo3 => todo!(),
            ABCOpA3Todo3 => todo!(),
            ABCOpA4Todo3 => todo!(),
            ABCOpA5Todo3 => todo!(),
            ABCOpA6Todo3 => todo!(),
            ABCOpA7Todo3 => todo!(),
            ABCOpA8Todo3 => todo!(),
            ABCOpA9Todo3 => todo!(),
            IdA1 | IdA2 | IdA3 => a.clone(),
            ABCOpABTodo3 => todo!(),
            IfCAB3 => todo!(),
            ABCOpADTodo3 => todo!(),
            ABCOpAETodo3 => todo!(),
            ABCOpAFTodo3 => todo!(),

            ABCOpB0Todo3 => todo!(),
            ABCOpB1Todo3 => todo!(),
            ABCOpB2Todo3 => todo!(),
            ABCOpB3Todo3 => todo!(),
            ABCOpB4Todo3 => todo!(),
            ABCOpB5Todo3 => todo!(),
            ABCOpB6Todo3 => todo!(),
            ABCOpB7Todo3 => todo!(),
            IfBAC3 => todo!(),
            ABCOpB9Todo3 => todo!(),
            ABCOpBATodo3 => todo!(),
            ImpliesBA2 | ImpliesBA3 => (a.clone()) | !(b.clone()),
            ABCOpBCTodo3 => todo!(),
            ABCOpBDTodo3 => todo!(),
            ABCOpBETodo3 => todo!(),
            ABCOpBFTodo3 => todo!(),

            ABCOpC0Todo3 => todo!(),
            ABCOpC1Todo3 => todo!(),
            ABCOpC2Todo3 => todo!(),
            ABCOpC3Todo3 => todo!(),
            ABCOpC4Todo3 => todo!(),
            ABCOpC5Todo3 => todo!(),
            ABCOpC6Todo3 => todo!(),
            ABCOpC7Todo3 => todo!(),
            ABCOpC8Todo3 => todo!(),
            ABCOpC9Todo3 => todo!(),
            IfCBA3 => todo!(),
            ABCOpCBTodo3 => todo!(),
            IdB2 | IdB3 => b.clone(),
            ABCOpCDTodo3 => todo!(),
            ABCOpCETodo3 => todo!(),
            ABCOpCFTodo3 => todo!(),

            ABCOpD0Todo3 => todo!(),
            ABCOpD1Todo3 => todo!(),
            ABCOpD2Todo3 => todo!(),
            ABCOpD3Todo3 => todo!(),
            ABCOpD4Todo3 => todo!(),
            ABCOpD5Todo3 => todo!(),
            ABCOpD6Todo3 => todo!(),
            ABCOpD7Todo3 => todo!(),
            IfABC3 => todo!(),
            ABCOpD9Todo3 => todo!(),
            ABCOpDATodo3 => todo!(),
            ABCOpDBTodo3 => todo!(),
            ABCOpDCTodo3 => todo!(),
            ImpliesAB2 | ImpliesAB3 => (!(a.clone())) | (b.clone()),
            ABCOpDETodo3 => todo!(),
            ABCOpDFTodo3 => todo!(),

            ABCOpE0Todo3 => todo!(),
            ABCOpE1Todo3 => todo!(),
            IfBCA3 => todo!(),
            ABCOpE3Todo3 => todo!(),
            IfACB3 => todo!(),
            ABCOpE5Todo3 => todo!(),
            ABCOpE6Todo3 => todo!(),
            ABCOpE7Todo3 => todo!(),
            ABCOpE8Todo3 => todo!(),
            ABCOpE9Todo3 => todo!(),
            ABCOpEATodo3 => todo!(),
            ABCOpEBTodo3 => todo!(),
            ABCOpECTodo3 => todo!(),
            ABCOpEDTodo3 => todo!(),
            OrAB2 | OrAB3 => (a.clone()) | (b.clone()),
            ABCOpEFTodo3 => todo!(),

            IdC3 => c.clone(),
            ABCOpF1Todo3 => todo!(),
            ABCOpF2Todo3 => todo!(),
            ABCOpF3Todo3 => todo!(),
            ABCOpF4Todo3 => todo!(),
            ABCOpF5Todo3 => todo!(),
            ABCOpF6Todo3 => todo!(),
            ABCOpF7Todo3 => todo!(),
            ABCOpF8Todo3 => todo!(),
            ABCOpF9Todo3 => todo!(),
            ABCOpFATodo3 => todo!(),
            ABCOpFBTodo3 => todo!(),
            ABCOpFCTodo3 => todo!(),
            ABCOpFDTodo3 => todo!(),
            OrABC3 => (a.clone()) | (b.clone()) | (c.clone()),
            True0 | True1 | True2 | True3 => B::from_bool(true),
        })
    }
}

#[cfg(feature = "bigint")]
use num_bigint::BigUint;

/// Checks if a Boolean `NodeByte` node is supported by this module.
///
/// | node | arity |
/// | ---- | ----- |
/// | [`True`] | 0 |
/// | [`False`] | 0 |
/// | [`Not`] | 1 |
/// | [`Implies`] | 2 |
/// | [`Biimp`] | 2 |
/// | [`And`] | 2 |
/// | [`Or`] | 2 |
/// | [`NotAnd`] | 2 |
/// | [`ExclusiveOr`] | 2 |
/// | [`NotOr`] | 2 |
/// | [`And3`] | 3 |
/// | [`Or3`] | 3 |
/// | [`SumFromAdder`] | 3 |
/// | [`CarryFromAdder`] | 3 |
/// | [`LogicalIf`] | 3 |
///
/// [`True`]: `crate::NodeByte::True`
/// [`False`]: `crate::NodeByte::False`
/// [`Not`]: `crate::NodeByte::Not`
/// [`Implies`]: `crate::NodeByte::Implies`
/// [`Biimp`]: `crate::NodeByte::Biimp`
/// [`And`]: `crate::NodeByte::And`
/// [`Or`]: `crate::NodeByte::Or`
/// [`NotAnd`]: `crate::NodeByte::NotAnd`
/// [`ExclusiveOr`]: `crate::NodeByte::ExclusiveOr`
/// [`NotOr`]: `crate::NodeByte::NotOr`
/// [`And3`]: `crate::NodeByte::And3`
/// [`Or3`]: `crate::NodeByte::Or3`
/// [`SumFromAdder`]: `crate::NodeByte::SumFromAdder`
/// [`CarryFromAdder`]: `crate::NodeByte::CarryFromAdder`
/// [`LogicalIf`]: `crate::NodeByte::LogicalIf`
pub fn is_supported_op(node: &NodeByte) -> bool {
    use NodeByte::*;
    matches!(
        node,
        True | False
            | Not
            | Implies
            | Biimp
            | And
            | Or
            | NotAnd
            | ExclusiveOr
            | NotOr
            | And3
            | Or3
            | SumFromAdder // aka `ExclusiveOr3`
            | CarryFromAdder // aka `Majority3`
            | LogicalIf
    )
}

/// Isolate the differences between various unsigned representations.
pub trait UnsignedBits<U, const N: usize>:
    Clone
    + DebugTrait
    + BitXor<Output = Self>
    + BitAnd<Output = Self>
    + BitOr<Output = Self>
    + Not<Output = Self>
where
    U: Clone + BitAnd<Output = U> + BitOr<Output = U> + BitXor<Output = U>,
{
    /// Mask for one's complement.
    fn mask() -> U;

    /// Return true if mask is the maximum value supported.
    fn is_mask_maximum(&self) -> bool;

    /// Return number of bits.
    fn n_bits() -> usize {
        1 << N
    }

    /// Return base 2 log of number of bits.
    fn n() -> usize {
        N
    }

    /// Convert a base-type value to this type.
    fn from_orig(orig: U) -> Self;

    /// Convert a Boolean value to this type.
    fn from_bool(orig: bool) -> Self {
        let m = Self::mask();
        Self::from_orig(if orig { m } else { m.clone() ^ m })
    }

    /// Set or reset a bit from 0..`2^N`, inclusive.
    ///
    /// # Errors
    ///
    /// TODO.
    fn set_bit(&mut self, bit_pos: u64, value: bool) -> Result<(), MguError>;

    /// Convenience method to evaluate a single node with no children.
    ///
    /// # Errors
    ///
    /// TODO.
    fn eval_boolean_nullary(node: &NodeByte) -> Result<Self, MguError> {
        use NodeByte::*;
        match node {
            True => Ok(Self::from_bool(true)),
            False => Ok(Self::from_bool(false)),
            _ => Err(MguError::UnknownError(690)),
        }
    }

    /// Convenience method to evaluate a single node with specified child.
    ///
    /// # Errors
    ///
    /// TODO.
    fn eval_boolean_unary<V>(&node: &NodeByte, a: &Self) -> Result<Self, MguError>
    where
        V: Metavariable,
    {
        use NodeByte::*;
        match node {
            Not => Ok(!a.clone()),
            _ => Err(MguError::UnknownError(691)),
        }
    }

    /// Convenience method to evaluate a single node with specified children.
    ///
    /// # Errors
    ///
    /// TODO.
    fn eval_boolean_binary<V>(node: &NodeByte, a: &Self, b: &Self) -> Result<Self, MguError>
    where
        V: Metavariable,
    {
        use NodeByte::*;
        match node {
            Implies => Ok((!a.clone()) | b.clone()),
            Biimp => Ok(!(a.clone() ^ b.clone())),
            And => Ok(a.clone() & b.clone()),
            Or => Ok(a.clone() | b.clone()),
            NotAnd => Ok(!(a.clone() & b.clone())),
            ExclusiveOr => Ok(a.clone() ^ b.clone()),
            NotOr => Ok(!(a.clone() | b.clone())),
            _ => Err(MguError::UnknownError(692)),
        }
    }

    /// Convenience method to evaluate a single node with specified children.
    ///
    /// # Errors
    ///
    /// TODO.
    fn eval_boolean_ternary<V>(
        node: &NodeByte,
        a: &Self,
        b: &Self,
        c: &Self,
    ) -> Result<Self, MguError>
    where
        V: Metavariable,
    {
        use NodeByte::*;
        match node {
            And3 => Ok(a.clone() & b.clone() & c.clone()),
            Or3 => Ok(a.clone() | b.clone() | c.clone()),
            SumFromAdder => Ok(a.clone() ^ b.clone() ^ c.clone()),
            CarryFromAdder => {
                Ok((a.clone() & b.clone()) | (a.clone() & c.clone()) | (b.clone() & c.clone()))
            }
            LogicalIf => Ok((a.clone() & b.clone()) | (!a.clone() & c.clone())),
            _ => Err(MguError::UnknownError(693)),
        }
    }

    /// Convenience method to evaluate a single node with specified children.
    ///
    /// # Errors
    ///
    /// TODO.
    fn eval_boolean_node<V>(node: &NodeByte, children: &[Self]) -> Result<Self, MguError>
    where
        V: Metavariable,
    {
        use NodeByte::*;
        match node {
            True | False => {
                let len = children.len();
                if len != 0 {
                    return Err(MguError::SlotsMismatch(len, 0));
                }
                Self::eval_boolean_nullary(node)
            }
            Not => {
                let len = children.len();
                if len != 1 {
                    return Err(MguError::SlotsMismatch(len, 1));
                }
                Self::eval_boolean_unary::<V>(node, &children[0])
            }
            Implies | Biimp | And | Or | NotAnd | ExclusiveOr | NotOr => {
                let len = children.len();
                if len != 2 {
                    return Err(MguError::SlotsMismatch(len, 2));
                }
                Self::eval_boolean_binary::<V>(node, &children[0], &children[1])
            }
            And3 | Or3 | SumFromAdder | CarryFromAdder | LogicalIf => {
                let len = children.len();
                if len != 3 {
                    return Err(MguError::SlotsMismatch(len, 3));
                }
                Self::eval_boolean_ternary::<V>(node, &children[0], &children[1], &children[2])
            }
            _ => Err(MguError::UnknownError(700)),
        }
    }

    /// Evaluate Boolean term in N variables.
    ///
    /// # Errors
    ///
    /// TODO.
    fn eval_boolean_term<Ty, V, No, CvtErr>(
        term: &EnumTerm<Ty, V, No>,
        vars: &[V],
    ) -> Result<Self, MguError>
    where
        Ty: Type,
        V: Metavariable<Type = Ty>,
        No: Node<Type = Ty> + TryInto<NodeByte, Error = CvtErr>,
        CvtErr: Into<MguError>,
    {
        match term {
            EnumTerm::Leaf(var) => {
                let typ = var.get_type()?;
                if !typ.is_boolean() {
                    return Err(MguError::from_found_and_expected_types(
                        false,
                        &typ,
                        &(Ty::try_boolean()?),
                    ));
                }
                let index = vars
                    .iter()
                    .position(|v| *v == *var)
                    .ok_or(MguError::UnknownError(702))?;
                if index >= N {
                    return Err(MguError::UnknownError(703));
                }

                if index >= 20 {
                    // Reasonable limit?
                    return Err(MguError::AllocationError(format!(
                        "Variable index {index} exceeds maximum 19 for 2^20 bits"
                    )));
                }

                let num_bits = 1u64 << (N as u32);
                let period = 1_u64 << (index + 1);
                if num_bits < period {
                    return Err(MguError::AllocationError(format!(
                        "num_bits ({num_bits}) must be at least 2^{} ({period}) for variable index {index}",
                        index + 1
                    )));
                }

                // Create alternating pattern: period = `2^(var_index+1)`, on for `2^var_index` bits
                // Pattern repeats with period `2^(var_index+1)`, and is high for the second half of each period

                let on_length = 1_u64 << index;

                let mut result = Self::from_bool(false);
                for bit_pos in 0..num_bits {
                    // Check if this bit position is in the "on" part of its period
                    let pos_in_period = bit_pos % period;
                    if pos_in_period >= on_length {
                        result.set_bit(bit_pos, true)?;
                    }
                }

                Ok(result)
            }

            EnumTerm::NodeOrLeaf(node, children) => {
                let node_converted: NodeByte = (node.clone()).try_into().map_err(|e| e.into())?;
                use NodeByte::*;
                match node_converted {
                    True | False | Not | Implies | Biimp | And | Or | NotAnd | ExclusiveOr
                    | NotOr | And3 | Or3 | SumFromAdder | CarryFromAdder | LogicalIf => {
                        let child_values = children
                            .iter()
                            .map(|t| Self::eval_boolean_term(t, vars))
                            .collect::<Vec<_>>();
                        if let Some(Err(err)) = child_values.iter().find(|x| (*x).is_err()) {
                            return Err(err.clone());
                        }
                        let child_values = child_values
                            .into_iter()
                            .map(|x| x.unwrap())
                            .collect::<Vec<_>>();
                        Self::eval_boolean_node::<V>(&node_converted, &child_values)
                    }
                    _ => Err(MguError::UnknownError(700)),
                }
            }
        }
    }
}

impl UnsignedBits<bool, 0> for bool {
    fn mask() -> bool {
        true
    }
    fn is_mask_maximum(&self) -> bool {
        true
    }

    fn from_orig(orig: bool) -> Self {
        orig
    }

    fn set_bit(&mut self, bit_pos: u64, value: bool) -> Result<(), MguError> {
        if bit_pos != 0 {
            Err(MguError::UnknownError(120))
        } else {
            *self = value;
            Ok(())
        }
    }
}

impl<const N: usize> UnsignedBits<u8, N> for u8 {
    fn mask() -> u8 {
        assert!(N <= 3);
        if N == 3 {
            return u8::MAX;
        }
        (1u8 << (1 << N)) - 1
    }
    fn is_mask_maximum(&self) -> bool {
        assert!(N <= 3);
        N == 3
    }

    fn n() -> usize {
        assert!(N <= 3);
        N
    }

    fn from_orig(orig: u8) -> Self {
        assert!(N <= 3);

        if N == 3 {
            return orig;
        }
        let mask = (1u8 << (1 << N)) - 1;
        mask & orig
    }

    fn set_bit(&mut self, bit_pos: u64, value: bool) -> Result<(), MguError> {
        assert!(N <= 3);
        let high_index = 1u64 << N;
        if bit_pos < high_index {
            if value {
                *self |= 1 << (bit_pos as u32);
            } else {
                let bit = 1u8 << (bit_pos as u32);
                let mask = if N == 3 {
                    u8::MAX
                } else {
                    (1u8 << (1 << N)) - 1
                };
                let bit = (bit & mask) ^ mask;
                *self &= bit;
            }
            Ok(())
        } else {
            Err(MguError::UnknownError(121))
        }
    }
}

/// A wrapper around `BigUint` to have it model truth tables on N Boolean variables.
#[cfg(feature = "bigint")]
#[derive(Clone, Debug)]
pub struct SomeBits<const N: usize>(BigUint);

#[cfg(feature = "bigint")]
impl<const N: usize> SomeBits<N> {
    /// A mask with `2^(2^N)` ones.
    pub fn all_ones_mask() -> Self {
        let one: BigUint = 1u32.into();
        Self(one.clone().pow(1 << N) - one)
    }
}

#[cfg(feature = "bigint")]
impl<const N: usize> UnsignedBits<SomeBits<N>, N> for SomeBits<N> {
    fn mask() -> SomeBits<N> {
        Self::all_ones_mask()
    }
    fn is_mask_maximum(&self) -> bool {
        false
    }
    fn n() -> usize {
        N
    }

    fn from_orig(orig: SomeBits<N>) -> Self {
        orig
    }

    fn set_bit(&mut self, bit_pos: u64, value: bool) -> Result<(), MguError> {
        let high_index = 1u64 << N;
        if bit_pos < high_index {
            self.0.set_bit(bit_pos, value);
            Ok(())
        } else {
            Err(MguError::UnknownError(119))
        }
    }
}

#[cfg(feature = "bigint")]
impl<const N: usize> BitAnd for SomeBits<N> {
    type Output = SomeBits<N>;

    fn bitand(self, rhs: Self) -> Self::Output {
        (SomeBits::<N>)(self.0 & rhs.0)
    }
}

#[cfg(feature = "bigint")]
impl<const N: usize> Not for SomeBits<N> {
    type Output = SomeBits<N>;

    fn not(self) -> Self::Output {
        (SomeBits::<N>)(self.0 ^ SomeBits::<N>::all_ones_mask().0)
    }
}

#[cfg(feature = "bigint")]
impl<const N: usize> BitOr for SomeBits<N> {
    type Output = SomeBits<N>;

    fn bitor(self, rhs: Self) -> Self::Output {
        (SomeBits::<N>)(self.0 | rhs.0)
    }
}

#[cfg(feature = "bigint")]
impl<const N: usize> BitXor for SomeBits<N> {
    type Output = SomeBits<N>;

    fn bitxor(self, rhs: Self) -> Self::Output {
        (SomeBits::<N>)(self.0 ^ rhs.0)
    }
}
