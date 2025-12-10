## Operators of arity 1 and 2 as tabulated by Prior following Bochenski and Łukasiewicz:

| Table        | Łukasiewicz | [`BooleanSimpleOp`] | Table        | Łukasiewicz | [`BooleanSimpleOp`] |
| ------------ | ----------- | ------------------- | ------------ | ----------- | ------------------- |
| (1, 0)       |             | [`IdA1`]            | (0, 1)       | N           | [`NotA1`]           |
| (1, 1, 1, 0) | A           | [`OrAB2`]           | (0, 0, 0, 1) | X           | [`NotOrAB2`]        |
| (1, 1, 0, 1) | B           | [`ImpliesBA2`]      | (0, 0, 1, 0) | M           | [`NotImpliesBA2`]   |
| (1, 0, 1, 1) | C           | [`ImpliesAB2`]      | (0, 1, 0, 0) | L           | [`NotImpliesAB2`]   |
| (0, 1, 1, 1) | D           | [`NotAndAB2`]       | (1, 0, 0, 0) | K           | [`AndAB2`]          |
| (1, 0, 0, 1) | E           | [`BiimpAB2`]        | (0, 1, 1, 0) | J           | [`XorAB2`]          |
| (0, 0, 1, 1) | F           | [`NotA2`]           | (1, 1, 0, 0) | I           | [`IdA2`]            |
| (0, 1, 0, 1) | G           | [`NotB2`]           | (1, 0, 1, 0) | H           | [`IdB2`]            |
| (0, 0, 0, 0) | O           | [`False2`]          | (1, 1, 1, 1) | V           | [`True2`]           |

Operators of arity 0 and 3 novel to this implementation:

| Additional | [`BooleanSimpleOp`] | Additional | [`BooleanSimpleOp`] |
| ---------- | ------------------- | ---------- | ------------------- |
| 0          | [`False0`]          | 1          | [`True0`]           |
| &amp;      | [`And3ABC3`]        | \|         | [`Or3ABC3`]         |
| +          | [`Xor3ABC3`]        | ^          | [`Majority3ABC3`]   |
| ?          | [`IfABC3`]          |            |                     |

**Reference:**

**Prior, A. N.** (1955) *Formal Logic*, pp. 4-13.
Available at <https://archive.org/details/formallogic0000anpr>

[`BooleanSimpleOp`]: `crate::bool_eval::BooleanSimpleOp`
[`IdA1`]: `crate::bool_eval::BooleanSimpleOp::IdA1`
[`NotA1`]: `crate::bool_eval::BooleanSimpleOp::NotA1`
[`False2`]: `crate::bool_eval::BooleanSimpleOp::False2`
[`NotOrAB2`]: `crate::bool_eval::BooleanSimpleOp::NotOrAB2`
[`NotImpliesAB2`]: `crate::bool_eval::BooleanSimpleOp::NotImpliesAB2`
[`NotB2`]: `crate::bool_eval::BooleanSimpleOp::NotB2`
[`NotImpliesBA2`]: `crate::bool_eval::BooleanSimpleOp::NotImpliesBA2`
[`NotA2`]: `crate::bool_eval::BooleanSimpleOp::NotA2`
[`XorAB2`]: `crate::bool_eval::BooleanSimpleOp::XorAB2`
[`NotAndAB2`]: `crate::bool_eval::BooleanSimpleOp::NotAndAB2`
[`AndAB2`]: `crate::bool_eval::BooleanSimpleOp::AndAB2`
[`BiimpAB2`]: `crate::bool_eval::BooleanSimpleOp::BiimpAB2`
[`IdA2`]: `crate::bool_eval::BooleanSimpleOp::IdA2`
[`ImpliesBA2`]: `crate::bool_eval::BooleanSimpleOp::ImpliesBA2`
[`IdB2`]: `crate::bool_eval::BooleanSimpleOp::IdB2`
[`ImpliesAB2`]: `crate::bool_eval::BooleanSimpleOp::ImpliesAB2`
[`OrAB2`]: `crate::bool_eval::BooleanSimpleOp::OrAB2`
[`True2`]: `crate::bool_eval::BooleanSimpleOp::True2`
[`False0`]: `crate::bool_eval::BooleanSimpleOp::False0`
[`True0`]: `crate::bool_eval::BooleanSimpleOp::True0`
[`And3ABC3`]: `crate::bool_eval::BooleanSimpleOp::And3ABC3`
[`Or3ABC3`]: `crate::bool_eval::BooleanSimpleOp::Or3ABC3`
[`Xor3ABC3`]: `crate::bool_eval::BooleanSimpleOp::Xor3ABC3`
[`Majority3ABC3`]: `crate::bool_eval::BooleanSimpleOp::Majority3ABC3`
[`IfABC3`]: `crate::bool_eval::BooleanSimpleOp::IfABC3`
