use std::fmt::Debug;

use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::target::BoolTarget;
use plonky2::iop::witness::{Witness, WitnessWrite};

use crate::frontend::builder::CircuitBuilder;
use crate::frontend::num::biguint::{BigUintTarget, CircuitBuilderBiguint};
use crate::frontend::num::u32::gadgets::arithmetic_u32::U32Target;
use crate::frontend::vars::{CircuitVariable, EvmVariable, U32Variable, Variable};
use crate::prelude::*;

#[derive(Clone, Debug)]
pub struct FloatVariable {
    pub x: U32Variable,
    pub z: U32Variable,
    pub a: U32Variable,
    pub b: U32Variable,
}

struct FloatValue {
    x: u32,
    z: u32,
    a: u32,
    b: u32,
}

impl CircuitVariable for FloatVariable {
    type ValueType<F: RichField> = FloatValue;

    fn init<F: RichField + Extendable<D>, const D: usize>(
        builder: &mut CircuitBuilder<F, D>,
    ) -> Self {
        Self {
            x: U32Variable::init(builder),
            z: U32Variable::init(builder),
            a: U32Variable::init(builder),
            b: U32Variable::init(builder),
        }
    }

    fn constant<F: RichField + Extendable<D>, const D: usize>(
        builder: &mut CircuitBuilder<F, D>,
        value: Self::ValueType<F>,
    ) -> Self {
        Self {
            x: U32Variable::constant(builder, value.x),
            z: U32Variable::constant(builder, value.z),
            a: U32Variable::constant(builder, value.a),
            b: U32Variable::constant(builder, value.b),
        }
    }

    fn variables(&self) -> Vec<Variable> {
        vec![self.x.0, self.z.0, self.a.0, self.b.0]
    }

    fn from_variables(variables: &[Variable]) -> Self {
        assert_eq!(variables.len(), 4);
        Self {
            x: U32Variable(variables[0]),
            z: U32Variable(variables[1]),
            a: U32Variable(variables[2]),
            b: U32Variable(variables[3]),
        }
    }

    fn get<F: RichField, W: Witness<F>>(&self, witness: &W) -> Self::ValueType<F> {
        let x = self.x.get(witness);
        let z = self.z.get(witness);
        let a = self.a.get(witness);
        let b = self.b.get(witness);
        FloatValue { x, z, a, b }
    }

    fn set<F: RichField, W: WitnessWrite<F>>(&self, witness: &mut W, value: Self::ValueType<F>) {
        self.x.set(witness, value.x);
        self.z.set(witness, value.z);
        self.a.set(witness, value.a);
        self.b.set(witness, value.b);
    }
}

impl EvmVariable for FloatVariable {
    fn encode<F: RichField + Extendable<D>, const D: usize>(
        &self,
        builder: &mut CircuitBuilder<F, D>,
    ) -> Vec<ByteVariable> {
        let mut bytes = Vec::new();
        bytes.extend_from_slice(&self.x.encode(builder));
        bytes.extend_from_slice(&self.z.encode(builder));
        bytes.extend_from_slice(&self.a.encode(builder));
        bytes.extend_from_slice(&self.b.encode(builder));
        bytes
    }

    fn decode<F: RichField + Extendable<D>, const D: usize>(
        builder: &mut CircuitBuilder<F, D>,
        bytes: &[ByteVariable],
    ) -> Self {
        assert_eq!(bytes.len(), 16);
        Self {
            x: U32Variable::decode(builder, &bytes[0..4]),
            z: U32Variable::decode(builder, &bytes[4..8]),
            a: U32Variable::decode(builder, &bytes[8..12]),
            b: U32Variable::decode(builder, &bytes[12..16]),
        }
    }

    fn encode_value<F: RichField>(value: Self::ValueType<F>) -> Vec<u8> {
        let mut bytes = Vec::new();
        bytes.extend_from_slice(&U32Variable::encode_value(value.x));
        bytes.extend_from_slice(&U32Variable::encode_value(value.z));
        bytes.extend_from_slice(&U32Variable::encode_value(value.a));
        bytes.extend_from_slice(&U32Variable::encode_value(value.b));
        bytes
    }

    fn decode_value<F: RichField>(bytes: &[u8]) -> Self::ValueType<F> {
        FloatValue {
            x: U32Variable::decode_value(&bytes[0..4]),
            z: U32Variable::decode_value(&bytes[4..8]),
            a: U32Variable::decode_value(&bytes[8..12]),
            b: U32Variable::decode_value(&bytes[12..16]),
        }
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Zero<F, D> for FloatVariable {
    fn zero(builder: &mut CircuitBuilder<F, D>) -> Self {
        let zero = U32Variable::zero(builder);
        let one = U32Variable::one(builder);
        Self {
            x: zero,
            z: zero,
            a: one,
            b: one,
        }
    }
}

impl<F: RichField + Extendable<D>, const D: usize> One<F, D> for FloatVariable {
    fn one(builder: &mut CircuitBuilder<F, D>) -> Self {
        let zero = Variable::zero(builder);
        let one = Variable::one(builder);
        Self {
            x: one,
            z: zero,
            a: one,
            b: one,
        }
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Add<F, D> for FloatVariable {
    type Output = Self;

    fn add(self, rhs: FloatVariable, builder: &mut CircuitBuilder<F, D>) -> Self::Output {
        builder.add(self.x, rhs);

        let self_target = self.0 .0;
        let rhs_target = rhs.0 .0;
        let self_biguint = BigUintTarget {
            limbs: vec![U32Target(self_target)],
        };
        let rhs_biguint = BigUintTarget {
            limbs: vec![U32Target(rhs_target)],
        };

        let sum_biguint = builder.api.add_biguint(&self_biguint, &rhs_biguint);

        // Get the least significant limb
        let sum = sum_biguint.limbs[0].0;

        Self(Variable(sum))
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Mul<F, D> for FloatVariable {
    type Output = Self;

    fn mul(self, rhs: U32Variable, builder: &mut CircuitBuilder<F, D>) -> Self::Output {
        let self_target = self.0 .0;
        let rhs_target = rhs.0 .0;
        let self_biguint = BigUintTarget {
            limbs: vec![U32Target(self_target)],
        };
        let rhs_biguint = BigUintTarget {
            limbs: vec![U32Target(rhs_target)],
        };

        let product_biguint = builder.api.mul_biguint(&self_biguint, &rhs_biguint);

        // Get the least significant limb
        let product = product_biguint.limbs[0].0;
        Self(Variable(product))
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Sub<F, D> for FloatVariable {
    type Output = Self;

    fn sub(self, rhs: U32Variable, builder: &mut CircuitBuilder<F, D>) -> Self::Output {
        let self_target = self.0 .0;
        let rhs_target = rhs.0 .0;
        let self_biguint = BigUintTarget {
            limbs: vec![U32Target(self_target)],
        };
        let rhs_biguint = BigUintTarget {
            limbs: vec![U32Target(rhs_target)],
        };

        let diff_biguint = builder.api.sub_biguint(&self_biguint, &rhs_biguint);
        let diff = diff_biguint.limbs[0].0;
        Self(Variable(diff))
    }
}

#[cfg(test)]
mod tests {
    use rand::Rng;

    use super::U32Variable;
    use crate::frontend::vars::EvmVariable;
    use crate::prelude::*;
}
