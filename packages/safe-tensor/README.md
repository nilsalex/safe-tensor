![Hackage-Deps](https://img.shields.io/hackage-deps/v/safe-tensor) [![Hackage](https://img.shields.io/hackage/v/sparse-tensor)](https://hackage.haskell.org/package/sparse-tensor) [![Build Status](https://travis-ci.org/nilsalex/safe-tensor.svg?branch=master)](https://travis-ci.org/nilsalex/safe-tensor)
# safe-tensor
Dependently typed tensor algebra in Haskell. Useful for applications in field theory, e.g., carrying out calculations for https://doi.org/10.1103/PhysRevD.101.084025

## Rationale
Tensor calculus is reflected in the type system. Let us view a tensor as a multilinear map from a product of vector spaces and duals thereof to the common field. The type of each tensor is its *generalized rank*, describing the vector spaces it acts on and assigning a label to each vector space. There are a few rules for tensor operations:

- Only tensors of the same type may be added. The result is a tensor of this type.
- Tensors may be multiplied if the resulting generalized rank does not contain repeated labels for the same (dual) vector space.
- The contraction of a tensors removes pairs of vector space and dual vector space with the same label from the generalized rank.

It is thus impossible to perform inconsistent tensor operations.

There is also an existentially typed variant of the tensor type useful for runtime computations. These computations take place in the Error monad, throwing errors if operand types are not consistent.
