# Changelog

## [0.2.1.0] - 2020-07-20
 * removeZeros is optional: Tensor addition and tensor contraction will not remove zero values afterwards in order to improve performance.
   Zero values have to be removed by explicitly applying removeZeros to a tensor.
 * all data types are now instances of NFData
 * added functionality to read solution from an rref matrix in a reversed manner

## [0.2.0.0] - 2020-07-08
 * Minor API adjustments
 * major documentation improvements
 * backwards compatibility with GHC 8.6.5

## [0.1.0.0] - 2020-07-07
Initial release.
