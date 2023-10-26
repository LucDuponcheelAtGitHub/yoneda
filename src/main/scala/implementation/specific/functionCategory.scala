package implementation.specific

import specification.{Category}

given functionCategory: Category[Function] with

  def identity[Z]: Function[Z, Z] = z => z

  def composition[Z, Y, X]: (Function[Y, X], Function[Z, Y]) => Function[Z, X] =
    (`y=>x`, `z=>y`) => z => `y=>x`(`z=>y`(z))

import notation.{Proof}

class FunctionCategoryProofs:

  def associativityProof[Z, Y, X, W]: ((Function[Z, Y], Function[Y, X], Function[X, W]) => Z => Proof[W]) =
    (`z=>y`, `y=>x`, `x=>w`) =>
      z =>
        Proof(
          ((`x=>w` o `y=>x`) o `z=>y`)(z),
          // definition o for functionCategory
          (`x=>w` o `y=>x`)(`z=>y`(z)),
          // definition o for functionCategory
          `x=>w`(`y=>x`(`z=>y`(z))),
          // definition o for functionCategory
          `x=>w`((`y=>x` o `z=>y`)(z)),
          // definition o for functionCategory
          (`x=>w` o (`y=>x` o `z=>y`))(z)
          // done
        )

  def leftIdentityProof[Z, Y]: Function[Z, Y] => Z => List[Y] =
    `z=>y` =>
      z =>
        def `y-->y`[Y] = functionCategory.identity[Y]
        List(
          (`y-->y` o `z=>y`)(z),
          // definition o for functionCategory
          `y-->y`(`z=>y`(z)),
          // definition `y-->y` for functionCategory
          (`z=>y`)(z)
          // done
        )

  def rightIdentityProof[Z, Y]: Function[Z, Y] => Z => List[Y] =
    `z=>y` =>
      z =>
        def `z-->z`[Z] = functionCategory.identity[Z]
        List(
          (`z=>y` o `z-->z`)(z),
          // definition o for functionCategory
          `z=>y`(`z-->z`(z)),
          // definition `z-->z` for functionCategory
          (`z=>y`)(z)
          // done
        )
