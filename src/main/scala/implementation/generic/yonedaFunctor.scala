package implementation.generic

import notation.{Yoneda}

import specification.{Category, Functor}

import implementation.specific.{functionCategory}

given yonedaFunctor[C[-_, +_]: Category, Z]: Functor[C, Function, Yoneda[C][Z]] with

  type YF = [Z] =>> [Y] =>> Yoneda[C][Z][Y]

  def f[Y, X]: C[Y, X] => Function[YF[Z][Y], YF[Z][X]] =
    `y-->x` => `z-->y` => `y-->x` o `z-->y`

import notation.{Proof}

class YonedaFunctorProofs[Z, C[-_, +_]: Category]:

  type YF = [Z] =>> [Y] =>> Yoneda[C][Z][Y]

  def yf[Y, X]: C[Y, X] => (YF[Z][Y] => YF[Z][X]) = yonedaFunctor.f

  def compositionProof[Y, X, W]: (C[Y, X], C[X, W]) => YF[Z][Y] => Proof[YF[Z][W]] =
    (`y-->x`, `x-->w`) =>
      `z-->y` =>
        Proof(
          yf(`x-->w` o `y-->x`)(`z-->y`),
          // definition yf
          (`x-->w` o `y-->x`) o `z-->y`,
          // associativityLaw for C
          `x-->w` o (`y-->x` o `z-->y`),
          // definition yf
          (`x-->w` o yf(`y-->x`)(`z-->y`)),
          // definition yf
          yf(`x-->w`)(yf(`y-->x`)(`z-->y`)),
          // definition o for functionCategory
          (yf(`x-->w`) o yf(`y-->x`))(`z-->y`)
          // done
        )

  def identityProof[Y]: C[Z, Y] => Proof[YF[Z][Y]] =
    `z-->y` =>
      def `y-->y`: C[Y, Y] = summon[Category[C]].identity
      Proof(
        yf(`y-->y`)(`z-->y`),
        // definition yf
        `y-->y` o `z-->y`,
        // leftIdentityLaw for C
        `z-->y`
        // done
      )
