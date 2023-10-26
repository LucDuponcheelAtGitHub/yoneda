package specification

import notation.{I, O, U, Yoneda}

import implementation.generic.{identityEndoFunctor, yonedaFunctor, yonedaEndoFunctor}

trait PreFunctional[C[-_, +_]] extends Functor[Function, C, I] with PreTriple[C, Yoneda[C][U]]

trait PreFunctionalCategory[C[-_, +_]] extends Category[C] with PreFunctional[C]:

  def f2m[Z, Y]: Function[Z, Y] => C[Z, Y] = f

  given PreFunctionalCategory[C] = this

  type GF = [Z] =>> C[U, Z]

  def gf[Z, Y]: C[Z, Y] => C[GF[Z], GF[Y]] =
    yonedaEndoFunctor[C, U].f

  def v2gv[Z]: Function[Z, GF[Z]] = z => f2m(u => z)
  val nu: EndoNaturalTransformation[C, I, GF] =
    new:
      def τ[Z]: C[I[Z], GF[Z]] = f2m(v2gv)

  type YF = [Z] =>> [Y] =>> Yoneda[C][Z][Y]

  def yfz[Z, Y, X]: C[Y, X] => Function[YF[Z][Y], YF[Z][X]] =
    yonedaFunctor[C, Z].f

  type YEF = [Z] =>> [Y] =>> Yoneda[C][Z][Y]

  def yefz[Z, Y, X]: C[Y, X] => C[YEF[Z][Y], YEF[Z][X]] =
    yonedaEndoFunctor[C, Z].f

import notation.{Law}

class PreFunctionalCategoryLaws[C[-_, +_]: PreFunctionalCategory]:

  val preFunctionalCategory = summon[PreFunctionalCategory[C]]
  import preFunctionalCategory.{GF}

  def commutativityLaw[Z, Y]: C[Z, Y] => Law[C[I[Z], GF[Y]]] =
    `z-->y` =>
      import preFunctionalCategory.{gf, ν}
      def i[Z, Y]: C[Z, Y] => C[Z, Y] = identityEndoFunctor[C].f
      (ν o i(`z-->y`), gf(`z-->y`) o ν)

  import preFunctionalCategory.{f2m}
  import implementation.specific.{functionCategory}

  def compositionLaw[Z, Y, X]: Function[Z, Y] => (Function[Y, X] => Law[C[Z, X]]) =
    `z=>y` => `y=>x` => (f2m(`y=>x` o `z=>y`), f2m(`y=>x`) o f2m(`z=>y`))

  def identityLaw[Z]: Law[C[Z, Z]] =
    def `z-->z`[Z]: C[Z, Z] = preFunctionalCategory.identity
    def `z=>z`[Z]: Function[Z, Z] = functionCategory.identity
    (f2m(`z=>z`), `z-->z`)

  def nuLaw[Z]: GF[Z] => Law[(GF O GF)[Z]] =
    `u-->z` =>
      import preFunctionalCategory.{v2gv, ν}
      (ν[Z] o `u-->z`, v2gv[C[U, Z]](`u-->z`))
      (ν o `u-->z`, v2gv(`u-->z`))
