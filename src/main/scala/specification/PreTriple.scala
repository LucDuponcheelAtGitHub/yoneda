package specification

import notation.{I}

trait PreTriple[C[-_, +_]: Category, PT[+_]: [_[+_]] =>> EndoFunctor[C, PT]]:

  val nu: EndoNaturalTransformation[C, I, PT]

  def pt[Z, Y]: C[Z, Y] => C[PT[Z], PT[Y]] = summon[EndoFunctor[C, PT]].f

  def ν[Z]: C[I[Z], PT[Z]] = nu.τ

import notation.{Law}

class PreTripleLaw[C[-_, +_]: Category, PT[+_]: [_[+_]] =>> PreTriple[C, PT]]:

  def commutativityLaw[Z, Y]: C[Z, Y] => Law[C[I[Z], PT[Y]]] =
    `z-->y` =>
      val preTriple: PreTriple[C, PT] = summon[PreTriple[C, PT]]
      import preTriple.{pt, ν}
      import implementation.generic.{identityEndoFunctor}
      def i[Z, Y]: C[Z, Y] => C[I[Z], I[Y]] = identityEndoFunctor.f
      Law(ν[Y] o i[Z, Y](`z-->y`), pt[Z, Y](`z-->y`) o ν[Z])
      Law(ν o i(`z-->y`), pt(`z-->y`) o ν)
