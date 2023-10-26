package implementation.generic

import notation.{I}

import specification.{Category, EndoFunctor}

given identityEndoFunctor[C[-_, +_]: Category]: EndoFunctor[C, I] with
  def f[Z, Y]: C[Z, Y] => C[I[Z], I[Y]] = `z-->y` => `z-->y`

import notation.{Proof}

class IdentityEndoFunctorProofs[C[-_, +_]: Category]:

  def i[Z, Y]: C[Z, Y] => C[Z, Y] = identityEndoFunctor.f

  def identityProof[Z]: Proof[C[I[Z], I[Z]]] =

    def `z-->z`: C[Z, Z] = summon[Category[C]].identity
    def `i[z]-->i[z]` : C[I[Z], I[Z]] = summon[Category[C]].identity

    List(
      i(`z-->z`),
      // definition i
      `z-->z`,
      // definition `i[z]-->i[z]`
      `i[z]-->i[z]`
      // done
    )

  def compositionProof[Z, Y, X]: C[Z, Y] => C[Y, X] => Proof[C[I[Z], I[X]]] =
    `z-->y` =>
      `y-->x` =>
        Proof(
          i(`y-->x` o `z-->y`),
          // definition i
          `y-->x` o `z-->y`,
          // definition i (twice)
          i(`y-->x`) o i(`z-->y`)
          // done
        )
