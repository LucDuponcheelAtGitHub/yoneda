package implementation.generic

import notation.{I}

import specification.{Category, EndoNaturalTransformation}

def identityEndoNaturalTransformation[C[-_, +_]: Category]: EndoNaturalTransformation[C, I, I] =
  new:
    def τ[Z]: C[I[Z], I[Z]] =
      summon[Category[C]].identity

import notation.{Proof}

class IdentityNaturalTransformationProof[C[-_, +_]: Category]:

  val category = summon[Category[C]]
  import category.{identity}

  def i[Z, Y]: C[Z, Y] => C[I[Z], I[Y]] = identityEndoFunctor.f
  def ι[Z]: C[I[Z], I[Z]] = identityEndoNaturalTransformation.τ

  def commutativityProof[Z, Y]: C[Z, Y] => Proof[C[I[Z], I[Y]]] =
    `z-->y` =>
      Proof(
        ι o i(`z-->y`),
        // definition i
        ι o i(`z-->y`),
        // definition ι
        identity o `z-->y`,
        // left identity law
        `z-->y`,
        // right identity law
        `z-->y` o identity,
        // definition ι
        `z-->y` o ι,
        // definition i
        i(`z-->y`) o ι
      )
