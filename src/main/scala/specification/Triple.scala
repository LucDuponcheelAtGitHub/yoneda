package specification

import notation.{O}

trait Triple[C[-_, +_]: Category, T[+_]: [_[+_]] =>> EndoFunctor[C, T]] extends PreTriple[C, T]:

  val mu: EndoNaturalTransformation[C, T O T, T]

  val tef: EndoFunctor[C, T] = summon[EndoFunctor[C, T]]

  def t[Z, Y]: C[Z, Y] => C[T[Z], T[Y]] = summon[EndoFunctor[C, T]].f

  def μ[Z]: C[(T O T)[Z], T[Z]] = mu.τ

import notation.{Law}

class TripleLaws[C[-_, +_]: Category, T[+_]: [_[+_]] =>> Triple[C, T]]:

  val category: Category[C] = summon[Category[C]]

  val triple: Triple[C, T] = summon[Triple[C, T]]

  def commutativityLaw[Z, Y]: C[Z, Y] => Law[C[(T O T)[Z], T[Y]]] =
    `z-->y` =>
      import triple.{t, μ}
      import implementation.specific.{functionCategory}
      Law(μ[Y] o (t[T[Z], T[Y]] o t[Z, Y])(`z-->y`), t[Z, Y](`z-->y`) o μ[Z])
      Law(μ o (t o t)(`z-->y`), t(`z-->y`) o (μ))

  def leftIdentityLaw[Z]: Law[C[T[Z], T[Z]]] =
    import implementation.generic.{identityEndoNaturalTransformation}
    def ι[Z]: C[Z, Z] = identityEndoNaturalTransformation.τ
    import triple.{ν, μ}
    Law(μ[Z] o ν[T[Z]], ι[T[Z]])
    Law(μ o ν, ι)
    import notation.{I}
    import triple.{nu}
    given EndoFunctor[C, T] = triple.tef
    import implementation.generic.{identityEndoFunctor, rightFunctorComposedNaturalTransformation}
    def νt[Z]: C[T[Z], (T O T)[Z]] = rightFunctorComposedNaturalTransformation(nu).τ
    Law(μ o νt, ι)

  def rightIdentityLaw[Z]: Law[C[T[Z], T[Z]]] =
    import implementation.generic.{identityEndoNaturalTransformation}
    def ι[Z]: C[Z, Z] = identityEndoNaturalTransformation.τ
    import triple.{t, ν, μ}
    Law(μ[Z] o t[Z, T[Z]](ν[Z]), ι[T[Z]])
    Law(μ o t(ν), ι)
    import notation.{I}
    import triple.{nu}
    given EndoFunctor[C, T] = triple.tef
    import implementation.generic.{identityEndoFunctor, leftFunctorComposedNaturalTransformation}
    def tν[Z]: C[T[Z], (T O T)[Z]] = leftFunctorComposedNaturalTransformation(nu).τ
    Law(μ o tν, ι)

  def associativityLaw[Z]: Law[C[(T O T O T)[Z], T[Z]]] =
    import triple.{t, μ}
    Law(μ[Z] o μ[T[Z]], μ[Z] o t[(T O T)[Z], T[Z]](μ[Z]))
    Law(μ o μ, μ o t(μ))
    import notation.{I}
    import triple.{mu}
    given EndoFunctor[C, T] = triple.tef
    import implementation.generic.{
      composedFunctor,
      leftFunctorComposedNaturalTransformation,
      rightFunctorComposedNaturalTransformation
    }
    def μt[Z]: C[(T O T O T)[Z], (T O T)[Z]] = rightFunctorComposedNaturalTransformation(mu).τ
    def tμ[Z]: C[(T O T O T)[Z], (T O T)[Z]] = leftFunctorComposedNaturalTransformation(mu).τ
    Law(μ o μt, μ o tμ)
