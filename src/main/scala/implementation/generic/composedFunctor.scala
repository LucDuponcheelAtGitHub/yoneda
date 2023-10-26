package implementation.generic

import notation.{O}

import specification.{Category, Functor}

given composedFunctor[
    C[-_, +_]: Category,
    D[-_, +_]: Category,
    E[-_, +_]: Category,
    F[+_]: [_[+_]] =>> Functor[C, D, F],
    G[+_]: [_[+_]] =>> Functor[D, E, G]
]: Functor[C, E, G O F] with

  def f[Z, Y]: C[Z, Y] => E[(G O F)[Z], (G O F)[Y]] =
    def f: C[Z, Y] => D[F[Z], F[Y]] = summon[Functor[C, D, F]].f
    def g: D[F[Z], F[Y]] => E[(G O F)[Z], (G O F)[Y]] = summon[Functor[D, E, G]].f
    `z-->y` => g(f(`z-->y`))

import notation.{Proof}

class ComposedFunctorProofs[
    C[-_, +_]: Category,
    D[-_, +_]: Category,
    E[-_, +_]: Category,
    F[+_]: [_[+_]] =>> Functor[C, D, F],
    G[+_]: [_[+_]] =>> Functor[D, E, G]
]:

  def f[Z, Y]: C[Z, Y] => D[F[Z], F[Y]] = summon[Functor[C, D, F]].f

  def g[Z, Y]: D[F[Z], F[Y]] => E[(G O F)[Z], (G O F)[Y]] = summon[Functor[D, E, G]].f

  def gof[Z, Y]: C[Z, Y] => E[(G O F)[Z], (G O F)[Y]]= composedFunctor[C, D, E, F, G].f

  def identityProof[Z]: Proof[E[(G O F)[Z], (G O F)[Z]]] =
    val `z-c->z`: C[Z, Z] = summon[Category[C]].identity[Z]
    val `f[z]-d->f[z]` : D[F[Z], F[Z]] = summon[Category[D]].identity[F[Z]]
    val `(gof)[z]-e->(gof)[z]` : E[(G O F)[Z], (G O F)[Z]] = summon[Category[E]].identity[(G O F)[Z]]
    Proof(
      gof(`z-c->z`),
      // definition f for gof
      g(f(`z-c->z`)),
      // identityLaw for f
      g(`f[z]-d->f[z]`),
      // identityLaw for g
      `(gof)[z]-e->(gof)[z]`
      // done
    )

  def compositionProof[Z, Y, X]: C[Z, Y] => (C[Y, X] => Proof[E[(G O F)[Z], (G O F)[X]]]) =
    `z-->y` =>
      `y-->x` =>
        extension [Z, Y, X](`y-->x`: C[Y, X])
          def o_c(`z-->y`: C[Z, Y]): C[Z, X] =
            summon[Category[C]].o[Z, Y, X](`y-->x`)(`z-->y`)
        extension [Z, Y, X](`y-->x`: D[Y, X])
          def o_d(`z-->y`: D[Z, Y]): D[Z, X] =
            summon[Category[D]].o[Z, Y, X](`y-->x`)(`z-->y`)
        extension [Z, Y, X](`y-->x`: E[Y, X])
          def o_e(`z-->y`: E[Z, Y]): E[Z, X] =
            summon[Category[E]].o[Z, Y, X](`y-->x`)(`z-->y`)
        Proof(
          gof(`y-->x` o_c `z-->y`),
          // definition f for gof
          g(f(`y-->x` o_c `z-->y`)),
          // compositionLaw for f
          g(f(`y-->x`) o_d f(`z-->y`)),
          // compositionLaw for g
          g(f(`y-->x`)) o_e g(f(`z-->y`)),
          // definition f for gof
          gof(`y-->x`) o_e gof(`z-->y`)
          // done
        )
