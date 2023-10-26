package specification

trait NaturalTransformation[
    C[-_, +_]: Category,
    D[-_, +_]: Category,
    F[+_]: [_[+_]] =>> Functor[C, D, F],
    G[+_]: [_[+_]] =>> Functor[C, D, G]
]:

  def τ[Z]: D[F[Z], G[Z]]

type EndoNaturalTransformation[C[-_, +_], F[+_], G[+_]] = NaturalTransformation[C, C, F, G]

import notation.{Law}

class NaturalTransformationLaw[
    C[-_, +_]: Category,
    D[-_, +_]: Category,
    F[+_]: [_[+_]] =>> Functor[C, D, F],
    G[+_]: [_[+_]] =>> Functor[C, D, G],
    T[_[-_, +_], _[-_, +_], _[+_], _[+_]]: [_[_[-_, +_], _[-_, +_], _[+_], _[+_]]] =>> NaturalTransformation[
      C,
      D,
      F,
      G
    ]
]:

  // def commutativityLaw[Z, Y]: C[Z, Y] => Law[D[F[Z], G[Y]]] =
  //   `z-->y` =>
  //     def f[Z, Y]: C[Z, Y] => D[F[Z], F[Y]] = summon[Functor[C, D, F]].f
  //     def g[Z, Y]: C[Z, Y] => D[G[Z], G[Y]] = summon[Functor[C, D, G]].f
  //     extension [Z, Y, X](`y-->x`: D[Y, X])
  //       def o_d(`z-->y`: D[Z, Y]): D[Z, X] = summon[Category[D]].o(`y-->x`)(`z-->y`)
  //     def τ[Z]: D[F[Z], G[Z]] = summon[NaturalTransformation[C, D, F, G]].τ
  //     (τ[Y] o_d f[Z, Y](`z-->y`), g[Z, Y](`z-->y`) o_d τ[Z])

  def commutativityLaw[Z, Y]: C[Z, Y] => Law[D[F[Z], G[Y]]] =
    `z-->y` =>
      def f[Z, Y]: C[Z, Y] => D[F[Z], F[Y]] = summon[Functor[C, D, F]].f
      def g[Z, Y]: C[Z, Y] => D[G[Z], G[Y]] = summon[Functor[C, D, G]].f
      def τ[Z]: D[F[Z], G[Z]] = summon[NaturalTransformation[C, D, F, G]].τ
      Law(τ o f(`z-->y`), g(`z-->y`) o τ)
