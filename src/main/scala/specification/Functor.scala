package specification

trait Functor[C[-_, +_]: Category, D[-_, +_]: Category, F[+_]]:
  def f[Z, Y]: C[Z, Y] => D[F[Z], F[Y]]

type EndoFunctor[C[-_, +_], F[+_]] = Functor[C, C, F]

import notation.{Law}

class FunctorLaws[C[-_, +_]: Category, D[-_, +_]: Category, F[+_]: [_[+_]] =>> Functor[C, D, F]]:

  // def identityLaw[Z]: Law[D[F[Z], F[Z]]] =
  //   def `z-c->z`[Z]: C[Z, Z] = summon[Category[C]].identity
  //   def `f[z]-d->f[z]`[F[Z]]: D[F[Z], F[Z]] = summon[Category[D]].identity
  //   def f[Z, Y]: C[Z, Y] => D[F[Z], F[Y]] = summon[Functor[C, D, F]].f
  //   Law(f[Z, Z](`z-c->z`), `f[z]-d->f[z]`)

  // def compositionLaw[Z, Y, X]: (C[Z, Y], C[Y, X]) => Law[D[F[Z], F[X]]] =
  //   (`z-->y`, `y-->x`) =>
  //     extension [Z, Y, X](`y-->x`: C[Y, X])
  //       def o_c(`z-->y`: C[Z, Y]): C[Z, X] = summon[Category[C]].o[Z, Y, X](`y-->x`)(`z-->y`)
  //     extension [Z, Y, X](`y-->x`: D[Y, X])
  //       def o_d(`z-->y`: D[Z, Y]): D[Z, X] = summon[Category[D]].o[Z, Y, X](`y-->x`)(`z-->y`)
  //     def f[Z, Y]: C[Z, Y] => D[F[Z], F[Y]] = summon[Functor[C, D, F]].f
  //     Law(f[Z, X](`y-->x` o_c `z-->y`), f[Y, X](`y-->x`) o_d f[Z, Y](`z-->y`))

  def identityLaw[Z]: Law[D[F[Z], F[Z]]] =
    def identity_C[Z]: C[Z, Z] = summon[Category[C]].identity
    def identity_D[Z]: D[Z, Z] = summon[Category[D]].identity
    def f[Z, Y]: C[Z, Y] => D[F[Z], F[Y]] = summon[Functor[C, D, F]].f
    Law(f(identity_C), identity_D)

  def compositionLaw[Z, Y, X]: (C[Z, Y], C[Y, X]) => Law[D[F[Z], F[X]]] =
    (`z-->y`, `y-->x`) =>
      def f[Z, Y]: C[Z, Y] => D[F[Z], F[Y]] = summon[Functor[C, D, F]].f
      Law(f(`y-->x` o `z-->y`), f(`y-->x`) o f(`z-->y`))

