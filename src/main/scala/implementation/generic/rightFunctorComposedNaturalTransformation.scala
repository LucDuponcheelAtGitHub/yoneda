package implementation.generic

import notation.{O}

import specification.{Category, Functor, NaturalTransformation}

def rightFunctorComposedNaturalTransformation[
    C[-_, +_]: Category,
    D[-_, +_]: Category,
    E[-_, +_]: Category,
    F[+_]: [_[+_]] =>> Functor[C, D, F],
    H[+_]: [_[+_]] =>> Functor[D, E, H],
    K[+_]: [_[+_]] =>> Functor[D, E, K]
](sigma: NaturalTransformation[D, E, H, K]): NaturalTransformation[C, E, H O F, K O F] =

  given `hof`: Functor[C, E, H O F] = composedFunctor[C, D, E, F, H]

  given `kof`: Functor[C, E, K O F] = composedFunctor[C, D, E, F, K]

  def σ[Z]: E[H[Z], K[Z]] = sigma.τ

  def σf[Z]: E[(H O F)[Z], (K O F)[Z]] = σ[F[Z]]

  new:
    def τ[Z]: E[(H O F)[Z], (K O F)[Z]] = σf

import notation.{Proof}

class RightFunctorComposedNaturalTransformationProof[
    C[-_, +_]: Category,
    D[-_, +_]: Category,
    E[-_, +_]: Category,
    F[+_]: [_[+_]] =>> Functor[C, D, F],
    H[+_]: [_[+_]] =>> Functor[D, E, H],
    K[+_]: [_[+_]] =>> Functor[D, E, K]
]:

  def commutativityProof[Z, Y](
      sigma: NaturalTransformation[D, E, H, K]
  ): C[Z, Y] => Proof[E[(H O F)[Z], (K O F)[Y]]] =
    `z-->y` =>
      def σ[Z]: E[H[Z], K[Z]] = sigma.τ
      def σf[Z]: E[(H O F)[Z], (K O F)[Z]] =
        rightFunctorComposedNaturalTransformation[C, D, E, F, H, K](sigma).τ
      def f[Z, Y]: C[Z, Y] => D[F[Z], F[Y]] = summon[Functor[C, D, F]].f
      def h[Z, Y]: D[Z, Y] => E[H[Z], H[Y]] = summon[Functor[D, E, H]].f
      def k[Z, Y]: D[Z, Y] => E[K[Z], K[Y]] = summon[Functor[D, E, K]].f
      import implementation.specific.{functionCategory}
      Proof(
        σf o (h o f)(`z-->y`),
        // definition τ for rightFunctorComposedNaturalTransformation
        σ[F[Y]] o (h o f)(`z-->y`),
        // definition o for functionCategory
        σ[F[Y]] o h(f(`z-->y`)),
        // commutativityLaw for S (with f(`z-->y`))
        k(f(`z-->y`)) o σ[F[Z]],
        // definition o for functionCategory
        (k o f)(`z-->y`) o σ[F[Z]],
        // definition τ for rightFunctorComposedNaturalTransformation
        (k o f)(`z-->y`) o σf
        // done
      )
