package implementation.generic

import notation.{O}

import specification.{Category, Functor, NaturalTransformation}

def leftFunctorComposedNaturalTransformation[
    C[-_, +_]: Category,
    D[-_, +_]: Category,
    E[-_, +_]: Category,
    H[+_]: [_[+_]] =>> Functor[D, E, H],
    F[+_]: [_[+_]] =>> Functor[C, D, F],
    G[+_]: [_[+_]] =>> Functor[C, D, G]
](sigma: NaturalTransformation[C, D, F, G]): NaturalTransformation[C, E, H O F, H O G] =

  given `hof`: Functor[C, E, H O F] = composedFunctor[C, D, E, F, H]

  given `hog`: Functor[C, E, H O G] = composedFunctor[C, D, E, G, H]

  def σ[Z]: D[F[Z], G[Z]] = sigma.τ

  def h[Z, Y]: D[Z, Y] => E[H[Z], H[Y]] = summon[Functor[D, E, H]].f

  def hσ[Z]: E[(H O F)[Z], (H O G)[Z]] = h(σ[Z])

  new:
    def τ[Z]: E[(H O F)[Z], (H O G)[Z]] = hσ

import notation.{Proof}

import implementation.specific.{functionCategory}

class LeftFunctorComposedNaturalTransformationProof[
    C[-_, +_]: Category,
    D[-_, +_]: Category,
    E[-_, +_]: Category,
    H[+_]: [_[+_]] =>> Functor[D, E, H],
    F[+_]: [_[+_]] =>> Functor[C, D, F],
    G[+_]: [_[+_]] =>> Functor[C, D, G]
]:

  def commutativityProof[Z, Y](
      sigma: NaturalTransformation[C, D, F, G]
  ): C[Z, Y] => Proof[E[(H O F)[Z], (H O G)[Y]]] =
    `z-->y` =>
      def σ[Z]: D[F[Z], G[Z]] = sigma.τ
      def h[Z, Y]: D[Z, Y] => E[H[Z], H[Y]] = summon[Functor[D, E, H]].f
      def hσ[Z, Y]: E[(H O F)[Z], (H O G)[Z]] =
        leftFunctorComposedNaturalTransformation[C, D, E, H, F, G](sigma).τ
      def f[Z, Y]: C[Z, Y] => D[F[Z], F[Y]] = summon[Functor[C, D, F]].f
      def g[Z, Y]: C[Z, Y] => D[G[Z], G[Y]] = summon[Functor[C, D, G]].f
      import implementation.specific.{functionCategory}
      Proof(
        hσ o (h o f)(`z-->y`),
        // definition τ for leftFunctorComposedNaturalTransformation
        h(σ) o (h o f)(`z-->y`),
        // definition o for functionCategory
        h(σ) o h(f(`z-->y`)),
        // compositionLaw for h
        h(σ o f(`z-->y`)),
        // commutativityLaw for S
        h(g(`z-->y`) o σ),
        // compositionLaw for h
        h(g(`z-->y`)) o h(σ),
        // definition o for functionCategory
        (h o g)(`z-->y`) o h(σ),
        // definition τ for leftFunctorComposedNaturalTransformation
        (h o g)(`z-->y`) o hσ
        // done
      )
