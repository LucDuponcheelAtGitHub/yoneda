package implementation.generic

import specification.{Category, EndoFunctor, EndoNaturalTransformation}

def composedNaturalTransformation[
    C[-_, +_]: Category,
    F[+_]: [_[+_]] =>> EndoFunctor[C, F],
    G[+_]: [_[+_]] =>> EndoFunctor[C, G],
    H[+_]: [_[+_]] =>> EndoFunctor[C, H],
    S[_[-_, +_], _[-_, +_], _[+_], _[+_]]: [_[
        _[-_, +_],
        _[-_, +_],
        _[+_],
        _[+_]
    ]] =>> EndoNaturalTransformation[
      C,
      F,
      G
    ],
    T[_[-_, +_], _[-_, +_], _[+_], _[+_]]: [_[
        _[-_, +_],
        _[-_, +_],
        _[+_],
        _[+_]
    ]] =>> EndoNaturalTransformation[
      C,
      G,
      H
    ]
]: EndoNaturalTransformation[C, F, H] =

  def σ[Z]: C[F[Z], G[Z]] = summon[EndoNaturalTransformation[C, F, G]].τ

  def τ[Z]: C[G[Z], H[Z]] = summon[EndoNaturalTransformation[C, G, H]].τ

  def υ[Z]: C[F[Z], H[Z]] = τ o σ

  new:
    def τ[Z]: C[F[Z], H[Z]] = υ

import notation.{Proof}

class ComposedEndoNaturalTransformationProof[
    C[-_, +_]: Category,
    F[+_]: [_[+_]] =>> EndoFunctor[C, F],
    G[+_]: [_[+_]] =>> EndoFunctor[C, G],
    H[+_]: [_[+_]] =>> EndoFunctor[C, H],
    S[_[-_, +_], _[-_, +_], _[+_], _[+_]]: [_[
        _[-_, +_],
        _[-_, +_],
        _[+_],
        _[+_]
    ]] =>> EndoNaturalTransformation[
      C,
      F,
      G
    ],
    T[_[-_, +_], _[-_, +_], _[+_], _[+_]]: [_[
        _[-_, +_],
        _[-_, +_],
        _[+_],
        _[+_]
    ]] =>> EndoNaturalTransformation[
      C,
      G,
      H
    ]
]:

  def commutativityProof[Z, Y]: C[Z, Y] => Proof[C[F[Z], H[Y]]] =
    def σ[Z]: C[F[Z], G[Z]] = summon[EndoNaturalTransformation[C, F, G]].τ
    def τ[Z]: C[G[Z], H[Z]] = summon[EndoNaturalTransformation[C, G, H]].τ
    def τoσ[Z]: C[F[Z], H[Z]] = composedNaturalTransformation[C, F, G, H, S, T].τ
    def f[Z, Y]: C[Z, Y] => C[F[Z], F[Y]] = summon[EndoFunctor[C, F]].f
    def g[Z, Y]: C[Z, Y] => C[G[Z], G[Y]] = summon[EndoFunctor[C, G]].f
    def h[Z, Y]: C[Z, Y] => C[H[Z], H[Y]] = summon[EndoFunctor[C, H]].f
    `z-->y` =>
      Proof(
        τoσ o f(`z-->y`),
        // definition τ for composedNaturalTransformation
        (τ o σ) o f(`z-->y`),
        // associativityLaw for C
        τ o (σ o f(`z-->y`)),
        // commutativityLaw for S
        τ o (g(`z-->y`) o σ),
        // categoryCompositionAssociativityLaw for C
        (τ o g(`z-->y`)) o σ,
        // commutativityLaw for T
        (h(`z-->y`) o τ) o σ,
        // associativityLaw for C
        h(`z-->y`) o (τ o σ),
        // definition τ for composedNaturalTransformation
        h(`z-->y`) o τoσ
        // done
      )
