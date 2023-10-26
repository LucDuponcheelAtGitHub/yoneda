package proposition

import notation.{Yoneda, Law}

import specification.{Category, Functor, NaturalTransformation}

import implementation.specific.{functionCategory}

import implementation.generic.{yonedaFunctor}

class YonedaLemma[C[-_, +_]: Category, Z, G[+_]: [_[+_]] =>> Functor[C, Function, G]]:

  val category = summon[Category[C]]

  import category.{identity}

  def g[Z, Y]: C[Z, Y] => Function[G[Z], G[Y]] = summon[Functor[C, Function, G]].f

  type YFZ = [Y] =>> Yoneda[C][Z][Y]

  def yonedaLemma1[Y]: (NaturalTransformation[C, Function, YFZ, G] => Law[Function[YFZ[Y], G[Y]]]) =
    yfz2g =>
      def `z-->z`[Z]: C[Z, Z] = identity[Z]
      def τ[Y]: Function[YFZ[Y], G[Y]] = yfz2g.τ
      def `g[z]` : G[Z] = τ(`z-->z`)
      val yfz_2_g: NaturalTransformation[C, Function, YFZ, G] =
        new:
          def τ[Y]: Function[YFZ[Y], G[Y]] = `z-->y` => g(`z-->y`)(`g[z]`)
      def σ[Y]: Function[YFZ[Y], G[Y]] = yfz_2_g.τ
      Law(τ, σ)

  def yonedaLemma2[Y, X]: G[Z] => (C[Y, X] => (Law[Function[YFZ[Y], G[X]]])) =
    `g[z]` =>
      val yfz2g: NaturalTransformation[C, Function, YFZ, G] =
        new:
          def τ[Y]: Function[YFZ[Y], G[Y]] = `z-->y` => g(`z-->y`)(`g[z]`)
      def σ[Y]: Function[YFZ[Y], G[Y]] = yfz2g.τ
      def yfz: C[Y, X] => Function[YFZ[Y], YFZ[X]] = yonedaFunctor.f
      `y-->x` => Law(g(`y-->x`) o σ, σ o yfz(`y-->x`))

import notation.{I}

import specification.{EndoFunctor}

import implementation.generic.{identityEndoFunctor}

class YonedaLemmaForIdentity[Z]extends YonedaLemma[Function, Z, I]

import notation.{Proof}

class YonedaLemmaProof[Z, C[-_, +_]: Category, G[+_]: [_[+_]] =>> Functor[C, Function, G]]:

  val category = summon[Category[C]]

  import category.{identity}

  def g[Z, Y]: C[Z, Y] => Function[G[Z], G[Y]] = summon[Functor[C, Function, G]].f

  type YFZ = [Y] =>> Yoneda[C][Z][Y]

  def yfz[Y, X]: C[Y, X] => Function[YFZ[Y], YFZ[X]] = yonedaFunctor.f

  def yonedaLemma1Proof[Y]: NaturalTransformation[C, Function, YFZ, G] => (YFZ[Y] => Proof[G[Y]]) =
    yfz2g =>
      def `z-->z`[Z]: C[Z, Z] = identity[Z]
      def τ[Y]: Function[YFZ[Y], G[Y]] = yfz2g.τ
      def `g[z]` : G[Z] = τ(`z-->z`)
      val yfz_2_g: NaturalTransformation[C, Function, YFZ, G] =
        new:
          def τ[Y]: Function[YFZ[Y], G[Y]] = `z-->y` => g(`z-->y`)(`g[z]`)
      def σ[Y]: Function[YFZ[Y], G[Y]] = yfz_2_g.τ
      `z-->y` =>
        List(
          τ(`z-->y`),
          // rightIdentityLaw for C
          τ(`z-->y` o `z-->z`),
          // definition yfz
          τ(yfz(`z-->y`)(`z-->z`)),
          // definition o for functionCategory
          (τ o yfz(`z-->y`))(`z-->z`),
          // commutativityLaw for τ
          (g(`z-->y`) o τ)(`z-->z`),
          // definition o for functionCategory
          g(`z-->y`)(τ(`z-->z`)),
          // definition `g[z]`
          g(`z-->y`)(`g[z]`),
          // definition σ
          σ(`z-->y`)
          // done
        )

  def yonedaLemma2Proof[Y, X]: G[Z] => (C[Y, X] => (YFZ[Y] => Proof[G[X]])) =
    `g[z]` =>
      `y-->x` =>
        val yfz2g: NaturalTransformation[C, Function, YFZ, G] =
          new:
            def τ[Y]: Function[YFZ[Y], G[Y]] = `z-->y` => g(`z-->y`)(`g[z]`)
        def σ[Y]: Function[YFZ[Y], G[Y]] = yfz2g.τ
        `z-->y` =>
          Proof(
            (g(`y-->x`) o σ)(`z-->y`),
            // definition o for functionCategory
            g(`y-->x`)(σ(`z-->y`)),
            // definition σ
            g(`y-->x`)(g(`z-->y`)(`g[z]`)),
            // definition o for functionCategory
            (g(`y-->x`) o g(`z-->y`))(`g[z]`),
            // compositionLaw for g
            (g(`y-->x` o `z-->y`))(`g[z]`),
            // definition yfz
            (g(yfz(`y-->x`)(`z-->y`)))(`g[z]`),
            // definition σ with yfz(`y-->x`)(`z-->y`)
            σ(yfz(`y-->x`)(`z-->y`)),
            // definition o for functionCategory
            (σ o yfz(`y-->x`))(`z-->y`)
            // done
          )
