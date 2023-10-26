package proposition

import notation.{O, U, Law}

import specification.{FunctionalCategory, EndoFunctor, EndoNaturalTransformation}

import implementation.generic.{composedFunctor, yonedaEndoFunctor}

import implementation.specific.{functionCategory}

class EndoYonedaLemma[C[-_, +_]: FunctionalCategory, Z, G[+_]: [G[+_]] =>> EndoFunctor[C, G]]:

  val functionalCategory = summon[FunctionalCategory[C]]

  import functionalCategory.{GF}

  import notation.{Yoneda}

  type YEFZ = [Y] =>> Yoneda[C][Z][Y]

  def g[Z, Y]: C[Z, Y] => C[G[Z], G[Y]] = summon[EndoFunctor[C, G]].f

  def endoYonedaLemma1[Y]: EndoNaturalTransformation[C, YEFZ, GF O G] => Law[C[YEFZ[Y], (GF O G)[Y]]] =
    yefz2gfog =>
      import functionalCategory.{identity, v2gv, yefz, gf, μ}
      def `z-->z`: C[Z, Z] = identity
      def τ[Y]: C[YEFZ[Y], (GF O G)[Y]] = yefz2gfog.τ
      val `u-->(u-->g[z])` : (GF O GF O G)[Z] = τ o v2gv(`z-->z`)
      val yefz_2_gfog: EndoNaturalTransformation[C, YEFZ, GF O G] =
        new:
          def τ[Y]: C[YEFZ[Y], (GF O G)[Y]] =
            μ o functionalCategory.f2m(`z-->y` => (gf o g)(`z-->y`) o `u-->(u-->g[z])`)
      def σ[Y]: C[YEFZ[Y], (GF O G)[Y]] = yefz_2_gfog.τ
      Law(τ, σ)

  def endoYonedaLemma2[Y, X]: (GF O GF O G)[Z] => (C[Y, X] => Law[C[YEFZ[Y], (GF O G)[X]]]) =
    `u-->(u-->g[z])` =>
      `y-->x` =>
        import functionalCategory.{yefz, f2m, gf, μ}
        type YEFZ = [Y] =>> Yoneda[C][Z][Y]
        val yefz2gfog: EndoNaturalTransformation[C, YEFZ, GF O G] =
          new:
            def τ[Y]: C[YEFZ[Y], (GF O G)[Y]] =
              μ o f2m(`z-->y` => (gf o g)(`z-->y`) o `u-->(u-->g[z])`)
        def σ[Y]: C[YEFZ[Y], (GF O G)[Y]] = yefz2gfog.τ

        Law((gf o g)(`y-->x`) o σ, σ o yefz(`y-->x`))

  def endoCorollary1[Y]: EndoNaturalTransformation[C, YEFZ, G] => Law[C[YEFZ[Y], (GF O G)[Y]]] =
    yef2g =>
      import functionalCategory.{ν}
      type YEFZ = [Y] =>> Yoneda[C][Z][Y]
      def σ[Y]: C[YEFZ[Y], G[Y]] = yef2g.τ
      endoYonedaLemma1[Y](
        new:
          override def τ[Y]: C[YEFZ[Y], (GF O G)[Y]] =
            ν o σ
      )

import notation.{I}

import implementation.generic.identityEndoFunctor

class EndoYonedaLemmaForIdentity[C[-_, +_]: FunctionalCategory, Z] extends EndoYonedaLemma[C, Z, I]

import notation.{Proof}

class EndoYonedaProof[Z, C[-_, +_]: FunctionalCategory, G[+_]: [G[+_]] =>> EndoFunctor[C, G]]:

  val functionalCategory = summon[FunctionalCategory[C]]

  import functionalCategory.{GF}

  import notation.{Yoneda}

  type YEFZ = [Y] =>> Yoneda[C][Z][Y]

  def g[Z, Y]: C[Z, Y] => C[G[Z], G[Y]] = summon[EndoFunctor[C, G]].f

  def endoYonedaProof1[Y]: EndoNaturalTransformation[C, YEFZ, GF O G] => (C[Z, Y] => Proof[(GF O GF O G)[Y]]) =
    yefz2gfog =>
      import functionalCategory.{identity, f2m, v2gv, yefz, gf, ν, μ}
      val `z-->z` = identity[Z]
      def τ[Y]: C[YEFZ[Y], (GF O G)[Y]] = yefz2gfog.τ
      def `u-->(u-->g[z])` : (GF O GF O G)[Z] = τ o v2gv(`z-->z`)
      val yefz_2_gfog: EndoNaturalTransformation[C, YEFZ, GF O G] =
        new:
          def τ[Y]: C[YEFZ[Y], (GF O G)[Y]] =
            μ o f2m(`z-->y` => (gf o g)(`z-->y`) o `u-->(u-->g[z])`)
      def σ[Y]: C[YEFZ[Y], (GF O G)[Y]] = yefz_2_gfog.τ
      `z-->y` =>
        Proof(
          τ o v2gv(`z-->y`),
          // rightIdentityLaw for C
          τ o v2gv(`z-->y` o `z-->z`),
          // pointfreeYoneda
          τ o yefz(`z-->y`) o v2gv(`z-->z`),
          // commutativityLaw for τ
          (gf o g)(`z-->y`) o τ o v2gv(`z-->z`),
          // definition `u-->(u-->g[z])`
          (gf o g)(`z-->y`) o `u-->(u-->g[z])`,
          // muProposition with `u-->(u-->y)` = (gf o g)((`z-->y`)) o `u-->(u-->g[z])`
          μ o v2gv((gf o g)((`z-->y`)) o `u-->(u-->g[z])`),
          // pointfreeApplication
          μ o f2m[C[Z, Y], (GF O GF O G)[Y]](`z-->y` => (gf o g)(`z-->y`) o `u-->(u-->g[z])`) o v2gv(`z-->y`),
          // definition σ
          σ o v2gv(`z-->y`)
          // done
        )

  def endoYonedaProof2[Y, X]: (GF O GF O G)[Z] => (C[Y, X] => (C[Z, Y] => Proof[(GF O GF O G)[X]])) =
    `u-->(u-->g[z])` =>
      `y-->x` =>
        import functionalCategory.{f2m, v2gv, yefz, gf, μ}
        val yefz2gfog: EndoNaturalTransformation[C, YEFZ, GF O G] =
          new:
            def τ[Y]: C[YEFZ[Y], (GF O G)[Y]] = μ o f2m(`z-->Y` => (gf o g)(`z-->Y`) o `u-->(u-->g[z])`)
        def σ[Y]: C[YEFZ[Y], (GF O G)[Y]] = yefz2gfog.τ
        `z-->y` =>
          Proof(
            (gf o g)(`y-->x`) o σ o v2gv(`z-->y`),
            // definition σ
            (gf o g)(`y-->x`) o (μ o f2m[C[Z, Y], (GF O GF O G)[Y]](`z-->y` =>
              (gf o g)(`z-->y`) o `u-->(u-->g[z])`
            )) o v2gv(`z-->y`),
            // pointfreeApplication
            (gf o g)(`y-->x`) o (μ o v2gv((gf o g)(`z-->y`) o `u-->(u-->g[z])`)),
            // muProposition
            (gf o g)(`y-->x`) o (gf o g)(`z-->y`) o `u-->(u-->g[z])`,
            // functorCompositionProposition for gf o g
            (gf o g)(`y-->x` o `z-->y`) o `u-->(u-->g[z])`,
            // functionalCategoryMuProposition
            μ o v2gv((gf o g)(`y-->x` o `z-->y`) o `u-->(u-->g[z])`),
            // pointfreeApplication
            μ o f2m[C[Z, X], (GF O GF O G)[X]](`z-->x` => (gf o g)(`z-->x`) o `u-->(u-->g[z])`) o v2gv(
              `y-->x` o `z-->y`
            ),
            // definition σ
            σ o v2gv(`y-->x` o `z-->y`),
            // pointfreeYoneda
            σ o yefz(`y-->x`) o v2gv(`z-->y`)
          )
