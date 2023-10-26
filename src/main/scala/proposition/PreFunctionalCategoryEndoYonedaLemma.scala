package proposition

import notation.{O, U, Law, Yoneda}

import specification.{PreFunctionalCategory, EndoFunctor, EndoNaturalTransformation}

import implementation.generic.{composedFunctor, yonedaEndoFunctor}

import implementation.specific.{functionCategory}

class PreEndoYonedaLemma[C[-_, +_]: PreFunctionalCategory, Z, G[+_]: [G[+_]] =>> EndoFunctor[C, G]]:

  val preFunctionalCategory = summon[PreFunctionalCategory[C]]

  import preFunctionalCategory.{GF}

  type YEFZ = [Y] =>> Yoneda[C][Z][Y]

  def g[Z, Y]: C[Z, Y] => C[G[Z], G[Y]] = summon[EndoFunctor[C, G]].f

  def preEndoYonedaLemma1[Y]: EndoNaturalTransformation[C, YEFZ, G] => Law[C[YEFZ[Y], (GF O G)[Y]]] =
    yefz2g =>

      import preFunctionalCategory.{identity, f2m, v2gv, ν}
      def `z-->z`[Z]: C[Z, Z] = identity
      def τ[Y]: C[YEFZ[Y], G[Y]] = yefz2g.τ
      def `u-->g[z]` : (GF O G)[Z] = τ o v2gv(`z-->z`)
      val yefz_2_gfog: EndoNaturalTransformation[C, YEFZ, GF O G] =
        new:
          def τ[Y]: C[YEFZ[Y], (GF O G)[Y]] = f2m(`z-->y` => g(`z-->y`) o `u-->g[z]`)
      def σ[Y]: C[YEFZ[Y], (GF O G)[Y]] = yefz_2_gfog.τ
      Law(ν[G[Y]] o τ, σ)
      Law(ν o τ, σ)

  def preEndoYonedaLemma2[Y, X]: (GF O G)[Z] => (C[Y, X] => Law[C[YEFZ[Y], (GF O G)[X]]]) =
    `u-->g[z]` =>
      `y-->x` =>
        import preFunctionalCategory.{f2m, yefz, gf}
        val yefz2gfog: EndoNaturalTransformation[C, YEFZ, GF O G] =
          new:
            def τ[Y]: C[YEFZ[Y], (GF O G)[Y]] = f2m(`z-->y` => g(`z-->y`) o `u-->g[z]`)
        def σ[Y]: C[YEFZ[Y], (GF O G)[Y]] = yefz2gfog.τ
        Law((gf o g)(`y-->x`) o σ, σ o yefz(`y-->x`))

import notation.{I}

import implementation.generic.identityEndoFunctor

class PreEndoYonedaLemmaForIdentity[C[-_, +_]: PreFunctionalCategory, Z] extends PreEndoYonedaLemma[C, Z, I]

import notation.{Proof}

class PreEndoYonedaProof[C[-_, +_]: PreFunctionalCategory, Z, G[+_]: [G[+_]] =>> EndoFunctor[C, G]]:

  val preFunctionalCategory = summon[PreFunctionalCategory[C]]

  import preFunctionalCategory.{GF, gf}

  type YEFZ = [Y] =>> Yoneda[C][Z][Y]

  def g[Z, Y]: C[Z, Y] => C[G[Z], G[Y]] = summon[EndoFunctor[C, G]].f

  def preEndoYonedaProof1[Y]: EndoNaturalTransformation[C, YEFZ, G] => (C[Z, Y] => Proof[(GF O GF O G)[Y]]) =
    yefz2gfog =>
      import preFunctionalCategory.{identity, f2m, v2gv, yefz, ν}
      def `z-->z`[Z]: C[Z, Z] = identity
      def τ[Y]: C[YEFZ[Y], G[Y]] = yefz2gfog.τ
      def `u-->g[z]` : (GF O G)[Z] = τ o v2gv(`z-->z`)
      val yefz_2_gfog: EndoNaturalTransformation[C, YEFZ, GF O G] =
        new:
          def τ[Y]: C[YEFZ[Y], (GF O G)[Y]] = f2m(`z-->y` => g(`z-->y`) o `u-->g[z]`)
      def σ[Y]: C[YEFZ[Y], (GF O G)[Y]] = yefz_2_gfog.τ
      `z-->y` =>
        Proof(
          ν[G[Y]] o τ o v2gv(`z-->y`),
          // rightIdentityLaw for C
          ν o τ o v2gv(`z-->y` o `z-->z`),
          // pointfreeYoneda
          ν o τ o yefz(`z-->y`) o v2gv(`z-->z`),
          // commutativityLaw for ν o τ
          (gf o g)(`z-->y`) o ν o τ o v2gv(`z-->z`),
          // definition `u-->g[z]`
          (gf o g)(`z-->y`) o ν o `u-->g[z]`,
          // muLaw
          (gf o g)(`z-->y`) o v2gv(`u-->g[z]`),
          // definition o for functionCategory
          gf(g(`z-->y`)) o v2gv(`u-->g[z]`),
          // definition gf
          yefz[U, G[Z], G[Y]](g(`z-->y`)) o v2gv(`u-->g[z]`),
          // pointfreeYoneda
          v2gv(g(`z-->y`) o `u-->g[z]`),
          // pointfreeApplication
          f2m[C[Z, Y], (GF O G)[Y]](`z-->y` => g(`z-->y`) o `u-->g[z]`) o v2gv(`z-->y`),
          // definition σ
          (σ o v2gv(`z-->y`))
          // done
        )

  def preEndoYonedaProof2[Y, X]: (GF O G)[Z] => (C[Y, X] => (C[Z, Y] => Proof[(GF O GF O G)[X]])) =
    `u-->g[z]` =>
      `y-->x` =>
        import preFunctionalCategory.{f2m, v2gv, yefz, gf}
        val yefz2gfog: EndoNaturalTransformation[C, YEFZ, GF O G] =
          new:
            def τ[Y]: C[YEFZ[Y], (GF O G)[Y]] = f2m(`z-->y` => g(`z-->y`) o `u-->g[z]`)
        def σ[Y]: C[YEFZ[Y], (GF O G)[Y]] = yefz2gfog.τ
        `z-->y` =>
          Proof(
            (gf o g)(`y-->x`) o σ o v2gv(`z-->y`),
            // definition σ
            (gf o g)(`y-->x`) o f2m[C[Z, Y], (GF O G)[Y]](`z-->y` => g(`z-->y`) o `u-->g[z]`) o v2gv(`z-->y`),
            // pointfreeApplication
            (gf o g)(`y-->x`) o v2gv(g(`z-->y`) o `u-->g[z]`),
            // definition o for functionCategory
            gf(g(`y-->x`)) o v2gv(g(`z-->y`) o `u-->g[z]`),
            // defintion gf
            yefz[U, G[Y], G[X]](g(`y-->x`)) o v2gv(g(`z-->y`) o `u-->g[z]`),
            // pointfreeYoneda
            v2gv(g(`y-->x`) o g(`z-->y`) o `u-->g[z]`),
            // compositionLaw for g
            v2gv(g(`y-->x` o `z-->y`) o `u-->g[z]`),
            // pointfreeApplication
            f2m[C[Z, X], (GF O G)[X]](`z-->x` => g(`z-->x`) o `u-->g[z]`) o v2gv(`y-->x` o `z-->y`),
            // definition σ
            σ o v2gv(`y-->x` o `z-->y`),
            // pointfreeYoneda
            σ o yefz(`y-->x`) o v2gv(`z-->y`)
            // done
          )
