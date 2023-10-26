package proposition

import notation.{Proposition}

import specification.{PreFunctionalCategory}

class PreFunctionalCategoryPropositions[C[-_, +_]: PreFunctionalCategory]:

  val preFunctionalCategory = summon[PreFunctionalCategory[C]]

  import preFunctionalCategory.{GF}

  def pointfreeApplication[Z, Y]: Function[Z, Y] => Z => Proposition[GF[Y]] =
    `z=>y` =>
      z =>
        import preFunctionalCategory.{v2gv, f2m}
        (f2m(`z=>y`) o v2gv(z), v2gv(`z=>y`(z)))

  def pointfreeYoneda[Z, Y, X]: C[Z, Y] => C[Y, X] => Proposition[GF[C[Z, X]]] =
    `z-->y` =>
      `y-->x` =>
        import preFunctionalCategory.{v2gv, yefz}
        (yefz(`y-->x`) o v2gv(`z-->y`), v2gv(`y-->x` o `z-->y`))

import implementation.specific.{functionCategory}

import notation.{Proof}

class PreFunctionalCategoryProofs[Z, C[-_, +_]: PreFunctionalCategory]:

  val preFunctionalCategory = summon[PreFunctionalCategory[C]]

  import preFunctionalCategory.{GF}

  def pointfreeApplicationProof[Z, Y]: Function[Z, Y] => Z => Proof[GF[Y]] =
    `z=>y` =>
      z =>
        import preFunctionalCategory.{f2m, v2gv}
        Proof(
          f2m(`z=>y`) o v2gv(z),
          // definition v2gv
          f2m(`z=>y`) o f2m(u => z),
          // compositionLaw for f2m
          f2m(`z=>y` o (u => z)),
          // definition o for functionCategory
          f2m(u => `z=>y`(z)),
          // definition v2gv
          v2gv(`z=>y`(z))
          // done
        )

  def pointfreeYonedaProof[Y, X]: C[Z, Y] => C[Y, X] => Proof[GF[C[Z, X]]] =
    `z-->y` =>
      `y-->x` =>
        import preFunctionalCategory.{f2m, yfz, yefz, v2gv}
        Proof(
          yefz(`y-->x`) o v2gv(`z-->y`),
          // definition yefz
          f2m(yfz(`y-->x`)) o v2gv(`z-->y`),
          // definition yfz
          f2m[C[Z, Y], C[Z, X]](`z-->y` => `y-->x` o `z-->y`) o v2gv(`z-->y`),
          // pointfreeApplicationProposition
          v2gv(`y-->x` o `z-->y`)
          // done
        )
