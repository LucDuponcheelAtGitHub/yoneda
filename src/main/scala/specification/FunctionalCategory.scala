package specification

import notation.{I, U, Yoneda}

trait Functional[C[-_, +_]] extends Functor[Function, C, I] with Triple[C, Yoneda[C][U]]

trait FunctionalCategory[C[-_, +_]] extends PreFunctionalCategory[C] with Functional[C]

import notation.{O, Law}

import implementation.specific.{functionCategory}

class FunctionalCategoryLaws[C[-_, +_]: FunctionalCategory]:

  val functionalCategory = summon[FunctionalCategory[C]]

  import functionalCategory.{GF}

  def commutativityLaw[Z, Y]: C[Z, Y] => Law[C[(GF O GF)[Z], GF[Y]]] =
    `z-->y` =>
      import functionalCategory.{gf, μ}
      (μ[Y] o (gf[GF[Z], GF[Y]] o gf[Z, Y])(`z-->y`), gf[Z, Y](`z-->y`) o μ[Z])
      (μ o (gf o gf)(`z-->y`), gf(`z-->y`) o μ)

  import implementation.generic.{identityEndoNaturalTransformation}
  def ι[Z]: C[Z, Z] = identityEndoNaturalTransformation.τ

  def leftIdentityLaw[Z]: Law[C[GF[Z], GF[Z]]] =
    import functionalCategory.{gf, ν, μ}
    (μ[Z] o gf(ν[Z]), ι[GF[Z]])
    (μ o gf(ν), ι)

  def rightIdentityLaw[Z]: Law[C[GF[Z], GF[Z]]] =
    import functionalCategory.{ν, μ}
    (μ[Z] o ν[GF[Z]], ι[GF[Z]])
    (μ o ν, ι)

  def associativityLaw[Z]: Law[C[(GF O GF O GF)[Z], GF[Z]]] =
    import functionalCategory.{gf, μ}
    (μ[Z] o μ[GF[Z]], μ[Z] o gf[(GF O GF)[Z], GF[Z]](μ[Z]))
    (μ o μ, μ o gf(μ))
