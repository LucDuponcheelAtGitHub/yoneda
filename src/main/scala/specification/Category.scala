package specification

trait Category[C[-_, +_]]:

  def identity[Z]: C[Z, Z]

  def composition[Z, Y, X]: (C[Y, X], C[Z, Y]) => C[Z, X]

  extension [Z, Y, X](`y-->x`: C[Y, X]) def o(`z-->y`: C[Z, Y]): C[Z, X] = composition(`y-->x`, `z-->y`)

import notation.{Law}

class CategoryLaws[C[-_, +_]: Category]:

  val category = summon[Category[C]]

  def leftIdentityLaw[Z, Y]: C[Z, Y] => Law[C[Z, Y]] =
    `z-->y` =>
      def `y-->y`[Y]: C[Y, Y] = category.identity
      Law(`y-->y` o `z-->y`, `z-->y`)

  def rightIdentityLaw[Z, Y]: C[Z, Y] => Law[C[Z, Y]] =
    `z-->y` =>
      def `z-->z`[Z]: C[Z, Z] = category.identity
      Law(`z-->y` o `z-->z`, `z-->y`)

  def associativityLaw[Z, Y, X, W]: (C[Z, Y], C[Y, X], C[X, W]) => Law[C[Z, W]] =
    (`z-->y`, `y-->x`, `x-->w`) => Law((`x-->w` o `y-->x`) o `z-->y`, `x-->w` o (`y-->x` o `z-->y`))
