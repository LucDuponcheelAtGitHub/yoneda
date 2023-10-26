package implementation.generic

import notation.{I, Yoneda}

import specification.{EndoFunctor, PreFunctionalCategory}

import implementation.generic.{composedFunctor}

import implementation.specific.{functionCategory}

given yonedaEndoFunctor[C[-_, +_]: PreFunctionalCategory, Z]: EndoFunctor[C, Yoneda[C][Z]] =

  type YEF = [Z] =>> [Y] =>> Yoneda[C][Z][Y]

  composedFunctor[C, Function, C, YEF[Z], I]
