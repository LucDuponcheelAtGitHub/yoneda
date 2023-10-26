package notation

type Yoneda = [C[-_, +_]] =>> [Z] =>> [Y] =>> C[Z, Y]

type Curry[C[-_, +_]] = [Z] =>> [Y] =>> C[Z, Y]
