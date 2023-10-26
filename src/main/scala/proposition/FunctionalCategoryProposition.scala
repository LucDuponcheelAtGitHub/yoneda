package proposition

import notation.{I, O, Proposition}

import specification.{EndoNaturalTransformation, FunctionalCategory}

class FunctionalCategoryProposition[Z, C[-_, +_]: FunctionalCategory]:

  val functionalCategory = summon[FunctionalCategory[C]]

  import functionalCategory.{GF}

  def muProposition[Z]: (GF O GF)[Z] => Proposition[(GF O GF)[Z]] =
    `u-->(u-->z)` =>
      import functionalCategory.{v2gv, μ}
      (μ o v2gv(`u-->(u-->z)`), `u-->(u-->z)`)

import notation.{Proof}

class FunctionalCategoryProof[Z, C[-_, +_]: FunctionalCategory]:

  val functionalCategory = summon[FunctionalCategory[C]]

  import functionalCategory.{GF}

  def muProof[Z]: (GF O GF)[Z] => Proof[(GF O GF)[Z]] =
    `u-->(u-->z)` =>
      import implementation.generic.{identityEndoNaturalTransformation}
      def ι[Z]: C[Z, Z] = identityEndoNaturalTransformation.τ
      import functionalCategory.{v2gv, ν, μ}
      Proof(
        μ o v2gv(`u-->(u-->z)`),
        // nuLaw for GF
        μ o (ν o `u-->(u-->z)`),
        // associativityLaw for C
        (μ o ν) o `u-->(u-->z)`,
        // leftIdentityLaw for GF
        `u-->(u-->z)` o ι,
        // rightIdentityLaw for C
        `u-->(u-->z)`
      )
