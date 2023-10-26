package implementation.specific

import notation.{I, O, U, u}

import specification.{FunctionalCategory, EndoNaturalTransformation}

import implementation.generic.{identityEndoFunctor, composedFunctor, yonedaFunctor, yonedaEndoFunctor}

given functionFunctionalCategory: FunctionalCategory[Function] with
  def composition[Z, Y, X]: (Function[Y, X], Function[Z, Y]) => Function[Z, X] = functionCategory.composition

  def identity[Z]: Function[Z, Z] = functionCategory.identity

  def f[Z, Y]: Function[Z, Y] => Function[I[Z], I[Y]] = identityEndoFunctor.f

  override val nu: EndoNaturalTransformation[Function, I, GF] =
    new:
      def τ[Z]: Function[I[Z], GF[Z]] = z => u => z

  val mu: EndoNaturalTransformation[Function, GF O GF, GF] =
    new:
      def τ[Z]: Function[(GF O GF)[Z], GF[Z]] = `u=>(u=>z)` => `u=>(u=>z)`(u)

import notation.{Law}

import implementation.specific.{functionCategory}

class FunctionFunctionalCategoryProposition:

  import functionFunctionalCategory.{GF}

  def f2mProposition[Z, Y]: Function[Z, Y] => Law[Function[Z, Y]] =
    import functionFunctionalCategory.{f2m}
    `z=>y` => Law(f2m(`z=>y`), `z=>y`)

  def nuProposition[Z]: Law[Function[I[Z], GF[Z]]] =
    import functionFunctionalCategory.{f2m, v2gv}
    Law(f2m(v2gv), z => u => z)

  def gfProposition[Z, Y]: Function[Z, Y] => Law[Function[GF[Z], GF[Y]]] =
    import functionFunctionalCategory.{gf, yfz}
    `z=>y` => Law(gf(`z=>y`), yfz(`z=>y`))

import notation.{Proof}

import implementation.specific.{functionCategory}

class FunctionFunctionalCategoryProofs:

  import functionFunctionalCategory.{GF, f, f2m, v2gv, ν}

  def f2mPropositionProof[Z, Y]: Function[Z, Y] => Proof[Function[Z, Y]] =
    `z=>y` =>
      Proof(
        f2m(`z=>y`),
        // definition f2m
        f(`z=>y`),
        // definition f for functionCategory
        identityEndoFunctor.f(`z=>y`),
        // definition f for identityEndoFunctor
        `z=>y`
      )

  def nuPropositionProof[Z]: Proof[Function[I[Z], GF[Z]]] =
    Proof(
      ν,
      // definition ν
      f2m(v2gv),
      // definition v2gv
      f2m(z => f2m(u => z)),
      // f2mProposition (twice)
      z => u => z
    )

  def gfPropositionProof[Z, Y]: Function[Z, Y] => Proof[Function[GF[Z], GF[Y]]] =
    import functionFunctionalCategory.{f, gf, yfz, yefz, f2m}
    `z=>y` =>
      Proof(
        gf(`z=>y`),
        // definition gf
        yonedaEndoFunctor[Function, U].f(`z=>y`),
        // definition yonedaEndoFunctor (via composedFunctor)
        f2m(yonedaFunctor[Function, U].f(`z=>y`)),
        // f2mProposition
        yonedaFunctor[Function, U].f(`z=>y`),
        // definition yfz
        yfz(`z=>y`)
      )

  def nuCommutativityProof[Z, Y]: Function[Z, Y] => Proof[Function[I[Z], GF[Y]]] =
    `z=>y` =>
      import functionFunctionalCategory.{yfz, gf, ν}
      def i[Z, Y]: Function[Z, Y] => Function[Z, Y] = identityEndoFunctor.f
      Proof(
        gf(`z=>y`) o ν,
        // gfProposition
        yfz(`z=>y`) o ν,
        // definition ν for function(Pre)FunctionalCategory
        yfz(`z=>y`) o (z => (u => z)),
        // definition o for function(Functional)Category
        z => yfz(`z=>y`)(u => z),
        // definition yfz
        z => `z=>y` o (u => z),
        // definition o for function(Functional)Category
        z => u => `z=>y`(z),
        // definition o for function(Functional)Category (substituting `z=>y`(z) for y)
        ((y: Y) => (u: U) => y) o (z => `z=>y`(z)),
        // lambda calculus eta conversion
        ((y: Y) => ((u: U) => y)) o `z=>y`,
        // definition ν
        ν o `z=>y`,
        // definition identityEndoFunctor.f
        ν o identityEndoFunctor.f(`z=>y`),
        // definition i
        ν o i(`z=>y`)
        // done
      )

  def muCommutativityProof[Z, Y]: Function[Z, Y] => Proof[(GF O GF)[Z] => GF[Y]] =
    `z=>y` =>
      import functionFunctionalCategory.{yfz, gf, μ}
      Proof(
        gf(`z=>y`) o μ,
        // gfProposition
        yfz(`z=>y`) o μ,
        // definition μ for functionFunctionalCategory
        yfz(`z=>y`) o (`u=>(u=>z)` => `u=>(u=>z)`(u)),
        // definition o for function(Functional)Category
        `u=>(u=>z)` => yfz(`z=>y`)(`u=>(u=>z)`(u)),
        // definition yfz
        `u=>(u=>z)` => (`z=>y` o `u=>(u=>z)`(u)),
        // eta conversion lambda calculus
        (`u=>(u=>z)` => ((u: U) => (`z=>y` o `u=>(u=>z)`(u)))(u)),
        // definition o for function(Functional)Category
        ((`u=>(u=>y)`: (GF O GF)[Y]) => `u=>(u=>y)`(u)) o (`u=>(u=>z)` => (u => `z=>y` o `u=>(u=>z)`(u))),
        // definition o for function(Functional)Category
        ((`u=>(u=>y)`: (GF O GF)[Y]) => `u=>(u=>y)`(u)) o (`u=>(u=>z)` =>
          ((`u=>z`: GF[Z]) => `z=>y` o `u=>z`) o (u => `u=>(u=>z)`(u))
        ),
        // eta conversion lambda calculus
        (((`u=>(u=>y)`: (GF O GF)[Y]) => `u=>(u=>y)`(u)) o (`u=>(u=>z)` =>
          ((`u=>z`: GF[Z]) => `z=>y` o `u=>z`) o `u=>(u=>z)`
        )),
        // definition yfz
        (((`u=>(u=>y)`: (GF O GF)[Y]) => `u=>(u=>y)`(u)) o yfz((`u=>z`: GF[Z]) => `z=>y` o `u=>z`)),
        // definition yfz
        (((`u=>(u=>y)`: (GF O GF)[Y]) => `u=>(u=>y)`(u)) o yfz(yfz(`z=>y`))),
        // definition μ for functionFunctionalCategory
        μ o yfz(yfz(`z=>y`)),
        // gfProposition twice
        μ o gf(gf(`z=>y`))
        // done
      )

  def nuProof[Z]: GF[Z] => Proof[(GF O GF)[Z]] =
    `u=>z` =>
      import functionFunctionalCategory.{f2m, v2gv, ν}
      Proof(
        ν o `u=>z`,
        // definition ν for function(Pre)FunctionalCategory
        ((z: Z) => ((u: U) => z)) o `u=>z`,
        // eta conversion lambda calculus
        (((z: Z) => ((u: U) => z)) o (u => `u=>z`(u))),
        // definition o for function(Functional)Category
        u => (u => `u=>z`(u)),
        // eta conversion lambda calculus
        u => `u=>z`,
        // f2mProposition
        f2m(u => `u=>z`),
        // definition v2gv
        v2gv(`u=>z`)
        // done
      )

  import implementation.generic.{identityEndoNaturalTransformation}
  def ι[Z]: Function[Z, Z] = identityEndoNaturalTransformation.τ

  def leftIdentityProof[Z]: Proof[GF[Z] => GF[Z]] =
    import functionFunctionalCategory.{f2m, yfz, yefz, gf, ν, μ}
    Proof(
      μ o gf(ν),
      // gfProposition
      μ o yfz(ν),
      // definition ν for function(Pre)FunctionalCategory
      μ o yfz(f2m(z => u => z)),
      // f2mProposition
      μ o yfz(z => u => z),
      // definition μ for functionFunctionalCategory
      ((`u=>(u=>z)`: (GF O GF)[Z]) => `u=>(u=>z)`(u)) o yfz(z => u => z),
      // definition yfz
      ((`u=>(u=>z)`: (GF O GF)[Z]) => `u=>(u=>z)`(u)) o (`u=>z` => ((z: Z) => ((u: U) => z)) o `u=>z`),
      // definition o for function(Functional)Category
      `u=>z` => (((z: Z) => ((u: U) => z)) o `u=>z`)(u),
      // lambda calculus ν conversion
      `u=>z` => (((z: Z) => ((u: U) => z)) o (u => `u=>z`(u)))(u),
      // definition o for function(Functional)Category
      `u=>z` => (u => `u=>z`(u)),
      // lambda calculus ν conversion
      (`u=>z` => `u=>z`),
      // definition ι for function(Functional)Category
      ι
      // done
    )

  def rightIdentityProof[Z]: Proof[GF[Z] => GF[Z]] =
    import functionFunctionalCategory.{ν, μ}
    Proof(
      μ o ν,
      // definition ν for function(Pre)FunctionalCategory
      μ o (`u=>z` => (u => `u=>z`)),
      // definition μ for functionFunctionalCategory
      ((`u=>(u=>z)`: (GF O GF)[Z]) => `u=>(u=>z)`(u)) o (`u=>z` => (_ => `u=>z`)),
      // definition o for function(Functional)Category
      `u=>z` => ((u: U) => `u=>z`)(u),
      // eta conversion lambda calculus
      `u=>z` => `u=>z`,
      // definition ι for function(Functional)Category
      ι
      // done
    )

  def associativityProof[Z]: Proof[(GF O GF O GF)[Z] => GF[Z]] =
    import functionFunctionalCategory.{f2m, yfz, yefz, gf, μ}
    Proof(
      μ o μ,
      // definition μ for functionFunctionalCategory (twice)
      (((`u=>(u=>z)`: (GF O GF)[Z]) => `u=>(u=>z)`(u)) o ((`u=>(u=>(u=>z))`: (GF O GF O GF)[Z]) =>
        `u=>(u=>(u=>z))`(u)
      )),
      // definition o for function(Functional)Category
      (`u=>(u=>(u=>z))`: (GF O GF O GF)[Z]) => `u=>(u=>(u=>z))`(u)(u),
      // definition o for function(Functional)Category
      (`u=>(u=>(u=>z))`: (GF O GF O GF)[Z]) =>
        (((`u=>(u=>z)`: (GF O GF)[Z]) => `u=>(u=>z)`(u)) o `u=>(u=>(u=>z))`)(u),
      // definition o for function(Functional)Category
      ((`u=>(u=>z)`: (GF O GF)[Z]) => `u=>(u=>z)`(u)) o (`u=>(u=>(u=>z))` =>
        ((`u=>(u=>z)`: (GF O GF)[Z]) => `u=>(u=>z)`(u)) o `u=>(u=>(u=>z))`
      ),
      // definition yfz
      ((`u=>(u=>z)`: (GF O GF)[Z]) => `u=>(u=>z)`(u)) o yfz(`u=>(u=>z)` => `u=>(u=>z)`(u)),
      // definition gfProposition
      ((`u=>(u=>z)`: (GF O GF)[Z]) => `u=>(u=>z)`(u)) o gf(`u=>(u=>z)` => `u=>(u=>z)`(u)),
      // definition μ for functionFunctionalCategory
      μ o gf(μ)
      // done
    )
