# A pointfree Yoneda lemma for endofunctors of functional categories

Also have a look at

- latex/yoneda.pdf

or

- latex/yonedaWithCode.pdf

(latex/yonedaWithCode.pdf is not fully in sync with this document and src (yet))

All comments are welcome at luc.duponcheel [at] gmail.com

## Part 01: Prologue: concepts involved

### The Yoneda lemma

The Yoneda lemma is a fundamantal result of category theory.

The Yoneda lemma is simple.

It involves only three concepts

- category,
- functory,
- natural transformation,

and one category instance

- the category of sets and functions.

Moreover, all functors involved are funtors to the category of sets and functions.

The simplicity of the Yoneda lemma does not imply in any way that the Yoneda lemma is easy.

The Yoneda lemma is pointful: it involves elements of sets.

In fact, being pointful is the essence of the Yoneda lemma.

### Our Yoneda lemma

The Yoneda lemma is also simple.

Our Yoneda lemma involves four concepts

- functional category,
- endofunctor,
- endo natural transformation,
- triple,

and one triple instance

- the triple of global elements.

Functional categories model, perhaps not surprisingly, functional programming.

Their morphisms are also referred to as programs.

The class of objects of functional categories is the class of sets of the category of sets and functions. The
functions of the category of sets and functions can, somehow, be used as programs of functional categories.
Functional categories may have programs that are not functions. Most notably effectful programs, like stateful
programs or programs that interact with the outside world.

The Yoneda lemma is pointfree.

The category of sets and functions does not play an explicit role any more.

### Programmatic notation

In this document, the formulation and proof of both the pointful Yoneda lemma and our pointfree Yoneda lemma
use programmatic notation. More precisely we use `Scala` code. Concepts are typically encoded as `trait`'s and
instances are typically encoded as `given`'s.

There is one important implication of using programmatic notation. The class of objects is encoded as the set
of `Scala` types. Fortunately, it turns out that, both for the proof of the pointful Yoneda lemma and the proof
of our pointfree Yoneda lemma this is not an issue at all. The proofs can easily be translated proofs that use
mathematical notation.

Let's start with the concepts involved.

Later on laws that come with concepts will be defined.

## Part 02: `Category`, `Functor`, `NaturalTransformation` and `Triple`

### `Category`

```scala
package specification

trait Category[C[-_, +_]]:

  def identity[Z]: C[Z, Z]

  def composition[Z, Y, X]: (C[Y, X], C[Z, Y]) => C[Z, X]

  extension [Z, Y, X](`y-->x`: C[Y, X]) def o(`z-->y`: C[Z, Y]): C[Z, X] = composition(`y-->x`, `z-->y`)

```

The `Category` specification for a binary type constructor parameter `C[-_, +_]` declares `def` members,
`identity` and `composition`, and defines an `extension` member, `o`, that is a convenient an infix version of
`composition`.

`Category` specifies a (higher kinded) type class for `C[-_, +_]`.

The `-` and `+` in `C[-_, +_]` declare variance. Like functions of type `Function[Z, Y]`, values of type
`C[Z, Y]` are allowed to require less and provide more (cfr. Liskov substitution principle). Variance is not
used in either the pointful Yoneda lemma or our pointfree Yoneda lemma.

Category parameters are named `C`, `D`, `E`, ... .

Maybe it would be more convenient to name them something like `Cat_C`, `Cat_D`, `Cat_E`, ... .

### `Functor`

```scala
package specification

trait Functor[C[-_, +_]: Category, D[-_, +_]: Category, F[+_]]:
  def f[Z, Y]: C[Z, Y] => D[F[Z], F[Y]]

type EndoFunctor[C[-_, +_], F[+_]] = Functor[C, C, F]
```

The `Functor` specification for a unary type constructor parameter `F[+_]` declares a `def` member `f`.

`Functor` specifies a (higher kinded) type class for `F[+_]`.

The `+` in `F[+_]` declares variance. Like lists of type `List[Z]`, values of type `F[Z]` are allowed to
provide more (cfr. Liskov substitution principle). Variance is not used in either the pointful Yoneda lemma or
our pointfree Yoneda lemma.

Note that `f` is a function

`type` `EndoFunctor` is defined using `Functor` using only one category.

Functor parameters are named `F`, `G`, `H`, `K`, ... .

Maybe it would be more convenient to name them something like `Fun_F`, `Fun_G`, `Fun_H`, `Fun_K`, ... .

### `Natural Transformation`

```scala
package specification

trait NaturalTransformation[
    C[-_, +_]: Category,
    D[-_, +_]: Category,
    F[+_]: [_[+_]] =>> Functor[C, D, F],
    G[+_]: [_[+_]] =>> Functor[C, D, G]
]:

  def τ[Z]: D[F[Z], G[Z]]

type EndoNaturalTransformation[C[-_, +_], F[+_], G[+_]] = NaturalTransformation[C, C, F, G]
```

The `NaturalTransformation` specification declares a `def` member `τ`.

The `trait` does not have a (higher kinded) type parameter like the `C[-_, +_]` of `Category` resp. the
`F[+_]` of `Functor`.

`NaturalTransformation` specifies an object class for natural transformations.

Note that, in the sentence above, the word 'object' has to be understood in the context of object oriented
programming instead of in the context of category theory

Note that `τ` is a morphism.

The `def` members of various natural transformations will be renamed as `σ`, `τ`, `υ`, `ν`, `μ` ... .

`type` `EndoNaturalTransformation` is defined using `NaturalTransformation` using endofunctors.

### `PreTriple` and `Triple`

#### `PreTriple`

Let

```scala
package notation

type I[+Z] = Z
```

in

```scala
package specification

import notation.{I}

trait PreTriple[C[-_, +_]: Category, PT[+_]: [_[+_]] =>> EndoFunctor[C, PT]]:

  val nu: EndoNaturalTransformation[C, I, PT]

  def pt[Z, Y]: C[Z, Y] => C[PT[Z], PT[Y]] = summon[EndoFunctor[C, PT]].f

  def ν[Z]: C[I[Z], PT[Z]] = nu.τ
```

The `PreTriple` specification for an endofunctor `PT[+_]` declares a `val` member `nu` that is an endo natural
transformation from `I[+_]` to `PT[+_]` and defines `pt` corresponding to function `f` and `ν` (Greek letter
nu (for neutral)) corresponding to morphism `τ` of `nu`.

Later on the identity endofunctor for the unary type constructor `I[+_]` will be defined.

#### `Triple`

Let

```scala
package notation

type O = [G[+_], F[+_]] =>> [Z] =>> G[F[Z]]
```

in

```scala
package specification

import notation.{O}

trait Triple[C[-_, +_]: Category, T[+_]: [_[+_]] =>> EndoFunctor[C, T]] extends PreTriple[C, T]:

  val mu: EndoNaturalTransformation[C, T O T, T]

  val tef: EndoFunctor[C, T] = summon[EndoFunctor[C, T]]

  def t[Z, Y]: C[Z, Y] => C[T[Z], T[Y]] = tef.f

  def μ[Z]: C[(T O T)[Z], T[Z]] = mu.τ
```

The `Triple` specification for an endofunctor `T[+_]` declares a `val` member `mu` that is an endo natural
transformation from `(T O T)[+_]` to `T[+_]` and defines `t` corresponding to function `f` and `μ` (Greek
letter 'mu' (for multiplication)) corresponding to the morphism `τ` of `mu`. 

Note that also `tef` has been defined in order to be able to access the endofunctor `T[+_]` outside of
`Triple`. There may be other ways to accomplish this.

Later on the composed functor `(G O F)[+_]` for the binary unary type constructor `O` will be defined.

We are done with our basic specifications.

Let's start with some basic implementations.

## Part 03: `functionCategory`, `identityEndoFunctor` and `composedFunctor`

### `functionCategory`

```scala
package implementation.specific

import specification.{Category}

given functionCategory: Category[Function] with

  def identity[Z]: Function[Z, Z] = z => z

  def composition[Z, Y, X]: (Function[Y, X], Function[Z, Y]) => Function[Z, X] =
    (`y=>x`, `z=>y`) => z => `y=>x`(`z=>y`(z))
```

The specific `functionCategory` implementation for the binary type constructor `Function[-_, +_]` defines `def`
members, `identity` and `composition` in a, hopefully, not very surprising way.

### `identityEndoFunctor`

```scala
package implementation.generic

import notation.{I}

import specification.{Category, EndoFunctor}

given identityEndoFunctor[C[-_, +_]: Category]: EndoFunctor[C, I] with
  def f[Z, Y]: C[Z, Y] => C[I[Z], I[Y]] = `z-->y` => `z-->y`
```

The generic `identityEndoFunctor` implementation for the unary type constructor `I[+_]` defines `def` member
`f` in a, hopefully, not very surprising way.

### `composedFunctor`

```scala
package implementation.generic

import notation.{O}

import specification.{Category, Functor}

given composedFunctor[
    C[-_, +_]: Category,
    D[-_, +_]: Category,
    E[-_, +_]: Category,
    F[+_]: [_[+_]] =>> Functor[C, D, F],
    G[+_]: [_[+_]] =>> Functor[D, E, G]
]: Functor[C, E, G O F] with

  def f[Z, Y]: C[Z, Y] => E[(G O F)[Z], (G O F)[Y]] =
    def f: C[Z, Y] => D[F[Z], F[Y]] = summon[Functor[C, D, F]].f
    def g: D[F[Z], F[Y]] => E[(G O F)[Z], (G O F)[Y]] = summon[Functor[D, E, G]].f
    `z-->y` => g(f(`z-->y`))
```

The generic `composedFunctor` implementation `(G O F)[+_]` for unary type constructor `G[+_]` and unary type
constructor `F[+-]` defines `def`  member `f` in a, hopefully, not very surprising way.

## Part 04: `identityEndoNaturalTransformation` and `composedNaturalTransformation`

### `identityEndoNaturalTransformation`

```scala
package implementation.generic

import notation.{I}

import specification.{Category, EndoNaturalTransformation}

def identityEndoNaturalTransformation[C[-_, +_]: Category]: EndoNaturalTransformation[C, I, I]  =
  new:
    def τ[Z]: C[I[Z], I[Z]] =
      summon[Category[C]].identity
```

The generic `identityEndoNaturalTransformation` implementation defines `def` member `τ` in a, hopefully, not
very surprising way.

Note that `identityEndoNaturalTransformation` is a `def`.

### `composedNaturalTransformation`

```scala
package implementation.generic

import specification.{Category, EndoFunctor, EndoNaturalTransformation}

def composedNaturalTransformation[
    C[-_, +_]: Category,
    F[+_]: [_[+_]] =>> EndoFunctor[C, F],
    G[+_]: [_[+_]] =>> EndoFunctor[C, G],
    H[+_]: [_[+_]] =>> EndoFunctor[C, H],
    S[_[-_, +_], _[-_, +_], _[+_], _[+_]]: [_[
        _[-_, +_],
        _[-_, +_],
        _[+_],
        _[+_]
    ]] =>> EndoNaturalTransformation[
      C,
      F,
      G
    ],
    T[_[-_, +_], _[-_, +_], _[+_], _[+_]]: [_[
        _[-_, +_],
        _[-_, +_],
        _[+_],
        _[+_]
    ]] =>> EndoNaturalTransformation[
      C,
      G,
      H
    ]
]: EndoNaturalTransformation[C, F, H] =

  def σ[Z]: C[F[Z], G[Z]] = summon[EndoNaturalTransformation[C, F, G]].τ

  def τ[Z]: C[G[Z], H[Z]] = summon[EndoNaturalTransformation[C, G, H]].τ

  def υ[Z]: C[F[Z], H[Z]] = τ o σ

  new:
    def τ[Z]: C[F[Z], H[Z]] = υ
```

The generic `composedNaturalTransformation` implementation defines `def`  member `τ` in a, hopefully, not
very surprising way.

Note that `composedNaturalTransformation` is a `def`.

## Part 05: `leftFunctorComposedNaturalTransformation` and `rightFunctorComposedNaturalTransformation`

### `leftFunctorComposedNaturalTransformation`

```scala
package implementation.generic

import notation.{O}

import specification.{Category, Functor, NaturalTransformation}

def leftFunctorComposedNaturalTransformation[
    C[-_, +_]: Category,
    D[-_, +_]: Category,
    E[-_, +_]: Category,
    H[+_]: [_[+_]] =>> Functor[D, E, H],
    F[+_]: [_[+_]] =>> Functor[C, D, F],
    G[+_]: [_[+_]] =>> Functor[C, D, G]
](sigma: NaturalTransformation[C, D, F, G]): NaturalTransformation[C, E, H O F, H O G] =

  given `hof`: Functor[C, E, H O F] = composedFunctor[C, D, E, F, H]

  given `hog`: Functor[C, E, H O G] = composedFunctor[C, D, E, G, H]

  def σ[Z]: D[F[Z], G[Z]] = sigma.τ

  def h[Z, Y]: D[Z, Y] => E[H[Z], H[Y]] = summon[Functor[D, E, H]].f

  def hσ[Z]: E[(H O F)[Z], (H O G)[Z]] = h(σ[Z])

  new:
    def τ[Z]: E[(H O F)[Z], (H O G)[Z]] = hσ
```

The generic `leftFunctorComposedNaturalTransformation` implementation defines `def` member `τ`.

Note that `leftFunctorComposedNaturalTransformation` is a `def` with a natural transformation value parameter
`sigma`.

### `rightFunctorComposedNaturalTransformation`

```scala
package implementation.generic

import notation.{O}

import specification.{Category, Functor, NaturalTransformation}

def rightFunctorComposedNaturalTransformation[
    C[-_, +_]: Category,
    D[-_, +_]: Category,
    E[-_, +_]: Category,
    F[+_]: [_[+_]] =>> Functor[C, D, F],
    H[+_]: [_[+_]] =>> Functor[D, E, H],
    K[+_]: [_[+_]] =>> Functor[D, E, K]
](sigma: NaturalTransformation[D, E, H, K]): NaturalTransformation[C, E, H O F, K O F] =

  given `hof`: Functor[C, E, H O F] = composedFunctor[C, D, E, F, H]

  given `kof`: Functor[C, E, K O F] = composedFunctor[C, D, E, F, K]

  def σ[Z]: E[H[Z], K[Z]] = sigma.τ

  def σf[Z]: E[(H O F)[Z], (K O F)[Z]] = σ[F[Z]]

  new:
    def τ[Z]: E[(H O F)[Z], (K O F)[Z]] = σf
```

The generic `rightFunctorComposedNaturalTransformation` implementation defines `def`  member `τ`.

Note that `rightFunctorComposedNaturalTransformation` is a `def` with a natural transformation value parameter.

Let's continue with some Yoneda related implementations and extending specifications

## Part 06: `yonedaFunctor`, `PreFunctionalCategory`,`yonedaEndoFunctor` and `FunctionalCategory`

### `yonedaFunctor`

Let

```scala
package notation

type Yoneda = [C[-_, +_]] =>> [Z] =>> [Y] =>> C[Z, Y]
```

in

```scala
package implementation.generic

import notation.{Yoneda}

import specification.{Category, Functor}

import implementation.specific.{functionCategory}

given yonedaFunctor[C[-_, +_]: Category, Z]: Functor[C, Function, Yoneda[C][Z]] with

  type YF = [Z] =>> [Y] =>> Yoneda[C][Z][Y]

  def f[Y, X]: C[Y, X] => Function[YF[Z][Y], YF[Z][X]] =
    `y-->x` => `z-->y` => `y-->x` o `z-->y`
```

The generic `yonedaFunctor` implementation for type `Z`, defines `def`  member `f` using morphism composition.

### `PreFunctionalCategory`

```scala
package specification

import notation.{I, Yoneda}

trait PreFunctional[C[-_, +_]] extends Functor[Function, C, I]

trait PreFunctionalCategory[C[-_, +_]] extends Category[C] with PreFunctional[C]:

  def f2m[Z, Y]: Function[Z, Y] => C[Z, Y] = f
```

Using `f2m` of the `PreFunctionalCategory` specification functions of type `Function[Z, Y]` can be used as
morphisms of type `C[Z, Y]`.

The `PreFunctionalCategory` code above is not completed yet.

Later on it will be completed.

### `yonedaEndoFunctor`

```scala
package implementation.generic

import notation.{I, Yoneda}

import specification.{EndoFunctor, PreFunctionalCategory}

import implementation.generic.{composedFunctor}

import implementation.specific.{functionCategory}

given yonedaEndoFunctor[C[-_, +_]: PreFunctionalCategory, Z]: EndoFunctor[C, Yoneda[C][Z]] =

  type YEF = [Z] =>> [Y] =>> Yoneda[C][Z][Y]

  composedFunctor[C, Function, C, YEF[Z], I]
```

`yonedaEndoFunctor` is the composition of two functors.

Later on it will be proved that the composition of two functors satisfies the functor laws.

As a consequence, `yonedaEndoFunctor` satisfies the functor laws.

### `PreFunctionalCategory` revisited

Let

```scala
package notation

type U = Unit
```

in

```scala
package specification

import notation.{I, O, U, Yoneda}

import implementation.generic.{identityEndoFunctor, yonedaFunctor, yonedaEndoFunctor}

trait PreFunctional[C[-_, +_]] extends Functor[Function, C, I] with PreTriple[C, Yoneda[C][U]]

trait PreFunctionalCategory[C[-_, +_]] extends Category[C] with PreFunctional[C]:

  def f2m[Z, Y]: Function[Z, Y] => C[Z, Y] = f

  given PreFunctionalCategory[C] = this

  type GF = [Z] =>> C[U, Z]

  def gf[Z, Y]: C[Z, Y] => C[GF[Z], GF[Y]] =
    yonedaEndoFunctor[C, U].f

  def v2gv[Z]: Function[Z, GF[Z]] = z => f2m(u => z)

  val nu: EndoNaturalTransformation[C, I, GF] =
    new:
      def τ[Z]: C[I[Z], GF[Z]] = f2m(v2gv)

  type YF = [Z] =>> [Y] =>> Yoneda[C][Z][Y]

  def yfz[Z, Y, X]: C[Y, X] => Function[YF[Z][Y], YF[Z][X]] =
    yonedaFunctor[C, Z].f

  type YEF = [Z] =>> [Y] =>> Yoneda[C][Z][Y]

  def yefz[Z, Y, X]: C[Y, X] => C[YEF[Z][Y], YEF[Z][X]] =
    yonedaEndoFunctor[C, Z].f
```

The `PreFunctionalCategory` is a convenient place to define other members.

`type` member `GF` (global functor) is defined as `[Z] =>> C[U, Z]` where `type` `U` is defined as the one
element type `Unit`.

Morphisms of type `GF[Z]`, in this document referred to as global values (of type `Z`), are the pointfree
versionof values (of type `Z`).

`def` member `gf` is defined as function `yonedaEndoFunctor[C, U].f`.

`def` member `v2gv` (value to global value) is defined as function `z => f2m(u => z)`.

Using defined `val` member `nu` of `PreTriple[C, Yoneda[C][U]]`, `def` member `τ: C[Z, GF[Z]]`, a morphism from
values to global values, is defined as `f2m(v2gv)`.

Furthermore `type` members `YF` (Yoneda functor) and `YEF` (Yoneda endofunctor) are defined, and corresponding
`def` members `yfz` and `yefz` are defined as well.

Note that names `yfz` and `yefz` are used since `Z` is not a type parameter of `PreFunctionalCategory`.

Note that `gf` is a special case of `yef`, using type argument `U` for type parameter `Z`.

### `FunctionalCategory`

```scala
package specification

import notation.{I, U, Yoneda}

trait Functional[C[-_, +_]] extends Functor[Function, C, I] with Triple[C, Yoneda[C][U]]

trait FunctionalCategory[C[-_, +_]] extends PreFunctionalCategory[C] with Functional[C]
```

Using declared `val` member `mu` of `Triple[C, Yoneda[C][U]]`, `def` member `τ: C[(GF O GF)[Z], Z], GF[Z]]`, a
morphism from global global values to global values, is declared.

## Part 07: `Law`, `Proof` and `Proposition`

Until now we have not associated any laws with specifications and proofs of laws with implementations.

This document only involves equational laws and corresponding equational proofs.

The pointful Yoneda lemma and the pointfree Yoneda lemma are both propositions.

This document only involves equational propositions and corresponding equational proofs.

### `Law`

```scala
package notation

type Law[Z] = Tuple2[Z, Z]

def Law[Z]: Tuple2[Z, Z] => Law[Z] = identity
```

`type` `Law` is defined as `Tuple[Z, Z]`, requiring both sides of an equational law to have the same type.

`def` `Law` is also defined so that laws can be encoded as `Law(lz, rz)`.

### `Proof`

```scala
package notation

type Proof = [Z] =>> List[Z]

def Proof[Z](zs: Z*): List[Z] = List(zs: _*)
```

`type` `Proof` is defined as `List[Z]`, requiring all steps of an equational proof to have the same type.
For the proofs of this document, especially the ones of generic laws, this provides some confidence that the
proofs are correct.

`def` `Proof` is also defined so that proofs can be encoded as `Proof(z1, z2, z3, ...)`.

### `Proposition`

```scala
package notation

type Proposition[Z] = Tuple2[Z, Z]

def Proposition[Z]: Tuple2[Z, Z] => Proposition[Z] = identity
```

`type` `Proposition` is defined as `Tuple[Z, Z]`, requiring both sides of an equational proposition to have
the same type.

`def` `Proposition` is also defined so that propositions can be encoded as `Proposition(lz, rz)`.

## Part 08: `Category`, `Functor`, `NaturalTransformation` and `Triple` laws

The names of the laws, hopefully, explain what the laws are all about.

### `Category` laws

```scala
package specification

// ...

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
```

The `def` local definition `` `y-->y` `` resp. `` `z-->z` `` are introduced to, hopefully, make the 
`leftIdentityLaw` resp. `rightIdentityLaw` law look natural.

The infix `extension` member `o`, hopefully, makes the `` law look natural

### `Functor` laws

```scala
package specification

// ...

import notation.{Law}

class FunctorLaws[C[-_, +_]: Category, D[-_, +_]: Category, F[+_]: [_[+_]] =>> Functor[C, D, F]]:

  def identityLaw[Z]: Law[D[F[Z], F[Z]]] =
    def `z-c->z`[Z]: C[Z, Z] = summon[Category[C]].identity
    def `f[z]-d->f[z]`[F[Z]]: D[F[Z], F[Z]] = summon[Category[D]].identity
    def f[Z, Y]: C[Z, Y] => D[F[Z], F[Y]] = summon[Functor[C, D, F]].f
    Law(f[Z, Z](`z-c->z`), `f[z]-d->f[z]`)

  def compositionLaw[Z, Y, X]: (C[Z, Y], C[Y, X]) => Law[D[F[Z], F[X]]] =
    (`z-->y`, `y-->x`) =>
      extension [Z, Y, X](`y-->x`: C[Y, X])
        def o_c(`z-->y`: C[Z, Y]): C[Z, X] = summon[Category[C]].o[Z, Y, X](`y-->x`)(`z-->y`)
      extension [Z, Y, X](`y-->x`: D[Y, X])
        def o_d(`z-->y`: D[Z, Y]): D[Z, X] = summon[Category[D]].o[Z, Y, X](`y-->x`)(`z-->y`)
      def f[Z, Y]: C[Z, Y] => D[F[Z], F[Y]] = summon[Functor[C, D, F]].f
      Law(f[Z, X](`y-->x` o_c `z-->y`), f[Y, X](`y-->x`) o_d f[Z, Y](`z-->y`))

```

Local definition are introduced to, hopefully, make laws more readable.

Type parameters are introduced to, hopefully, make laws more understandable.

The `Scala` type system does not warry about names, and, more important, can understand laws without most type
parameters.

```scala
  def identityLaw[Z]: Law[D[F[Z], F[Z]]] =
    def identity_C[Z]: C[Z, Z] = summon[Category[C]].identity
    def identity_D[Z]: D[Z, Z] = summon[Category[D]].identity
    def f[Z, Y]: C[Z, Y] => D[F[Z], F[Y]] = summon[Functor[C, D, F]].f
    Law(f(identity_C), identity_D)

  def compositionLaw[Z, Y, X]: (C[Z, Y], C[Y, X]) => Law[D[F[Z], F[X]]] =
    (`z-->y`, `y-->x`) =>
      def f[Z, Y]: C[Z, Y] => D[F[Z], F[Y]] = summon[Functor[C, D, F]].f
      Law(f(`y-->x` o `z-->y`), f(`y-->x`) o f(`z-->y`))
```

Later on, when proving laws and propositions, the `Scala` type system will turn out to be very helpful.

### `NaturalTransformation` law

```scala
package specification

// ...

import notation.{Law}

class NaturalTransformationLaw[
    C[-_, +_]: Category,
    D[-_, +_]: Category,
    F[+_]: [_[+_]] =>> Functor[C, D, F],
    G[+_]: [_[+_]] =>> Functor[C, D, G],
    T[_[-_, +_], _[-_, +_], _[+_], _[+_]]: [_[_[-_, +_], _[-_, +_], _[+_], _[+_]]] =>> NaturalTransformation[
      C,
      D,
      F,
      G
    ]
]:

  def commutativityLaw[Z, Y]: C[Z, Y] => Law[D[F[Z], G[Y]]] =
    `z-->y` =>
      def f[Z, Y]: C[Z, Y] => D[F[Z], F[Y]] = summon[Functor[C, D, F]].f
      def g[Z, Y]: C[Z, Y] => D[G[Z], G[Y]] = summon[Functor[C, D, G]].f
      extension [Z, Y, X](`y-->x`: D[Y, X])
        def o_d(`z-->y`: D[Z, Y]): D[Z, X] = summon[Category[D]].o(`y-->x`)(`z-->y`)
      def τ[Z]: D[F[Z], G[Z]] = summon[NaturalTransformation[C, D, F, G]].τ
      (τ[Y] o_d f[Z, Y](`z-->y`), g[Z, Y](`z-->y`) o_d τ[Z])
```

Agreed, `commutativityLaw` is, maybe, not the best name since two functors, `f` and `g`, are involved.

Local definition are introduced to, hopefully, make laws more readable.

Type parameters are introduced to, hopefully, make laws more understandable.

The `Scala` type system does not warry about names, and, more important, can understand laws without most type
parameters.

```scala
  def commutativityLaw[Z, Y]: C[Z, Y] => Law[D[F[Z], G[Y]]] =
    `z-->y` =>
      def f[Z, Y]: C[Z, Y] => D[F[Z], F[Y]] = summon[Functor[C, D, F]].f
      def g[Z, Y]: C[Z, Y] => D[G[Z], G[Y]] = summon[Functor[C, D, G]].f
      def τ[Z]: D[F[Z], G[Z]] = summon[NaturalTransformation[C, D, F, G]].τ
      Law(τ o f(`z-->y`), g(`z-->y`) o τ)
```

### `Triple` laws

#### `PreTriple` laws

```scala
package specification

// ...

import notation.{Law}

class PreTripleLaw[C[-_, +_]: Category, PT[+_]: [_[+_]] =>> PreTriple[C, PT]]:

  def commutativityLaw[Z, Y]: C[Z, Y] => Law[C[I[Z], PT[Y]]] =
    `z-->y` =>
      val preTriple: PreTriple[C, PT] = summon[PreTriple[C, PT]]
      import preTriple.{pt, ν}
      import implementation.generic.{identityEndoFunctor}
      def i[Z, Y]: C[Z, Y] => C[I[Z], I[Y]] = identityEndoFunctor.f
      Law(ν[Y] o i[Z, Y](`z-->y`), pt[Z, Y](`z-->y`) o ν[Z])
```

This law is just a special version of an already mentioned one.

Again the `Scala` type system can understand the law without most type parameters.

```scala
  def commutativityLaw[Z, Y]: C[Z, Y] => Law[C[I[Z], PT[Y]]] =
    `z-->y` =>
      val preTriple: PreTriple[C, PT] = summon[PreTriple[C, PT]]
      import preTriple.{pt, ν}
      import implementation.generic.{identityEndoFunctor}
      def i[Z, Y]: C[Z, Y] => C[I[Z], I[Y]] = identityEndoFunctor.f
      Law(ν o i(`z-->y`), pt(`z-->y`) o ν)
```

#### `Triple` laws

```scala
package specification

// ...

import notation.{Law}

class TripleLaws[C[-_, +_]: Category, T[+_]: [_[+_]] =>> Triple[C, T]]:

  val category: Category[C] = summon[Category[C]]

  val triple: Triple[C, T] = summon[Triple[C, T]]

  def commutativityLaw[Z, Y]: C[Z, Y] => Law[C[(T O T)[Z], T[Y]]] =
    `z-->y` =>
      import triple.{t, μ}
      import implementation.specific.{functionCategory}
      Law(μ[Y] o (t[T[Z], T[Y]] o t[Z, Y])(`z-->y`), t[Z, Y](`z-->y`) o μ[Z])

  def leftIdentityLaw[Z]: Law[C[T[Z], T[Z]]] =
    import implementation.generic.{identityEndoNaturalTransformation}
    def ι[Z]: C[Z, Z] = identityEndoNaturalTransformation.τ
    import triple.{ν, μ}
    Law(μ[Z] o ν[T[Z]], ι[T[Z]])

  def rightIdentityLaw[Z]: Law[C[T[Z], T[Z]]] =
    import implementation.generic.{identityEndoNaturalTransformation}
    def ι[Z]: C[Z, Z] = identityEndoNaturalTransformation.τ
    import triple.{t, ν, μ}
    Law(μ[Z] o t[Z, T[Z]](ν[Z]), ι[T[Z]])

  def associativityLaw[Z]: Law[C[(T O T O T)[Z], T[Z]]] =
    import triple.{t, μ}
    Law(μ[Z] o μ[T[Z]], μ[Z] o t[(T O T)[Z], T[Z]](μ[Z]))
```

The first law is just a special version of an already mentioned one.

Again the `Scala` type system can understand the law without most type parameters.

```scala
  def commutativityLaw[Z, Y]: C[Z, Y] => Law[C[(T O T)[Z], T[Y]]] =
    `z-->y` =>
    import implementation.generic.{identityEndoNaturalTransformation}
    def ι[Z]: C[Z, Z] = identityEndoNaturalTransformation.τ
      import implementation.specific.{functionCategory}
      Law(μ o (t o t)(`z-->y`), t(`z-->y`) o (μ))

  def leftIdentityLaw[Z]: Law[C[T[Z], T[Z]]] =
    import implementation.generic.{identityEndoNaturalTransformation}
    def ι[Z]: C[Z, Z] = identityEndoNaturalTransformation.τ
    import triple.{ν, μ}
    Law(μ o ν, ι)

  def rightIdentityLaw[Z]: Law[C[T[Z], T[Z]]] =
    import category.{ι}
    import triple.{t, ν, μ}
    Law(μ o t(ν), ι)

  def associativityLaw[Z]: Law[C[(T O T O T)[Z], T[Z]]] =
    import triple.{t, μ}
    Law(μ o μ, μ o t(μ))
```

It is challenging to translate the laws above back to the ones that use type parameters.

Another way to encode the laws is by using `leftFunctorComposedNaturalTransformation` and
`righFunctorComposedNaturalTransformation`

```scala
  def leftIdentityLaw[Z]: Law[C[T[Z], T[Z]]] =
    import implementation.generic.{identityEndoNaturalTransformation}
    def ι[Z]: C[Z, Z] = identityEndoNaturalTransformation.τ
    import triple.{ν, μ}
    import notation.{I}
    import triple.{nu}
    given EndoFunctor[C, T] = triple.tef
    import implementation.generic.{
      identityEndoFunctor,
      rightFunctorComposedNaturalTransformation
    }
    def νt[Z]: C[T[Z], (T O T)[Z]] = rightFunctorComposedNaturalTransformation(nu).τ
    Law(μ o νt, ι)

  def rightIdentityLaw[Z]: Law[C[T[Z], T[Z]]] =
    import implementation.generic.{identityEndoNaturalTransformation}
    def ι[Z]: C[Z, Z] = identityEndoNaturalTransformation.τ
    import triple.{t, ν, μ}
    import notation.{I}
    import triple.{nu}
    given EndoFunctor[C, T] = triple.tef
    import implementation.generic.{
      identityEndoFunctor,
      leftFunctorComposedNaturalTransformation
    }
    def tν[Z]: C[T[Z], (T O T)[Z]] = leftFunctorComposedNaturalTransformation(nu).τ
    Law(μ o tν, ι)

  def associativityLaw[Z]: Law[C[(T O T O T)[Z], T[Z]]] =
    import triple.{t, μ}
    import notation.{I}
    import triple.{mu}
    given EndoFunctor[C, T] = triple.tef
    import implementation.generic.{
      composedFunctor,
      leftFunctorComposedNaturalTransformation,
      rightFunctorComposedNaturalTransformation
    }
    def μt[Z]: C[(T O T O T)[Z], (T O T)[Z]] = rightFunctorComposedNaturalTransformation(mu).τ
    def tμ[Z]: C[(T O T O T)[Z], (T O T)[Z]] = leftFunctorComposedNaturalTransformation(mu).τ
    Law(μ o μt, μ o tμ)
```

This way to encode the laws is in sync with writinh the laws using mathematical notation.

### Remark

So what is the preferred notation for writing `leftIdentityLaw`?

- `Law(μ[Z] o ν[T[Z]], ι[T[Z]])`
- `Law(μ o ν, ι)`
- `Law(μ o νt, ι)`

Well ... it depends.

For documentation for human beings, perhaps the first notation.

For correspondence with mathematical documents, perhaps the last notation.

Anyway, in contrast with, often used, matematicical "abuse of notation" to simplify notation, the middle
notation, which is the simplest one, is not an example of programmatic "abuse of notation". The Scala type
system is happy with it (and so should human beings be). 

On the one hand, human beings can not fool the `Scala` system by using "abuse of notation".
On the other hand, human beings should start worrying when writing laws the `Scala` type system is not happy
with.

In my opinion this is a situation were software (the `Scala` system) can better deal with complexity than human
beings. Being better with dealing with (not necessarily complexity related) difficulty is another matter.

For sure, there exists software that can assist human beings to deal with difficulty, like proof assistant
software, but, at least as far as I know (I may be wrong) there does not exist software that, out of the blue,
comes up with a proof of, say, the pointful Yoneda lemma resp. our pointful Yoneda lemma, or comes up with 
the formulation of the lemmas themselves.

But, then again, never say never, ... .

## Part 09: `PreFunctionalCategory` and `FunctionalCategory` laws

### `PreFunctionalCategory` laws

```scala
package specification

// ...

import notation.{Law}

class PreFunctionalCategoryLaws[C[-_, +_]: PreFunctionalCategory]:

  val preFunctionalCategory = summon[PreFunctionalCategory[C]]
  import preFunctionalCategory.{GF}

  def commutativityLaw[Z, Y]: C[Z, Y] => Law[C[I[Z], GF[Y]]] =
    `z-->y` =>
      import preFunctionalCategory.{gf, ν}
      def i[Z, Y]: C[Z, Y] => C[Z, Y] = identityEndoFunctor[C].f
      (ν o i(`z-->y`), gf(`z-->y`) o ν)

  import preFunctionalCategory.{f2m}
  import implementation.specific.{functionCategory}

  def compositionLaw[Z, Y, X]
      : Function[Z, Y] => (Function[Y, X] => Law[C[Z, X]]) =
    `z=>y` =>
      `y=>x` =>
        (f2m(`y=>x` o `z=>y`), f2m(`y=>x`) o f2m(`z=>y`))

  def identityLaw[Z]: Law[C[Z, Z]] =
    def `z-->z`[Z]: C[Z, Z] = preFunctionalCategory.identity
    def `z=>z`[Z]: Function[Z, Z] = functionCategory.identity
    (f2m(`z=>z`), `z-->z`)

  def nuLaw[Z]: GF[Z] => Law[(GF O GF)[Z]] =
    `u-->z` =>
      import preFunctionalCategory.{v2gv, ν}
      (ν[Z] o `u-->z`, v2gv[C[U, Z]](`u-->z`))
```

The first three laws are special versions of already mentioned ones.

Again the `Scala` type system can understand the fourth law with less type parameters.

```scala
  def nuLaw[Z]: GF[Z] => Law[(GF O GF)[Z]] =
    `u-->z` =>
      import preFunctionalCategory.{v2gv, ν}
      (ν o `u-->z`, v2gv(`u-->z`))
```

Again, it is challenging to translate the laws above back to the ones that use type parameters.

### `FunctionalCategory` laws

```scala
package specification

// ...

import notation.{O, Law}

import implementation.specific.{functionCategory}

class FunctionalCategoryLaws[C[-_, +_]: FunctionalCategory]:

  val functionalCategory = summon[FunctionalCategory[C]]

  import functionalCategory.{GF}

  def commutativityLaw[Z, Y]: C[Z, Y] => Law[C[(GF O GF)[Z], GF[Y]]] =
    `z-->y` =>
      import functionalCategory.{gf, μ}
      (μ[Y] o (gf[GF[Z], GF[Y]] o gf[Z, Y])(`z-->y`), gf[Z, Y](`z-->y`) o μ[Z])

  import implementation.generic.{identityEndoNaturalTransformation}
  def ι[Z]: C[Z, Z] = identityEndoNaturalTransformation.τ

  def leftIdentityLaw[Z]: Law[C[GF[Z], GF[Z]]] =
    import functionalCategory.{gf, ν, μ}
    (μ[Z] o gf(ν[Z]), ι[GF[Z]])

  def rightIdentityLaw[Z]: Law[C[GF[Z], GF[Z]]] =
    import functionalCategory.{ν, μ}
    (μ[Z] o ν[GF[Z]], ι[GF[Z]])

  def associativityLaw[Z]: Law[C[(GF O GF O GF)[Z], GF[Z]]] =
    import functionalCategory.{gf, μ}
    (μ[Z] o μ[GF[Z]], μ[Z] o gf[(GF O GF)[Z], GF[Z]](μ[Z]))
```

The laws are special versions of already mentioned ones.

Again the `Scala` type system can understand the laws with less type parameters.

```scala
  def commutativityLaw[Z, Y]: C[Z, Y] => Law[C[(GF O GF)[Z], GF[Y]]] =
    `z-->y` =>
      import functionalCategory.{gf, μ}
      (μ o (gf o gf)(`z-->y`), gf(`z-->y`) o μ)

  import implementation.generic.{identityEndoNaturalTransformation}
  def ι[Z]: C[Z, Z] = identityEndoNaturalTransformation.τ

  def leftIdentityLaw[Z]: Law[C[GF[Z], GF[Z]]] =
    import functionalCategory.{gf, ν, μ}
    (μ o gf(ν), ι)

  def rightIdentityLaw[Z]: Law[C[GF[Z], GF[Z]]] =
    import functionalCategory.{ν, μ}
    (μ o ν, ι)

  def associativityLaw[Z]: Law[C[(GF O GF O GF)[Z], GF[Z]]] =
    import functionalCategory.{gf, μ}
    (μ o μ, μ o gf(μ))
```

Again, it is challenging to translate the laws above back to the ones that use type parameters.

We are done with declaring specifications and defining their laws.

## Part 10: `functionFunctionalCategory`

Let

```scala
package notation

val u: U = ()
```

in

```scala
package implementation.specific

import notation.{I, O, U, u}

import specification.{FunctionalCategory, EndoNaturalTransformation}

import implementation.generic.{identityEndoFunctor, composedFunctor, yonedaEndoFunctor}

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
```

Only `def` member `τ` of `val` member `mu` needs to be defined.

Also `def` member `τ` of `val` member `nu` is redefined (cfr. `override`).

Later on the correctness of this redefinition will be proved.

We are done with defining implementations

It is time to start with proofs.

Let's start with specific implementations.

The definitions and auxiliary propositions that are used are written in comments.

## Part 11: `functionCategory` and `functionFunctionalCategory` proofs

### `functionCategory` proofs

```scala
package implementation.specific

// ...

import notation.{Proof}

class FunctionCategoryProofs:

  def associativityProof[Z, Y, X, W]: ((Function[Z, Y], Function[Y, X], Function[X, W]) => Z => Proof[W]) =
    (`z=>y`, `y=>x`, `x=>w`) =>
      z =>
        Proof(
          ((`x=>w` o `y=>x`) o `z=>y`)(z),
          // definition o for function(Functional)Category
          (`x=>w` o `y=>x`)(`z=>y`(z)),
          // definition o for function(Functional)Category
          `x=>w`(`y=>x`(`z=>y`(z))),
          // definition o for function(Functional)Category
          `x=>w`((`y=>x` o `z=>y`)(z)),
          // definition o for functionCategory
          (`x=>w` o (`y=>x` o `z=>y`))(z)
          // done
        )

  def leftIdentityProof[Z, Y]: Function[Z, Y] => Z => List[Y] =
    `z=>y` =>
      z =>
        def `y-->y`[Y] = functionCategory.identity[Y]
        List(
          (`y-->y` o `z=>y`)(z),
          // definition o for functionCategory
          `y-->y`(`z=>y`(z)),
          // definition `y-->y` for functionCategory
          (`z=>y`)(z)
          // done
        )

  def rightIdentityProof[Z, Y]: Function[Z, Y] => Z => List[Y] =
    `z=>y` =>
      z =>
        def `z-->z`[Z] = functionCategory.identity[Z]
        List(
          (`z=>y` o `z-->z`)(z),
          // definition o for functionCategory
          `z=>y`(`z-->z`(z)),
          // definition `z-->z` for functionCategory
          (`z=>y`)(z)
          // done
        )
```

The proofs are simple and easy.

### `functionFunctionalCategory` proofs

```scala
package implementation.specific

// ...

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
        // definition f for function(Functional)Category
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
        // definition definition o for function(Functional)Category (substituting `z=>y`(z) for y)
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
```

The proofs are more complex but they are still easy.

We are done with proofs of specific implementations.

Let's continue with proofs of generic implementations.

The definitions, laws and propositions that are used are written in comments.

## Part 12: `IdentityEndoFunctor` and `ComposedFunctor` proofs

### `IdentityEndoFunctor` proofs

```scala
package implementation.generic

// ...

import notation.{Proof}

class IdentityEndoFunctorProofs[C[-_, +_]: Category]:

  def i[Z, Y]: C[Z, Y] => C[Z, Y] = identityEndoFunctor.f

  def identityProof[Z]: Proof[C[I[Z], I[Z]]] =

    def `z-->z`: C[Z, Z] = summon[Category[C]].identity
    def `i[z]-->i[z]` : C[I[Z], I[Z]] = summon[Category[C]].identity

    List(
      i(`z-->z`),
      // definition i
      `z-->z`,
      // definition `i[z]-->i[z]`
      `i[z]-->i[z]`
      // done
    )

  def compositionProof[Z, Y, X]: C[Z, Y] => C[Y, X] => Proof[C[I[Z], I[X]]] =
    `z-->y` =>
      `y-->x` =>
        Proof(
          i(`y-->x` o `z-->y`),
          // definition i
          `y-->x` o `z-->y`,
          // definition i (twice)
          i(`y-->x`) o i(`z-->y`)
          // done
        )
```

### `ComposedFunctorProofs` proofs

```scala
package implementation.generic

// ...

import notation.{Proof}

class ComposedFunctorProofs[
    C[-_, +_]: Category,
    D[-_, +_]: Category,
    E[-_, +_]: Category,
    F[+_]: [_[+_]] =>> Functor[C, D, F],
    G[+_]: [_[+_]] =>> Functor[D, E, G]
]:

  def f[Z, Y]: C[Z, Y] => D[F[Z], F[Y]] = summon[Functor[C, D, F]].f

  def g[Z, Y]: D[F[Z], F[Y]] => E[(G O F)[Z], (G O F)[Y]] = summon[Functor[D, E, G]].f

  def gof[Z, Y]: C[Z, Y] => E[(G O F)[Z], (G O F)[Y]]= composedFunctor[C, D, E, F, G].f

  def identityProof[Z]: Proof[E[(G O F)[Z], (G O F)[Z]]] =
    val `z-c->z`: C[Z, Z] = summon[Category[C]].identity[Z]
    val `f[z]-d->f[z]` : D[F[Z], F[Z]] = summon[Category[D]].identity[F[Z]]
    val `(gof)[z]-e->(gof)[z]` : E[(G O F)[Z], (G O F)[Z]] = summon[Category[E]].identity[(G O F)[Z]]
    Proof(
      gof(`z-c->z`),
      // definition f for gof
      g(f(`z-c->z`)),
      // identityLaw for f
      g(`f[z]-d->f[z]`),
      // identityLaw for g
      `(gof)[z]-e->(gof)[z]`
      // done
    )

  def compositionProof[Z, Y, X]: C[Z, Y] => (C[Y, X] => Proof[E[(G O F)[Z], (G O F)[X]]]) =
    `z-->y` =>
      `y-->x` =>
        extension [Z, Y, X](`y-->x`: C[Y, X])
          def o_c(`z-->y`: C[Z, Y]): C[Z, X] =
            summon[Category[C]].o[Z, Y, X](`y-->x`)(`z-->y`)
        extension [Z, Y, X](`y-->x`: D[Y, X])
          def o_d(`z-->y`: D[Z, Y]): D[Z, X] =
            summon[Category[D]].o[Z, Y, X](`y-->x`)(`z-->y`)
        extension [Z, Y, X](`y-->x`: E[Y, X])
          def o_e(`z-->y`: E[Z, Y]): E[Z, X] =
            summon[Category[E]].o[Z, Y, X](`y-->x`)(`z-->y`)
        Proof(
          gof(`y-->x` o_c `z-->y`),
          // definition f for gof
          g(f(`y-->x` o_c `z-->y`)),
          // compositionLaw for f
          g(f(`y-->x`) o_d f(`z-->y`)),
          // compositionLaw for g
          g(f(`y-->x`)) o_e g(f(`z-->y`)),
          // definition f for gof
          gof(`y-->x`) o_e gof(`z-->y`)
          // done
        )
```

## Part 13: `IdentityEndoNaturalTransformation` and `ComposedEndoNaturalTransformationProof` proofs

### `IdentityEndoNaturalTransformation` proof

```scala
package implementation.generic

// ...

import notation.{Proof}

class IdentityNaturalTransformationProof[C[-_, +_]: Category]:

  val category = summon[Category[C]]
  import category.{identity}

  def i[Z, Y]: C[Z, Y] => C[I[Z], I[Y]] = identityEndoFunctor.f
  def ι[Z]: C[I[Z], I[Z]] = identityEndoNaturalTransformation.τ

  def commutativityProof[Z, Y]: C[Z, Y] => Proof[C[I[Z], I[Y]]] =
    `z-->y` =>
      Proof(
        ι o i(`z-->y`),
        // definition i
        ι o i(`z-->y`),
        // definition ι
        identity o `z-->y`,
        // left identity law 
        `z-->y`,
        // right identity law 
        `z-->y` o identity,
        // definition ι
        `z-->y` o ι,
        // definition i
        i(`z-->y`) o ι
      )
```

### `ComposedEndoNaturalTransformationProof` proofs

```scala
package implementation.generic

// ...

import notation.{Proof}

class ComposedEndoNaturalTransformationProof[
    C[-_, +_]: Category,
    F[+_]: [_[+_]] =>> EndoFunctor[C, F],
    G[+_]: [_[+_]] =>> EndoFunctor[C, G],
    H[+_]: [_[+_]] =>> EndoFunctor[C, H],
    S[_[-_, +_], _[-_, +_], _[+_], _[+_]]: [_[
        _[-_, +_],
        _[-_, +_],
        _[+_],
        _[+_]
    ]] =>> EndoNaturalTransformation[
      C,
      F,
      G
    ],
    T[_[-_, +_], _[-_, +_], _[+_], _[+_]]: [_[
        _[-_, +_],
        _[-_, +_],
        _[+_],
        _[+_]
    ]] =>> EndoNaturalTransformation[
      C,
      G,
      H
    ]
]:

  def commutativityProof[Z, Y]: C[Z, Y] => Proof[C[F[Z], H[Y]]] =
    def σ[Z]: C[F[Z], G[Z]] = summon[EndoNaturalTransformation[C, F, G]].τ
    def τ[Z]: C[G[Z], H[Z]] = summon[EndoNaturalTransformation[C, G, H]].τ
    def τoσ[Z]: C[F[Z], H[Z]] = composedNaturalTransformation[C, F, G, H, S, T].τ
    def f[Z, Y]: C[Z, Y] => C[F[Z], F[Y]] = summon[EndoFunctor[C, F]].f
    def g[Z, Y]: C[Z, Y] => C[G[Z], G[Y]] = summon[EndoFunctor[C, G]].f
    def h[Z, Y]: C[Z, Y] => C[H[Z], H[Y]] = summon[EndoFunctor[C, H]].f
    `z-->y` =>
      Proof(
        τoσ o f(`z-->y`),
        // definition τ for composedNaturalTransformation
        (τ o σ) o f(`z-->y`),
        // associativityLaw for C
        τ o (σ o f(`z-->y`)),
        // commutativityLaw for S
        τ o (g(`z-->y`) o σ),
        // categoryCompositionAssociativityLaw for C
        (τ o g(`z-->y`)) o σ,
        // commutativityLaw for T
        (h(`z-->y`) o τ) o σ,
        // associativityLaw for C
        h(`z-->y`) o (τ o σ),
        // definition τ for composedNaturalTransformation
        h(`z-->y`) o τoσ
        // done
      )
```

## Part 14: `LeftFunctorComposedNaturalTransformationProof` and `RightFunctorComposedNaturalTransformationProof` proof

### `LeftFunctorComposedNaturalTransformationProof` proof

```scala
package implementation.generic

// ...

import notation.{Proof}

import implementation.specific.{functionCategory}

class LeftFunctorComposedNaturalTransformationProof[
    C[-_, +_]: Category,
    D[-_, +_]: Category,
    E[-_, +_]: Category,
    H[+_]: [_[+_]] =>> Functor[D, E, H],
    F[+_]: [_[+_]] =>> Functor[C, D, F],
    G[+_]: [_[+_]] =>> Functor[C, D, G]
]:

  def commutativityProof[Z, Y](
      sigma: NaturalTransformation[C, D, F, G]
  ): C[Z, Y] => Proof[E[(H O F)[Z], (H O G)[Y]]] =
    `z-->y` =>
      def σ[Z]: D[F[Z], G[Z]] = sigma.τ
      def h[Z, Y]: D[Z, Y] => E[H[Z], H[Y]] = summon[Functor[D, E, H]].f
      def hσ[Z, Y]: E[(H O F)[Z], (H O G)[Z]] =
        leftFunctorComposedNaturalTransformation[C, D, E, H, F, G](sigma).τ
      def f[Z, Y]: C[Z, Y] => D[F[Z], F[Y]] = summon[Functor[C, D, F]].f
      def g[Z, Y]: C[Z, Y] => D[G[Z], G[Y]] = summon[Functor[C, D, G]].f
      import implementation.specific.{functionCategory}
      Proof(
        hσ o (h o f)(`z-->y`),
        // definition τ for leftFunctorComposedNaturalTransformation
        h(σ) o (h o f)(`z-->y`),
        // definition o for functionCategory
        h(σ) o h(f(`z-->y`)),
        // compositionLaw for h
        h(σ o f(`z-->y`)),
        // commutativityLaw for S
        h(g(`z-->y`) o σ),
        // compositionLaw for h
        h(g(`z-->y`)) o h(σ),
        // definition o for functionCategory
        (h o g)(`z-->y`) o h(σ),
        // definition τ for leftFunctorComposedNaturalTransformation
        (h o g)(`z-->y`) o hσ
        // done
      )
```

### `RightFunctorComposedNaturalTransformationProof` proof

```scala
package implementation.generic

// ...

import notation.{Proof}

class RightFunctorComposedNaturalTransformationProof[
    C[-_, +_]: Category,
    D[-_, +_]: Category,
    E[-_, +_]: Category,
    F[+_]: [_[+_]] =>> Functor[C, D, F],
    H[+_]: [_[+_]] =>> Functor[D, E, H],
    K[+_]: [_[+_]] =>> Functor[D, E, K]
]::

  def commutativityProof[Z, Y](
      sigma: NaturalTransformation[D, E, H, K]
  ): C[Z, Y] => Proof[E[(H O F)[Z], (K O F)[Y]]] =
    `z-->y` =>
      def σ[Z]: E[H[Z], K[Z]] = sigma.τ
      def σf[Z]: E[(H O F)[Z], (K O F)[Z]] =
        rightFunctorComposedNaturalTransformation[C, D, E, F, H, K](sigma).τ
      def f[Z, Y]: C[Z, Y] => D[F[Z], F[Y]] = summon[Functor[C, D, F]].f
      def h[Z, Y]: D[Z, Y] => E[H[Z], H[Y]] = summon[Functor[D, E, H]].f
      def k[Z, Y]: D[Z, Y] => E[K[Z], K[Y]] = summon[Functor[D, E, K]].f
      import implementation.specific.{functionCategory}
      Proof(
        σf o (h o f)(`z-->y`),
        // definition τ for rightFunctorComposedNaturalTransformation
        σ[F[Y]] o (h o f)(`z-->y`),
        // definition o for functionCategory
        σ[F[Y]] o h(f(`z-->y`)),
        // commutativityLaw for S (with f(`z-->y`))
        k(f(`z-->y`)) o σ[F[Z]],
        // definition o for functionCategory
        (k o f)(`z-->y`) o σ[F[Z]],
        // definition τ for rightFunctorComposedNaturalTransformation
        (k o f)(`z-->y`) o σf
        // done
      )

```

## Part 15: `Category` Yoneda lemma and proof

```scala
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
```

Natural transformations of type `NaturalTransformation[C, Function, YFZ, G]` are in one-to-one correspondence
with values of type `G[Z]`.

With every natural transformation with morphism `τ` of type `Function[YFZ[Y], G[Y]]` corresponds a value
`` `g[z]` = τ(`z-->z`) `` of type `G[Z]` and with every value `` `g[z]` `` of type `G[Z]` corresponds a
natural transformation with morphism `` σ = `z-->y` => g(`z-->y`)(`g[z]`) `` of type `Function[YFZ[Y], G[Y]]`
such that `τ` is equal to `σ`.

Let

```scala
import notation.{I}

import specification.{EndoFunctor}

import implementation.generic.{identityEndoFunctor}

class YonedaLemmaForIdentity[Z]extends YonedaLemma[Function, Z, I]
```

If `G` is `I`, then, with every natural transformation with morphism `τ` of type `Function[YFZ[Y], Y]`
corresponds a value `` z = τ(`z-->z`) `` of type `Z` and with every value `z` of type `Z` corresponds a
natural transformation with morphism `` σ = `z-->y` => `z-->y`(z) `` of type `Function[YFZ[Y], Y]`
such that `τ` is equal to `σ`.

```scala
package proposition

// ...

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
```

## Part 16: `PreFunctionalCategory` propositions and proofs

```scala
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
```

`pointfreeApplication` and `pointfreeYoneda` are pointfree versions of function application and the Yoneda
endofunctor.

```scala
package proposition

// ...

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
          // pointfreeApplication
          v2gv(`y-->x` o `z-->y`)
          // done
        )
```

## Part 17: `FunctionalCategory` proposition and proof

```scala
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
```

```scala
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
```

Note that `muProof` uses `nuLaw`.

## Part 18: `PreFunctionalCategory` Yoneda lemma and proof

```scala
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
```

With every endo natural transformation with morphism `τ` of type `C[YEFZ[Y], G[Y]]` corresponds a global value
`` `u-->g[z]` = τ o v2gv(`z-->z`) `` of type `(GF O G)[Z]` and with every global value `` `u-->g[z]` `` of type
`(GF O G)[Z]` corresponds an endo natural transformation with morphism
`` σ = f2m(`z-->y` => g(`z-->y`) o `u-->g[z]`) `` of type `C[YEFZ[Y], (GF O G)[Y]]` such that `ν o τ` is equal
to `σ`.

Let

```scala
import notation.{I}

import implementation.generic.identityEndoFunctor

class PreEndoYonedaLemmaForIdentity[C[-_, +_]: PreFunctionalCategory, Z] extends PreEndoYonedaLemma[C, Z, I]
```

If `G` is `I`, then with every endo natural transformation with morphism `τ` of type `C[YEFZ[Y], Y]`
corresponds a global value `` `u-->z` = τ o v2gv(`z-->z`) `` of type `GF[Z]` and with every global value
`` `u-->z` `` of type `GF[Z]` corresponds an endo natural transformation with morphism
`` σ = f2m(`z-->y` => `z-->y` o `u-->z`) `` of type `C[YEFZ[Y], GF[Y]]` such that `ν o τ` is equal to `σ`.

```scala
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
          ν[G[Y]] o σ o v2gv(`z-->y`),
          // rightIdentityLaw for C
          ν o σ o v2gv(`z-->y` o `z-->z`),
          // pointfreeYoneda
          ν o σ o yefz(`z-->y`) o v2gv(`z-->z`),
          // commutativityLaw for ν o τ
          (gf o g)(`z-->y`) o ν o τ o v2gv(`z-->z`),
          // definition `u-->g[z]`
          (gf o g)(`z-->y`) o ν o `u-->g[z]`,
          // muLaw
          (gf o g)(`z-->y`) o v2gv(`u-->g[z]`),
          // definition o for function(Functional)Category
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
            // definition o for function(Functional)Category
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
```

## Part 19: `FunctionalCategory` Yoneda lemma and proof

```scala
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
```

Endo natural transformations of type `EndoNaturalTransformation[C, Function, YFZ, GF O G]` are in one-to-one
correspondence with global global values of type `(GF O GF O G)[Z]`.

With every endo natural transformation with morphism `τ` of type `C[YEFZ[Y], (GF O G)[Y]]` corresponds a global
global value `` `u-->(u-->g[z])` = τ o v2gv(`z-->z`) `` of type `(GF O GF O G)[Z]` and with every global global
value `` `u-->(u-->g[z])` `` of type `(GF O GF OG)[Z]` corresponds an endo natural transformation with morphism
`` σ = μ o functionalCategory.f2m(`z-->y` => (gf o g)(`z-->y`) o `u-->(u-->g[z])`) `` of type
`C[YEFZ[Y], (GF O G)[Y]]]` such that `τ` is equal to `σ`.

Let

```scala
import notation.{I}

import implementation.generic.identityEndoFunctor

class EndoYonedaLemmaForIdentity[C[-_, +_]: FunctionalCategory, Z] extends EndoYonedaLemma[C, Z, I]
```

If `G` is `I`, then, with every endo natural transformation with morphism `τ` of type `C[YEFZ[Y], GF[Y]]`
corresponds a global global value `` `u-->(u-->z)` = τ o v2gv(`z-->z`) `` of type `(GF O GF)[Z]` and with every
global global value `` `u-->(u-->z)` `` of type `(GF O GF)[Z]` corresponds an endo natural transformation with
morphism `` σ = μ o f2m(`z-->y` => gf(`z-->y`) o `u-->(u-->z)`) `` of type `C[YEFZ[Y], GF[Y]]]` such that
`τ` is equal to `σ`.

```scala
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
```

`preEndoYonedaLemma1` for `PreFunctionalCategory` can be seen as a special case of `endoYonedaLemma1` for
`FunctionalCategory`.

```scala
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
            // μ proposition for (GF, μ, ν)
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
```

## Part20: Epilogue: Laws used

Did we use all `FunctionalCategory laws`?

Let's list them again

1. `μ` `commutativityLaw` for triple`GF`
2. `μ` and `ν` `leftIdentityLaw` for triple`GF`
3. `μ` and `ν` `rightIdentityLaw` for triple`GF`
4. `μ` `associativityLaw` for triple `GF`
5. `f2m` `compositionLaw` for functor `Functor[Function, C, I]`
6. `f2m` `identityLaw` for functor `Functor[Function, C, I]`
7. `ν` `commutativityLaw` for preTriple `GF`
8. `ν` `nuLaw` for preTriple `GF`

- `pointfreeApplicationProof` uses 5. 
- `pointfreeYonedaProof` uses 2.
- `muProof` uses 8. and 2.`
- `preEndoYonedaProof1` of `PreFunctionalCategory` uses 7.