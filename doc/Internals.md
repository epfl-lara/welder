
Welder Internals
================

In this file, we expose some of the implementation details of the library.
This documentation is intended for people wishing to contribute to the library.

Scoping `Theorem`s 
==================

Some functions, such as `implI`, make it possible to obtain a `Theorem` for any given property.
The catch is that those `Theorems` are supposed to be used only within a certain scope.

```scala
implE(BooleanLiteral(false)) { (falseAsThm: Theorem) => 
  ??? // Some derivation that can use `falseAsThm`.
}

// `falseAsThm` is no longer in scope.
```

A problem arises when mutable variables or exceptions come into play.
Using those features, it is easy to make the `Theorem` escape the scope
it was supposed to be enclosed in.

```scala
var illegalThm: Theorem = null

implE(BooleanLiteral(false)) { (falseAsThm: Theorem) =>

  illegalThm = falseAsThm

  ??? // Some derivation that can use `falseAsThm`.
}

// `falseAsThm` is no longer in scope.
// But `illegalThm` contains its value, a `Theorem` for `false`.
```

Markings
--------

To circumvent this problem, we introduce markings.
Each object of the class `Theorem` contains a, possibly empty, set of markings (encoded as `BigInt`s).
Those markings are used to taint `Theorem`s that are valid only in a limited scope.

When the library creates a `Theorem` that is supposed to be valid only within a certain scope,
it taints it using the `mark` method. The method taints the `Theorem` object with a fresh mark.

Each time a `Theorem` depends on another `Theorem`, it is tainted by all the markings from the first `Theorem`.
This is done using the `from` method on `Theorem`. 

The method `unmark` can be used to remove some of the markings from a `Theorem`.

To showcase how markings are used, here is, in essence, how the `implI` method is implemented:
```scala
def implI(assumption: Expr)(conclusion: Theorem => Attempt[Theorem]): Attempt[Theorem] = {

  val (hypothesis, mark) = new Theorem(assumption).mark  // Here, we mark the `Theorem`.

  conclusion(hypothesis) map {
    // We create a new `Theorem` from the result, and indicate that it depends on `thm` using `from`.
    // We then remove the mark related to the `hypothesis`. The resulting `Theorem` does not depend on it. 
    (thm: Theorem) => new Theorem(Implies(assumption, thm.expression)).from(thm).unmark(mark)
  }
}
```

To verify that a `Theorem` is valid in the global scope, the `isGloballyValid` method should be used.
It checks that the `Theorem` is not tainted by any markings.
