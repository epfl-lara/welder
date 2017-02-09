
Welder Internals
================

In this file, we expose some of the implementation details of the library.
This documentation is intended for people wishing to contribute to the library.

Scoping Theorems 
================

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
def implI(assumption: Expr)(conclusion: Theorem => Attempt[Theorem]) = {

  // Here, we mark the `Theorem`.
  val (hypothesis, mark) = new Theorem(assumption).mark

  conclusion(hypothesis) map { (thm: Theorem) => 
    // We create a new `Theorem` for the implication,
    // and indicate that it depends on `thm` using `from`.
    // We then remove the mark related to the `hypothesis`.
    // The resulting `Theorem` does not depend on it. 
    new Theorem(Implies(assumption, thm.expression))
        .from(thm)
        .unmark(mark)
  }
}
```

To verify that a `Theorem` is valid in the global scope, the `isGloballyValid` method should be used.
It checks that the `Theorem` is not tainted by any markings.

Freezing Expression Functions
=============================

Some functions, such as `congruence`, `naturalInduction` or `structuralInduction` accept as argument function of the type `Expr => Expr`.
In each case, the goal is to allow users of the library to easily specify some sort of *context* or a property.

Take for instance the method `congruence`, which is used to derive the equality of two expressions within the *same context* given the equality of the two expressions. The context in this case is specified using a function of the type `Expr => Expr`.

If nothing is done, the use of the function type `Expr => Expr` is very problematic. Indeed, nothing would stop users from providing ill-behaved functions.

```scala
var i: BigInt = 0

// Returns a different IntegerLiteral each time it is called. 
def illBehaved(expr: Expr): Expr = {
  i += 1
  
  IntegerLiteral(i)
}

// Contains the theorem `true == true`.
val trueIsTrue = reflexivity(BooleanLiteral(true))

// Would return the theorem `1 == 2` if nothing was done.
congruence(trueIsTrue)(illBehaved)
```

To ensure that this does not happen, the library *freezes* all the parameter functions of those methods using the `freeze` function. The `freeze` function applies its argument, only once, to a fresh `Variable`. All calls to the frozen function are then resolved using variable substitution.

```scala
val frozen = freeze(BooleanType, illBehaved)

frozen(BooleanLiteral(true)) // Returns `IntegerLiteral(1)`.
frozen(BooleanLiteral(true)) // Also returns `IntegerLiteral(1)`.
```

When debugging is enabled, we also issue a warning when the frozen function returns a different value than the original function.
