Inox String Interpolation
=========================

## Primitives

### Strings

#### Literal Syntax

```
''
'hello world'
'hey!'
```

#### Functions

| Function | Type | Description | Inox Constructor |
| -------- | ---- | ----------- | ---------------- |
| `length`   | `String => BigInt` | Returns the length of the string. | `StringLength` |
| `concatenate` | `(String, String) => String` | Returns the concatenation of the two strings. | `StringConcat` |
| `substring` | `(String, BigInt, BigInt) => String` | Returns the substring from the first index inclusive to the second index exclusive. | `SubString ` |

#### Operators

| Operator | Type | Associativity | Precedence | Description | Inox Constructor |
| -------- | ---- | ------------- | ---------- | ----------- | ---------------- |
| `++` | `(String, String) => String` | Left-associative | ??? | Returns the concatenation of the two strings. | `StringConcat` |

### Sets

#### Constructor

| Constructor | Description | Inox Constructor |
| ----------- | ----------- | ---------------- |
| `Set[A](elements: A*)` | Returns a set containing the given `elements`. | `FiniteSet` |

#### Literal Syntax

```
{}
{1, 2, 3}
{'foo', 'bar', 'baz'}
```

#### Functions

| Function | Type | Description | Inox Constructor |
| -------- | ---- | ----------- | ---------------- |
| `contains[A]` | `(Set[A], A) => Boolean` | Returns `true` if the given set contains the given element, `false` otherwise. | `ElementOfSet` |
| `add[A]` | `(Set[A], A) => Set[A]` | Returns the set with an element added. | `SetAdd` |
| `subset[A]` | `(Set[A], Set[A]) => Boolean` | Returns `true` if the first set is a subset of the second, `false` otherwise. | `SubsetOf` |
| `union[A]` | `(Set[A], Set[A]) => Set[A]` | Returns the unions of the two sets. | `SetUnion` |
| `intersection[A]` | `(Set[A], Set[A]) => Set[A]` | Returns the intersection of the two sets. | `SetIntersection` |
| `difference[A]` | `(Set[A], Set[A]) => Set[A]` | Returns the elements of the first set minus the elements of the second set. | `SetDifference` |

#### Operators

| Operator | Type | Associativity | Precedence | Description | Inox Constructor |
| -------- | ---- | ------------- | ---------- | ----------- | ---------------- |
| `∈` | `(A, Set[A]) => Boolean` | Left-associative | ??? | Returns `true` if the element is part of the set, `false` otherwise. | `ElementOfSet` |
| `⊆` | `(Set[A], Set[A]) => Boolean` | Left-associative | ??? | Returns `true` if the first set is a subset of the second, `false` otherwise. | `SubsetOf` | |
| `∪` | `(A, Set[A]) => Boolean` | Left-associative | ??? | Returns the unions of the two sets. | `SetUnion` |
| `∩` | `(A, Set[A]) => Boolean` | Left-associative | ??? | Returns the intersection of the two sets. | `SetIntersection` |
| `∖` | `(A, Set[A]) => Boolean` | Left-associative | ??? | Returns the elements of the first set minus the elements of the second set. | `SetDifference` |

### Bags

#### Constructor

| Constructor | Description | Inox Constructor |
| ----------- | ----------- | ---------------- |
| `Bag[A](bindings: (A -> BigInt)*)` | Returns a bag containing the given `bindings`. | `FiniteBag` |

#### Literal Syntax

```
{1 -> 2, 2 -> 4, 3 -> 6}
{'foo' -> 5, 'bar' -> 2, 'baz' -> 2}
```

#### Functions

| Function | Type | Description | Inox Constructor |
| -------- | ---- | ----------- | ---------------- |
| `multiplicity[A]` | `(Bag[A], A) => BigInt` | Returns the number of occurences in the given bag of the given value. | `MultiplicityInBag` |
| `bagAdd[A]` | `(Bag[A], A) => Bag[A]` | Returns the bag with an element added. | `BagAdd` |
| `bagUnion[A]` | `(Bag[A], Bag[A]) => Bag[A]` | Returns the unions of the two bags. | `BagUnion` |
| `bagIntersection[A]` | `(Bag[A], Bag[A]) => Bag[A]` | Returns the intersection of the two bags. | `BagIntersection` |
| `bagDifference[A]` | `(Bag[A], Bag[A]) => Bag[A]` | Returns the elements of the first bag minus the elements of the second bag. | `BagDifference` |

### Maps

#### Constructor

| Constructor | Description | Inox Constructor |
| ----------- | ----------- | ---------------- |
| `Map[A](default: A, bindings: (A -> BigInt)*)` | Returns a map with default value `default` containing the given `bindings`. | `FiniteMap` |

#### Literal syntax

```
{*: Int -> 42}
{* -> '???', 'hello' -> 'HELLO', 'world' -> 'WORLD'}
```

#### Functions

| Function | Type | Description | Inox Constructor |
| -------- | ---- | ----------- | ---------------- |
| `apply[K, V]` | `(Map[K, V], K) => V` | Returns the value associated to the given key. | `MapApply` |
| `updated[K, V]` | `(Map[K, V], K, V) => Map[K, V]` | Returns the map with a bidding from the key to the value added. | `MapUpdated` |
