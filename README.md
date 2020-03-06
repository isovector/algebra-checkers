# algebra-checkers

## Dedication

> "Any fool can make a rule, and any fool will mind it."
>
> Henry David Thoreau


## Overview

`algebra-checkers` is a little library for testing algebraic laws. For example,
imagine we're writing an ADT:

```haskell
data Foo a

empty :: Foo a
insert :: a -> Foo a -> Foo a
size :: Foo a -> Int
```

and would like to enforce the law of commutativity:

```haskell
law insert a (insert b foo) = insert b (insert a foo)
```

We can test this very naturally via:

```haskell
law_commutative :: (Eq a, EqProp a, Show a, Typeable a) => Law a
law_commutative = $(law [|
  insert a (insert b foo) == insert b (insert a foo)
  |]


main = quickCheck $ checkLaw (law_commutative @Int)
-- +++ OK, passed 100 tests.
```

(note the double equals in the law's definition)

`algebra-checkers` can also prove that a set of laws are confluent. Let's add
another law, attempting to enforce that `Foo` can only hold four elements:

```haskell
law_max4 :: (Eq a, EqProp a, Show a, Typeable a) => Law a
law_max4 = $(law [|
  insert a (insert b (insert c (insert d (insert e empty))))
    == insert b (insert c (insert d (insert e empty)))
  |]
```

Clearly `law_commutative` and `law_max4` are nonconfluent. `algebra-checkers`
can show us this:

```haskell
main = quickCheck $ confluent (law_commutative @Int) law_max4
-- *** Failed! Falsified (after 4 tests):
-- insert (-2) (insert (-1) (insert (5) (insert (-1) (insert (-1) empty)))) /= insert (-1) (insert (5)
--  (insert (-1) (insert (-1) empty)))
-- insert (-1) (insert (-2) ([5])) == insert (-2) (insert (-1) ([5]))
-- insert (-1) (insert (5) (insert (-1) (insert (-1) empty))) /= insert (-2) (insert (-1) ([5]))
```

