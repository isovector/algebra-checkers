# algebra-checkers

[![Build Status](https://travis-ci.org/isovector/algebra-checkers.svg?branch=master)](https://travis-ci.org/isovector/algebra-checkers)

## Dedication

> "Any fool can make a rule, and any fool will mind it."
>
> Henry David Thoreau


## Overview

`algebra-checkers` is a little library for testing algebraic laws. For example,
imagine we're writing an ADT:

```haskell
data Foo a
instance Semigroup (Foo a)
instance Monoid (Foo a)

data Key


get :: Key -> Foo a -> a
get = undefined

set :: Key -> a -> Foo a -> Foo a
set = undefined
```

Let's say we expect the lens laws to hold for `get` and `set`, as well for `set`
to be a monoid homomorphism. We can express those facts to `algebra-checkers`
and have it generate tests for us:

```haskell
lawTests :: [Property]
lawTests = $(lawConf'
  [e| do
  law "set/set"
      (set i x' (set i x s) == set i x' s)
  law "set/get"
      (set i (get i s) s == s)
  law "get/set"
      (get i (set i x s) == x)
  homo @Monoid
      (\s -> set i x s)
  |])
```

Furthermore, `algebra-checkers` will generate tests to show that these laws are
confluent. We can run these tests via `quickCheck lawTests`.

If we use the `theoremsOf'` function instead of `lawConf'`,
`algebra-checkers` will dump out all the additional theorems it has proven about
our algebra. This serves as a good sanity check:

```
Theorems:

• set i x' (set i x s) == set i x' s (definition of "set/set")
• set i (get i s) s == s (definition of "set/get")
• get i (set i x s) == x (definition of "get/set")
• set i x mempty == mempty (definition of "set:Monoid:mempty")
• set i x (s1 <> s2) == set i x s1 <> set i x s2
    (definition of "set:Monoid:<>")
• set i1 (get i1 s2) s1 == set i1 x1 s1
    (implied by "set/get" and "set/set")
• set i1 (get i1 s1) s12 <> set i1 (get i1 s1) s22 == s12 <> s22
    (implied by "set:Monoid:<>" and "set/get")
• get i1 mempty == x1 (implied by "get/set" and "set:Monoid:mempty")
• set i1 x'2 (set i1 x1 s11 <> set i1 x1 s21)
  == set i1 x'2 (s11 <> s21)
    (implied by "set:Monoid:<>" and "set/set")
• get i1 (set i1 x1 s11 <> set i1 x1 s21) == x1
    (implied by "get/set" and "set:Monoid:<>")
```

Uh oh! Look at that!

```
• get i1 mempty == x1 (implied by "get/set" and "set mempty")
```

This is clearly a bogus theorem, which lets us know that "get/set" and "set
mempty" are nonconfluent with one another!

