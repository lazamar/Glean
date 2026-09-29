---
id: recursion
title: Recursion
sidebar_label: Recursion
---

import {OssOnly, FbInternalOnly} from 'internaldocs-fb-helpers';

Recursion comes up in two ways in a schema: predicates whose *types*
refer to each other, and derived predicates whose *derivations* refer
to themselves.

## Recursive types

Predicates can be (mutually) recursive. In other words, **we can use
predicates to define recursive types**. You can define linked lists,
trees and DAGs using predicates. However, the **facts cannot form a
cycle**: we cannot have a circular list, or a cyclic graph in the
data.


The restriction on cyclic data is enforced when facts are added to a
database: each new fact added to the database can only refer to
earlier facts via its key. This is because facts are added to the
database in batches, removing duplicates and substituting references
to duplicated facts at the same time. Allowing recursion between the
keys would make this process significantly harder.


Facts can be recursive in their *values*, but not their *keys*. A
mutually recursive set of facts must be added to the database in a
single batch, however.

To summarise, recursion is

* allowed between *predicates*
* not allowed between *keys*
* allowed between *values*

## Recursive derived predicates

A [derived predicate](../derived.md) can be defined in terms of
itself, directly or through other derived predicates. For example,
using the schema from the [Angle Guide](../angle/guide.md), the
ancestors of a class are its parent and its parent's ancestors:

```lang=angle
predicate Ancestor : { child : Class, ancestor : Class }
  { C, A } where
    Parent { C, A } |
    (Ancestor { C, P }; Parent { P, A })
```

Queries use it like any other predicate:

```
facts> A where example.Ancestor { child = { name = "Goldfish" }, ancestor = A }
{ "id": 1026, "key": { "name": "Fish", "line": 30 } }
{ "id": 1024, "key": { "name": "Pet", "line": 10 } }
```

* Glean only derives the facts that the query needs. Here it follows
  the parents of `Goldfish`, rather than computing the ancestors of
  every class.
* Results are returned as they're derived. A query that only needs
  some of them stops early: for example, a negation or the condition
  of an `if` stops at the first result.
* The data can have cycles. Each fact is derived once, so the
  derivation finishes even when following the relation would go round
  in circles.
* Predicates can be mutually recursive, and a recursive predicate can
  use other derived predicates, recursive or not.
* Within a query, once a call to a recursive predicate has finished,
  later calls with the same arguments reuse its results.

A query can also declare its own recursive predicates, without changing
the schema: see [Predicates declared in a query](../derived.md#predicates-declared-in-a-query).

### No recursion through negation

A derived predicate can't depend on its own negation, directly or
through other predicates. Negating a predicate, using it in the
condition of an `if`, or using it inside `all` count as negating it.
For example, these two predicates have no single meaning: a class with
a parent could be in either one, and nothing says which.

```lang=angle
predicate Root : Class
  C where C = Class _; !NonRoot C

predicate NonRoot : Class
  C where Parent { C, _ }; !Root C
```

A schema like this is rejected when it's loaded:

```
recursion through negation is not allowed. These predicates depend on their own negation:
  example.NonRoot.1 -> !example.Root.1 -> example.NonRoot.1
  example.Root.1 -> !example.NonRoot.1 -> example.Root.1
(!P means that P is negated, used in the condition of an if, or used inside all)
```

Negating a recursive predicate is fine when it's not part of the same
cycle, e.g. `!example.Ancestor { C, A }` in another predicate or in a
query.

### Stored predicates can't involve recursion

A `stored` derived predicate can't be recursive, and can't depend on a
recursive predicate, for now. A schema that has one is rejected when
it's loaded:

```
recursion is not supported in stored predicates yet:
  example.StoredAncestor.1 depends on the recursive predicate example.Ancestor.1
```

There are two reasons:

* A stored predicate can only be derived once the stored predicates it
  depends on are complete, and a recursive one depends on itself.
* A recursive derivation works from facts that it derived earlier in
  the same query, and those don't carry the ownership information that
  incremental databases need to decide which derived facts to keep.

Recursive predicates that aren't stored are derived when they're
queried, so neither applies to them.

### Limits and continuations

A query that uses recursive predicates can't be continued. When it
reaches one of its limits (on the number of results, bytes or time),
it returns the results it has found so far, with a diagnostic saying
that there may be more. Resuming it fails: in the shell, `:more` does.
To get more results, raise the limit, e.g. with `:limit` in the shell.

### Termination

A recursive derivation finishes when it runs out of new facts. It
always does if the facts it derives only combine values that already
exist, in the database or in the query. A derivation that makes a new
value at each step, such as a counter, can go on forever on cyclic
data. Glean doesn't detect this: the query runs until it reaches its
time limit.

Bound such a derivation with an argument that the query provides. For
example, the ancestors of a class up to a maximum depth `max`:

```lang=angle
predicate AncestorWithin :
  { child : Class, max : nat, ancestor : Class, depth : nat }
  { C, Max, A, D } where
    (Parent { C, A }; D = 1) |
    (AncestorWithin { C, Max, P, D0 }; D0 < Max; Parent { P, A }; D = D0 + 1)
```

A query must provide `max`, e.g.
`example.AncestorWithin { child = { name = "Goldfish" }, max = 2 }`.
