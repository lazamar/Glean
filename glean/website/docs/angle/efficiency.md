---
id: efficiency
title: Query Efficiency
sidebar_label: Query Efficiency
---

import {OssOnly, FbInternalOnly} from 'internaldocs-fb-helpers';

There are two important aspects of a query that affect its efficiency;

1. Which fields are specified in a pattern
2. The ordering of statements

We’ll cover each of these in the following sections. For recursive predicates, how the recursion is written matters too: see [Recursive predicates](#recursive-predicates).

## Efficient matching of facts

The order of fields in the schema matters a lot for efficiency. Glean indexes facts by a prefix of their keys, so if we know the prefix when searching for facts this will be a lot faster. Often this difference is absolutely crucial; the difference is between *O(log n)* and *O(n)*, so when the database is large this can be many orders of magnitude.

For example, the `example.Parent` predicate we saw [earlier](./guide.md#matching-nested-facts) is defined as

```lang=angle
predicate Parent :
  {
    child : Person,
    parent : Person,
  }
```

We should think of this as a mapping from `child` to `parent`. Glean won’t stop you writing a query for `{ parent = ... }`, but such a query will examine all of the `example.Parent` facts in the database. We can see how many facts are searched for our query using `:profile full` in the shell (see [debugging](debugging.md) for more details):

```
facts> :profile full
facts> example.Parent { parent = { name = "Pet" }}
(snip)
2 results, 2 facts, 0.40ms, 159440 bytes, 988 compiled bytes
Facts searched:
                        example.Parent.1 : 3
```

This tells us that although it found the 2 results we expected, it searched all 3 `example.Parent` facts in the process.

## Making queries efficient using a derived predicate

What if we wanted to efficiently map from `parent` to `child`? That’s easy to accomplish using a *derived predicate*. We’re going to define a new predicate with a different field ordering, and automatically generate the facts of our new predicate by deriving them from the facts of the existing predicate.  For full details see [Derived Predicates](../derived.md), what follows will be a walkthrough showing how to use a derived predicate to make our queries more efficient.

First we’ll define our derived predicate in the schema, like this:

```lang=angle
predicate Child :
  {
    parent : Class,
    child : Class,
  }
  stored
  { P, C } where Parent { C, P }
```

We can try this out in the shell. First we have to create a new database to hold the derived facts that is *stacked* on top of the old database. Drop out of the shell and run this command to create the new database:

```lang=angle
glean create --db-root /tmp/glean/db --schema dir:/tmp/glean/schema --db derived/1 --stacked facts/1
```

Now start the shell again and load the stacked database. Note that we can still query facts from the original database:

```lang=angle
> :db derived/1
derived> example.Parent _
{ "id": 1028, "key": { "child": { "id": 1025 }, "parent": { "id": 1024 } } }
{ "id": 1029, "key": { "child": { "id": 1026 }, "parent": { "id": 1024 } } }
{ "id": 1030, "key": { "child": { "id": 1027 }, "parent": { "id": 1026 } } }
```

Initially we have no facts of the `Child` predicate:

```lang=angle
derived> example.Child _
0 results, 0 facts, 0.91ms, 812952 bytes, 664 compiled bytes
```

But we can create them automatically:

```lang=angle
derived> * example.Child _
{ "id": 1037, "key": { "parent": { "id": 1024 }, "child": { "id": 1025 } } }
{ "id": 1038, "key": { "parent": { "id": 1024 }, "child": { "id": 1026 } } }
{ "id": 1039, "key": { "parent": { "id": 1026 }, "child": { "id": 1027 } } }
```

(the `*` means “derive and store” the facts produced by the query. To derive facts for a production database you would use either `glean derive` from the command line, or the appropriate Thrift API in whatever language you’re using to talk to the Glean server).

Now we have 3 facts of our derived predicate:

```lang=angle
derived> :stat
example.Child.1
  count: 3
  size:  87 (87 bytes) 100.0000%
```

And finally we can make efficient queries to find a parent’s children:

```lang=angle
derived> example.Child { parent = { name = "Pet" }}
{ "id": 1037, "key": { "parent": { "id": 1024 }, "child": { "id": 1025 } } }
{ "id": 1038, "key": { "parent": { "id": 1024 }, "child": { "id": 1026 } } }

2 results, 2 facts, 0.41ms, 160992 bytes, 1013 compiled bytes
Facts searched:
                         example.Child.1 : 2
                         example.Class.1 : 1
```

We found the correct 2 results, and only searched 2 `example.Child` facts.

This idea of adding extra indices to your database using derived predicates is common practice when working with Glean data, so it’s worthwhile getting familiar with it.

## The order of statements is important

Suppose we want to find the grandparent of the `Goldfish` class using our example schema. We would probably write it like this:

```lang=angle
Q where
    example.Parent { child = { name = "Goldfish" }, parent = P };
    example.Parent { child = P, parent = Q }
```

Generally speaking the statements are matched top-to-bottom. For each of the facts that match the first statement, bind the variables in the pattern and then proceed with the second statement, and so on.

As written, this query works by *first* finding the parent of `Goldfish` and *then* finding its parent, which is exactly what we want. This query will be efficient, because both stages are matching on the first field of the `example.Parent` predicate.

If instead we swapped the order of the statements:

```lang=angle
Q where
    example.Parent { child = P, parent = Q };
    example.Parent { child = { name = "Goldfish" }, parent = P }
```

The query still works, and means exactly the same thing, but it’s much less efficient. This query works as follows:

* for each `example.Parent` fact, call the child `P` and the parent `Q`
* search for an `example.Parent` fact with child `{ name = "Goldfish" }` and parent `P`
* if it exists, then `Q` is a result

This is going to involve searching all of the `example.Parent` facts, instead of just the ones for the parent of `Goldfish`.

The general rule of thumb is to do the more specific searches first. The search for `example.Parent { child = { name = "Goldfish" }, parent = P }` is efficient because we know the `child`, this binds he value of `P` which makes the search for `example.Parent { child = P, parent = Q }` also fast.

## Recursive predicates

The same rules apply to [recursive predicates](../schema/recursion.md#recursive-derived-predicates), plus one more: the recursive call should know the same arguments as the query. There are two natural ways to write the ancestors of a class:

```lang=angle
# The recursive call comes first ("left-linear")
predicate Ancestor : { child : Class, ancestor : Class }
  { C, A } where
    Parent { C, A } |
    (Ancestor { C, P }; Parent { P, A })

# The recursive call comes last ("right-linear")
predicate AncestorR : { child : Class, ancestor : Class }
  { C, A } where
    Parent { C, A } |
    (Parent { C, P }; AncestorR { P, A })
```

They mean the same thing, but for a query that knows the child, like `example.Ancestor { child = { name = "Goldfish" } }`, the first is much more efficient:

* In `Ancestor`, the recursive call `Ancestor { C, P }` has the same child as the query. Glean finds the ancestors of `Goldfish` one generation at a time, and each step searches `Parent` by its first field. The work is proportional to the number of ancestors.
* In `AncestorR`, the recursive call `AncestorR { P, A }` has a different child at each step: the parent of `Goldfish`, then its grandparent, and so on. Glean finds all the ancestors of each of them separately, so the work grows with the square of the number of ancestors.

On a database indexing all of Stackage, finding the 1,031 modules that a module uses, directly or not, took 14 ms with the first shape and 226 ms with the second. The gap grows with the number of results. `:profile full` in the shell shows how many facts each recursive predicate derived (see [debugging](debugging.md#debugging-a-slow-query)), which makes the difference easy to see.

### Searching in the other direction

For the descendants of a class, the query knows the `ancestor` instead, and neither definition is efficient:

* In `Ancestor`, the recursive call `Ancestor { C, P }` knows nothing, so Glean derives the ancestors of every class before keeping the ones it needs.
* In `AncestorR`, each step needs the children of a class, which means searching `Parent` by its second field: a search of all the `Parent` facts, at every step.

The answer is the one from [the previous section](#making-queries-efficient-using-a-derived-predicate): the stored `Child` predicate, which has the fields in the other order, and a left-linear definition over it with the ancestor first:

```lang=angle
predicate Descendant : { ancestor : Class, descendant : Class }
  { A, D } where
    Child { A, D } |
    (Descendant { A, P }; Child { P, D })
```

Now `example.Descendant { ancestor = { name = "Pet" } }` finds the descendants of `Pet` one generation at a time, and each step searches `Child` by its first field. On the Stackage database, finding the 21,616 modules that use a module, directly or not, took 56 s with the left-linear definition over the original relation, 1.6 s with the right-linear one, and 0.14 s with the left-linear definition over a stored copy with the fields swapped.

### Summary

To write an efficient recursive predicate:

* Put the arguments that queries will know first.
* Put the recursive call first ("left-linear"), so that it knows the same arguments as the query.
* Make sure each step searches a stored predicate by a prefix of its key. For the other direction, that usually means a stored derived predicate with the fields swapped, like `Child`.
* If queries need both directions, define a predicate for each.

Some other things to know:

* A query that only needs some of the results, such as a negation or the condition of an `if`, stops as soon as it has them.
* Within one query, later calls with the same arguments reuse the results of a finished call. A right-linear definition also leaves behind the results of every intermediate call, which later calls can reuse. So in a query that calls it for many related values, the right-linear shape can occasionally come out ahead, even though each call on its own costs more. Measure before relying on it.
* * *
