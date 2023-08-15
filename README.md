# AddressC

AddressC is a frontend for [Iris's HeapLang](https://gitlab.mpi-sws.org/iris/iris)
with a focus on easily proving functional correctness for idiomatic, imperative algorithms.
It defines a syntactic layer around HeapLang to achieve an imperative-style syntax and provides primitives such as while-loops or structs
inspired by projects such as [MiniC](https://gitlab.mpi-sws.org/iris/c) and [Bedrock 2](https://github.com/mit-plv/bedrock2).
All primitives come with a high degree of automation thanks to [Diaframe](https://gitlab.mpi-sws.org/iris/diaframe). The AddressC language has been
used in particular to show correctness of various tree insertion 
algorithms (see our [techreport][fiptree-tr]).

[fiptree-tr]: https://www.microsoft.com/en-us/research/publication/a-functional-correspondence-between-top-down-and-bottom-up-tree-algorithms-fast-and-correct-fully-in-place-functions-with-first-class-constructor-contexts-and-zippers-tr/

AddressC is especially powerful for imperative algorithms which arise naturally from a functional version.
As an example, take the `reverse` function:

```koka
fun reverse( xs : list<a>, acc : list<a> ) : list<a>
  match xs
    Cons(x, xx) -> reverse( xx, Cons(x, acc) )
    Nil -> acc
```

This function reverses a list by appending the elements one-by-one onto an accumulator.
Since it is tail-recursive, any functional language will compile it to an imperative while-loop.
Additionally, a language with reuse analysis such as [Koka](https://koka-lang.github.io/koka/doc/index.html)
or [Lean](https://leanprover.github.io/) can optimize this further: Assuming that the input `xs` is unique,
this function can _reuse_ the cells of the old list `xs` for the accumulator.
In pseudo-code, Koka will emit code similar to the following:

```koka
fun reverse( xs : list<a>, acc : list<a> ) : list<a>
  match xs
    Cons(x, xx) ->
      let next = if is-unique(xs) then &xs else ...
      next[1] = acc
      goto reverse( xx, next )
    Nil ->
      return acc
```

We can formalize an imperative formulation of this function directly in AddressC:

```coq
Definition heap_reverse :=
  fun: ( curr ) {                  (* A function to reverse the list `curr` *)
    var: prev := NULL in           (* The accumulator starts out as empty *)
    while: (curr != NULL) {        (* Until we reach the end of the list: *)
      var: next := curr〚1〛 in     (* Store the tail of the list *)
      curr〚1〛 = prev;;            (* Set the tail to the accumulator *)
      prev = curr;;                (* The new cell is added to the accumulator *)
      curr = next                  (* Continue with the stored tail *)
    };;
    ret: prev                      (* Return the accumulator *)
  }.
```

As can be seen, AddressC is quite close to imperative syntax and should be understandable
by a typical imperative programmer. Yet, this definition yields a normal Iris HeapLang program
which can be proven correct within the usual Iris separation logic.
In Iris, we can write a specification as follows:

```coq
Lemma heap_reverse_correct (xsv : val) (xs : list Z) :
    {{{ is_list xs xsv }}}
    heap_reverse (ref xsv)
    {{{ v, RET v; is_list (reverse xs []) v }}}.
```

This asserts that if `heap_reverse` is given a reference to an Iris value `xsv`,
which corresponds to a Coq list `xs` and its evaluation terminates,
then it will return a value `v` which corresponds to the Coq list `reverse xs []`.
We can prove this claim as follows:

```coq
Proof.
  wp_begin "Hxs"; curr. wp_var prev.          (* Set up the program with variables curr and prev *)
  wp_while (∃ xs' acc' prevv currv,           (* This is the main loop invariant: *)
    curr ↦ currv ∗ is_list xs' currv          (* - curr points to an Iris list corresponding to xs' *)
    ∗ prev ↦ prevv ∗ is_list acc' prevv       (* - prev points to an Iris list corresponding to acc' *)
    ∗ ⌜reverse xs [] = reverse xs' acc'⌝)%I.  (* - and xs', acc' correspond to one iteration of the functional program *)
  - iModIntro. iIntros "[%xs' [% [% [% [? [Hxs [? [? ->]]]]]]]]".
    destruct xs'; iDecompose "Hxs".           (* Split the current list as in the `match` statement *)
     { wp_type. }                             (* If the list is empty, the loop finishes and we are done *)
     { wp_heap.                               (* Otherwise, we evaluate `curr != NULL` *)
       wp_enter_loop.                         (* curr is not null and we enter the loop *)
       wp_heap.                               (* We complete the assignments of the main loop body *)
       wp_type. }                             (* We show that the loop invariant is maintained *)
  - wp_type.                                  (* We show that the loop invarint is true at the start. *)
Qed.
```

This repository contains several formalizations in AddressC including advanced ones
such as move-to-root trees, splay trees and zip trees. In these cases, it is even possible
to obtain AddressC code which corresponds closely to the pseudo-code presented in the
original papers. To learn more about this work,
please refer [to our paper][fiptree-tr]:
```
@TechReport{Lorenzen:correspondence,
  author = {Lorenzen, Anton and Leijen, Daan and Swierstra, Wouter and Lindley, Sam},
  title = {A Functional Correspondence between Top-down and Bottom-up Tree Algorithms},
  year = 2023,
  month = Jul,
  institution = {Microsoft Research},
  number = {MSR-TR-2023-28}
}
```

## Prerequisites

The Coq code is known to compile with:

```
coq                         8.17.0                     The Coq Proof Assistant
coq-core                    8.17.0                     The Coq Proof Assistant -- Core Binaries and Tools
coq-diaframe                dev.2023-06-15.0.1c3b5549  Diaframe: Automation for Iris
coq-diaframe-heap-lang      dev.2023-06-15.0.1c3b5549  Diaframe: Automation for Iris's Heap Lang
coq-equations               1.3+8.17                   A function definition package for Coq
coq-iris                    dev.2023-06-14.0.f0e415b6  A Higher-Order Concurrent Separation Logic Framework with support for interactive proofs
coq-iris-heap-lang          dev.2023-06-14.0.f0e415b6  The canonical example language for Iris
coq-stdlib                  8.17.0                     The Coq Proof Assistant -- Standard Library
coq-stdpp                   dev.2023-06-01.0.d1254759  An extended "Standard Library" for Coq
```

## Compilation

The Coq code can be compiled using:
```
make -jN
```
Where N is the number of cores to be used.

