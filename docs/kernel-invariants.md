# Kernel invariants

The kernel checks global declarations independently of the surface elaborator.
The regression tests in `soundness.test.mbt` include three previously accepted
axiom-free proofs of `False`; each must fail with a kernel type error.

## Binding representation

`Pi(Some(name), domain, body)` introduces a de Bruijn binder.
`Pi(None, domain, body)` is a nonbinding arrow: indices in its body retain their
meaning in the enclosing context. Names may be ignored in alpha-equivalence,
but these two cases may not. Definitional equality opens only actual binders;
`instantiate_pi` centralizes that distinction. Normalization removes unused
named binders after opening their bodies into free variables.

`instantiate` operates on locally closed replacements: enclosing binders must
be opened before substitution. It is not a general capture-avoiding substitution
operation on arbitrary terms with loose de Bruijn indices.

## Universe comparison

`u.leq(v, n)` means that `u <= v + n` for every assignment of natural numbers to
universe parameters. The solver partitions those assignments by whether each
parameter that can decide an `imax` is zero or positive: the parameters of every
second argument `b` of an `imax(a, b)`, unless `b` is syntactically positive
(a successor, or a `max`/`imax` with such a part). In a positive case, write the
parameter as a new independent nonnegative variable plus one. Other parameters
only ever contribute to maxima, so they remain unconstrained nonnegative
variables. Every split parameter is split exactly once, so the procedure
terminates.

In each case, every `imax` second argument is either identically zero or always
positive, since it is syntactically positive or mentions only split parameters.
Consequently `imax(a, b)` becomes zero when `b` is zero and `max(a, b)` otherwise.
The resulting expression is a maximum of constants and variables plus offsets.
A constant on the left must be bounded by a right-hand atom's minimum value.
A variable-plus-offset on the left must be bounded by an atom with the same
variable and a sufficient offset on the right. This is necessary because that
variable can grow without bound while all other variables remain zero; it is
sufficient by pointwise comparison of the atoms.

This implementation favors an explicit finite algorithm over rewrite heuristics.
Its worst-case cost is exponential in the number of distinct parameters that
decide an `imax`; comparisons of plain maxima split nothing. The independent
numeric oracles in `universe.test.mbt`, including a randomized one over three
parameters, are regression coverage, not a formal proof of the implementation.

## Inductive declarations

`Context.add_decl` validates an inductive, its constructors, and its recursor in
a staged environment, committing them together only after all checks succeed.
Standalone constructors and manually supplied recursors are rejected. Global
types and bodies must be closed and may use only declared universe parameters.
Constructor parameter binders are derived from the checked inductive telescope.
As in Lean, every constructor is checked with only the inductive type in scope:
constructors are added once all of them have been checked, so a constructor's
type may not mention a sibling constructor.

The arity must be well typed and end in a sort. Its result universe must be
identically `Prop` or provably positive at every universe instantiation. Ambiguous
levels such as bare `Sort u` are rejected. Propositions have small elimination;
empty/singleton large-elimination exceptions are not currently implemented.

Positivity checking reduces field types before inspecting their shape. A Pi
domain must not mention the inductive. No earlier declaration can refer to the
inductive being declared, so reduction never introduces an occurrence; only a
domain that mentions it syntactically is normalized, to see whether the
occurrence reduces away. Recursive
occurrences may be direct applications of the declared inductive, or occur under
function codomains whose domains do not contain the inductive. Recursive
applications must preserve universe instances and parameters, and must not contain
recursive occurrences in indices. The inductive may not occur in the indices
of a constructor's result type either. Nested inductives are not supported.

Indices are checked by walking and instantiating the arity in declaration order;
later index domains may depend on earlier indices.

## Recursors and reduction

A field `f : forall x : A, I indices(x)` contributes the pointwise hypothesis
`forall x : A, motive indices(x) (f x)`. The same operation applies to telescopes
with multiple dependent arguments. Reduction reconstructs that telescope from
the constructor field type and supplies a lambda making the corresponding
recursive calls. Field indices in `RecRule` identify these recursive fields;
their telescope is recovered from the constructor type rather than duplicated
in the rule metadata. Constructor universes are instantiated before this step.

Iota reduction fires only when the major premise reduces to a constructor
applied to exactly its parameters and fields. Anything else, such as a partially
applied constructor in a term that has not been checked yet, stays stuck.

Before publication, each generated recursor signature is checked to inhabit a
sort. Each constructor reduction is also checked for type preservation with
fresh neutral parameters, motive, handlers, and fields. These checks supplement
the structural positivity and universe restrictions; they do not replace them.

## Definitional equality

Eta compares a lambda with a term `e` only when the type of `e` reduces to a
product `forall x : A, B`; it then compares the lambda with `fun x : A => e x`
by lambda congruence, so the binder domains are compared too. A lambda is never
equal to a non-function, and the comparison returns `false` instead of failing
to infer the type of `e x`.

## Annotations

An annotated let retains `Ann(value, type)` in its core term. Expected types used
while elaborating are hints, so discarding the annotation would otherwise allow
it to escape kernel validation.

The elaborator reduces expected types, and the kernel only guarantees that
reduction terminates on well-typed terms. Declaration types, type ascriptions,
let and lambda annotations, and match motives are therefore checked by the
kernel before elaboration relies on them, whenever they are locally closed. An
annotation that mentions a variable bound by an enclosing, unopened binder is
checked with its declaration instead.

## Reduction under binders

`whnf` and `instantiate` assume locally closed terms. When inferring a Pi, the
sort of its body is reduced while the binder is still opened as a free variable;
closing first would leave a loose index that substitution could capture.
