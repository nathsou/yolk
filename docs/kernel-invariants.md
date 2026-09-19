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
parameter is zero or positive. In a positive case, write the parameter as a new
independent nonnegative variable plus one. Every parameter is split exactly
once, so the procedure terminates.

In each case, every expression is either identically zero or always positive.
Consequently `imax(a, b)` becomes zero when `b` is zero and `max(a, b)` otherwise.
The resulting expression is a maximum of constants and variables plus offsets.
A constant on the left must be bounded by a right-hand atom's minimum value.
A variable-plus-offset on the left must be bounded by an atom with the same
variable and a sufficient offset on the right. This is necessary because that
variable can grow without bound while all other variables remain zero; it is
sufficient by pointwise comparison of the atoms.

This implementation favors an explicit finite algorithm over rewrite heuristics.
Its worst-case cost is exponential in the number of distinct universe parameters.
The independent numeric oracle in `universe.test.mbt` is regression coverage,
not a formal proof of the implementation.

## Inductive declarations

`Context.add_decl` validates an inductive, its constructors, and its recursor in
a staged environment, committing them together only after all checks succeed.
Standalone constructors and manually supplied recursors are rejected. Global
types and bodies must be closed and may use only declared universe parameters.
Constructor parameter binders are derived from the checked inductive telescope.

The arity must be well typed and end in a sort. Its result universe must be
identically `Prop` or provably positive at every universe instantiation. Ambiguous
levels such as bare `Sort u` are rejected. Propositions have small elimination;
empty/singleton large-elimination exceptions are not currently implemented.

Positivity checking reduces field types before inspecting their shape. Recursive
occurrences may be direct applications of the declared inductive, or occur under
function codomains whose domains do not contain the inductive. Recursive
applications must preserve universe instances and parameters, and must not contain
recursive occurrences in indices. Nested inductives are not supported.

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

Before publication, each generated recursor signature is checked to inhabit a
sort. Each constructor reduction is also checked for type preservation with
fresh neutral parameters, motive, handlers, and fields. These checks supplement
the structural positivity and universe restrictions; they do not replace them.

## Annotations

An annotated let retains `Ann(value, type)` in its core term. Expected types used
while elaborating are hints, so discarding the annotation would otherwise allow
it to escape kernel validation.
