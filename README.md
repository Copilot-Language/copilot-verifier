# Copilot Verifier

This "Copilot Verifier" is an add-on to the
[Copilot Stream DSL](https://copilot-language.github.io)
for verifying the correctness of C code generated
by the `copilot-c99` package.

The main idea of the verifier is to use the
[Crucible symbolic simulator](https://github.com/galoisinc/crucible)
to interpret the semantics of the generated C program and
and to produce verification conditions sufficient to guarantee
that the meaning of the generated program corresponds in a precise
way to the meaning of the original stream specification. The generated
verification conditions are then dispatched to SMT solvers to
be automatically solved.  We will have more to say about exactly
what is meant by this correspondence below.

## Using the Copilot Verifier

The main interface to the verifier is the `Copilot.Verifier.verify`
function, which takes some options to drive the code generation
process and a Copilot `Spec` object. It will invoke the Copilot
code generator to obtain C sources, compile the C sources into
LLVM bitcode using the `clang` compiler front-end, then
parse and interpret the bitcode using `crucible`.  After generating
verification conditions, it will dispatch them to an SMT solver,
and the result of those queries will be presented to the user.

There are a number of examples (based on similar examples
from the main Copilot repository) demonstrating how to
incorporate the verifier into a Copilot program.
See the `copilot-verifier/examples` subdirectory of this repository.

## Details of the Verification

### Synopsis of Copilot semantics

The Copilot DSL represents a certain nicely-behaved
class of discrete-time stream programs. Each `Stream`
in Copilot denotes an infinite stream of values; one may
just as well think that `Stream a` represents a pure mathematical
function `ℕ → a` from natural numbers to values of type `a`.
See the
[Copilot manual]
(https://ntrs.nasa.gov/api/citations/20200003164/downloads/20200003164.pdf)
for more details of the Copilot language itself and its semantics.

One of the central design considerations for Copilot is that is should
be possible to implement stream programs using a fixed, finite amount
of storage.  As a result, Copilot will only accept stream programs
that access a bounded amount of their input streams (including any
recursive stream references). This allows an
implementation strategy where the generated C code can use fixed-size
ring buffers to store a limited number of previous stream values.

The execution model for the generated programs is that the program
starts in a state corresponding to stream values at time `t = 0`;
"external" stream input values are placed in distinguished global
variables by the calling environment, which then executes a `step()`
function to move to the next time step.  The `step()` function captures
the values of these external inputs and does whatever computation is
necessary to update its internal state from time `t=n` to time
`t=n+1`.  In addition, it will call any defined "trigger" functions
if the stream state at that time step satisfies the defined guard condition.
In short, the generated C program steps one moment at a time through
the stream program, consuming a sequence of input values provided by
a cooperating environment and calling handler functions whenever
states of interest occur.

### The Desired Correspondence

What does it mean, then, for a generated C program in this style
to correctly implement a given stream program? The intuition
is basically that after `n` calls to the `step` function,
the state of the ring-buffers of the C program should correctly
compute the value of the corresponding stream expression 
evaluated at index `n`, assuming the C program has been fed
inputs corresponding to the first `n` values of the external stream
inputs.  Moreover, the trigger functions should be called from
the `step` function exactly at time values when the stream expressions
evaluate to true.

The notion of correspondence for the values flowing in streams is
relatively straightforward: these values consist of fixed-width
machine integers, floating-point values, structs and fixed-length
arrays. For each, the appropriate notion of equality is fairly clear.

Both the original Stream program and the generated C program
can be viewed straightforwardly as a transition system, and under
this view, the correspondence we want to establish is a bisimulation
between the states of the high-level stream program and the low-level
C program. The proof method for bisimulation requires us to provide
a "correspondence" relation between the program states, and then prove
three things about this relation:

1. that the initial states of thee programs are in the relation;
2. if we assume two arbitrary program states begin in the relation
and each takes a single transition (consuming corresponding inputs),
the resulting states are back in the relation;
3. that any observable 
actions taken by one program are exactly mirrored by the other.

On the high-level side of the bisimulation, the program
state is essentially just the value of the current time step `n`,
whereas on the C side it consists of the regions of global memory that
contain the ring-buffers and their current indices.  The transition
relation for the high-level program just increments the time value by
one, and the transition for the C program is defined by the action
of the generated `step()` function.

Suppose `s` is one of the stream definitions in the original Copilot
program which is required to retain `k` previous values;
let `buf` be the global variable name of the ring-buffer in the C
program, and `idx` be the global variable name maintaining the
current index into the ring buffer.  Then the correspondence
relation is basically that `0 <= idx < k` and
`s[n+i] =buf[(idx+i) mod k]` as `i` ranges from `0 .. k-1`.
By abuse of notation, here we mean that `s[j]` is
the value of the stream expression `s` evaluated at index `j`,
whereas `buf[j]` means the value obtained by reading the `j`th value
of the buffer `buf` from memory.  The overall correspondence relation
is a conjunction of statements like this, one for each stream
expression that is realized via a buffer.

### Implementing the Bismulation proof steps

The kind of program correspondence property we desire is a largely
mechanical affair. As the code under consideration is automatically
generated, it has a very regular structure and is specifically
intended to implement the semantics we wich to verify it against.  As
such, we expect these proofs to be highly automatable.

The proof principle of bisimulation itself is not amenable
to reduction to SMT, as if falls outside the first-order theories
those solvers understand. Likewise, the semantics of Copilot
and C might possibly be reducible directly to SMT, but it would be
impractical to do so. However, we can reduce the individual
proof obligations mentioned above into a series of lower-level
logical statements that are amenable to SMT proof by
defining the logical semantics of stream programs, and using
symbolic simulation techniques to interpret the semantics of the
C program.  Performing this reduction is the key contribution
of `copilot-verifier`.

#### Initial state correspondence

The proof first obligation we must discharge is to show that
the initial states of the two programs correspond. For each
stream `s` there is a corresponding `k`, which is the length of
the ring-buffer implementing it.  We must simply verify that
the C program initializes its buffer with the first `k` values
of the stream `s`, and that the `idx` value starts at 0.
Because of the restrictions Copilot places on programs, these
first `k` values must be specified concretely and will not be
able to depend on any external inputs.  As such, this step
is quite easily performed, as it requires only direct evaluation
of concrete inputs.

#### Transition correspondence

The bulk of the proof effort consists of demonstrating that
the bisimulation relation is preserved by transitions.
In order to do this step, we must begin with totally symbolic
initial states: we know nothing except that we are at some
arbitrary time value `n`, and that the C program buffers
correspond to their stream values as required by the relation.
Thus, we create fresh symbolic variables for the streams
from `n` to `n + k-1`, and for the values of all the involved
external streams at time `n`. Then, we run forward the Copilot
program by evaluating the stream recurrence expression to
compute the value of each stream at time `n+k`.

Next we set up an initial state of the C program by choosing,
for each ring buffer, an arbitrary value for its current index
within it's allowed range, and then writing the variables
corresponding to each stream value into the buffers at
their appropriate offsets. The symbolic simulator is then
invoked to compute the state update effects of the `step()`
function. Afterward, we read the poststate values from the
ring-buffers and verify that the correspond to the stream
values from `n+1` up to `n+k`.

As part of symbolic simulation, Crucible may also generate
side-conditions that relate to memory safety of the program, or to
error conditions that must be avoided. All of the bisimulation
equivalence conditions and the safety side-conditions will be
submitted to an SMT solver.

#### Observable effects

For our purposes, the only observable effects of a Copilot program
relate to any "trigger" functions defined in the spec.  Our task it to
show that the generated C code calls the external trigger functions if
and only if the corresponding guard condition is true, and that the
arguments passed to those functions are as expected.
This proof obligation is proved in the same phase along with
the transition relation proof above because the `step()` function
is responsible for both invoking triggers and for performing state
updates.

The technique we use to perform this aspect of the proof is to
install "override" functions to the external symbols corresponding
to the C trigger functions before we begin symbolic simulation.
In a real system, the external environment would be responsible
for implementing these functions and taking whatever appropriate
action is necessary when the triggers fire. However, we are verifying
the generated code in isolation from its environment, so we have no
implementation in hand. Instead, the override will
essentially implement a stub function that simply captures its
arguments and the path condition under which it was called.
After simulation completes, the captured arguments and path condition
are required to be equivalent to the corresponding trigger guard
and arguments from the Copilot spec.  These conditions are
discharged to the SMT solver at the same time as the transition
relation obligations.

Because of the way we model the trigger functions, we make a number of
implicit assumptions about how the actual implementations of those
functions must behave. The most important of those assumptions is that
the trigger functions must not modify any memory under the control of
the Copilot program, including its ring buffers and stack.  We also
assume that the trigger functions are well defined, i.e. they are
memory safe and do not perform any undefined behavior.  Finally, we
assume that they implement "normal" control flow and will eventually
return to their caller.  This last requirement may well be violated if
the trigger function actually performs some aborting action, or
otherwise halts normal execution; however, this seems relatively
harmless from the point of view of correctness of the generated code.
