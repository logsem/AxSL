The goal of this project is to provide a full system model of an architecture
entirely in Coq. This requires interfacing an ISA model and a relaxed-memory concurrency model.

 In order to do that we need.
- An interface between both models.
- An ISA model, which we intend to be either a direct Sail to Coq
  export or a Coq import of isla traces
- A concurrency model. For now the intention is to implement this directly in
  Coq as a separate directory in this repository. This may change.

This repository is currently work in progress so not everything may build easily.



## Goals

### Interface

The goal for the interface is to support multiple architecture and all
our use cases. The immediate target architecture is Arm-A, but in the
long term it should also support Morello, RISC-V, CHERI-RISC-V, Power,
x86, and Arm-M.

The interface is mainly defined in Sail, such that all Sail exports use the same
interface. It is composed of a generic part that is common to all architectures
and an architecture-specific part, for which we give an instantiation for Arm-A.

The interface is defined around the concept of outcomes, which are requests that
the ISA can make to a memory model. The interface is (loosely speaking) a monad;
the ISA model is a monadic value in that monad; and the memory model is an
implementation of that monad. Another way of seeing it is that the interface is
a set of algebraic effects called by the ISA model and provided by the memory
model. The set of outcomes is entirely generic, although the types they contain
can be architecture-specific. This set of outcomes is defined in
`ISASem/Interface.v` and is a bit bigger than the corresponding set of Sail
outcomes. This is because certain actions are implicit in the Sail language but
explicit in the Coq outcome type. For now those actions are:

- Accessing registers (special variable access in Sail but not an outcome)
- Making a non-deterministic choice. (undefined in Sail).
- Ending an instruction (Returning from top level function in Sail)

In terms of use-cases, the interface need to be usable with sequential models,
operational models, axiomatic models, and promising models. For operational
models, it needs to be similar to the existing RMEM interface, in particular it
needs to contain write announcements.

There is some open questions with dependencies that are not fully resolved. In the
current version the Coq interface expects dependency information that is not
provided by a Sail model. For now this gap is intended to be filled with
information from `isla-footprint` but this may change.

The interface should ideally support all system features that are directly used
by the ISA. This includes raising exceptions, translating virtual memory, and
doing relaxed system register access. It should support being used with and
without address translation.

At some point later point, the interface should support intra-instruction
concurrency with a `par` construct. This is not implemented yet.

The interface does not support any SoC aspects like the Arm GIC.


### Getting an ISA model that uses the interface.

There are two ways of getting the instruction semantics from Sail:
 - Export the Sail model to Coq
 - Extract simplified instruction traces with Isla and import them into Coq with
   the Islaris frontend.

We intend to study both options.


### Memory-System model implementations.

For now the goal is to have an executable promising model as well as a
non-executable axiomatic model. The exact feature coverage that we aim for those
is to be determined.

## Directory structure

- `Common` contains standard-library like features, support type definitions,
  and automation helpers. Some of it could be upstreamed and some of it is specific
  to this development.
- `ISASem` contains the ISA semantics interface that models may use. In
  particular this is where the main concurrency interface is defined as well as
  the Arm instantiation. 
- `GenModels` contains generic definitions to discuss machine models.
  the Arm instantiation. The Arm instantiation will move to the
  `sail-arm` repository at some later point.
