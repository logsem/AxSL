This repository contains the Coq mechanisation of the Arm-A instance of AxSL, 
an Iris-based program logic for Arm-A relaxed concurrency.

## Building the Project

The project can be compiled using the OCaml building system `dune` with required denpendencies installed.
The building scripts are organised into `dune-project` and severnal `dune` files.

Refer to `INSTALL.md` for more information on building it in a Docker environment or
manually.

## Structure of the Development

The Coq development is organised into two subdirectories.

The `theories` directory contains the primary Coq development of the work, including:

- `lang`: This directory contains definitions of instructions, the Arm memory model, and our opax 
semantics.
  - `lang/instrs.v` defines the semantics of instructions using the outcome interface.
  - `lang/mm.v` (combined with `CandidateExecutions.v`) defines the (user) Arm memory model.
  - `lang/opsem.v` defines the opax semantics.

- `algebra`: This directory includes most of the ghost state constructions for the logical assertions 
of `AxSL`.

- `low`: This directory contains the definition of weakest preconditions, the soundness proof of 
low-level proof rules, and the adequacy theorem.
  - `low/weakestpre.v` defines the base weakest precondition that is parameterised by the implementation 
  of state interpretation. It also contains the definition of flow implications.
  - `low/instantiation.v` and `low/*_res.v` contains the instantiation of the base weakest precondition with a specific 
  state interpretation implementation.
  - `low/rules/*.v` contain base proof rules and their soundness proofs.
  - `low/lifting.v` and `low/adequacy.v` contain the adequacy proof with respect to the base weakest 
  precondition.

- `middle`: This directory contains the proof rules for all microinstructions and abstraction layers.
  - `middle/weakestpre.v` defines an abstraction layer based on low-level weakest preconditions.
  - `middle/rules.v` contains proof rules for some instructions and their soundness proofs (utilising 
  the results of `low/rules/*.v`).
  - `middle/excl.v` contains our solution for supporting exclusives.
  - `middle/specialised_rules.v` contains proof rules for specific instructions used in verified examples
  and their soundness proofs.

- `examples`: This directory contains the examples.
  - `examples/lb/` includes four variants of load-buffering and their proofs.
  - `examples/mp/` contains four variants of message-passing and their proofs.
  - `examples/isa2/` contains a variant of ISA2 and its proofs.
  - `examples/co/` contains two coherence examples and their proofs.
  - `examples/try_lock/` contains an implementation of try lock using exclusives, a mutual exclusion example using the lock, and their proofs.

The `system-semantics` directory contains the Coq infrastructure used to define and reason about 
memory models, including:

- `ISASem`: This directory contains the ISA semantics interface that models may use.
  - `ISASem/Interface.v` defines the main concurrency interface.
  - `ISASem/ArmInst.v` and `ISASem/SailArmInstTypes.v` together define the Arm instantiation of the 
  interface, which is used to define the Arm memory model.

- `Common`: This directory contains standard-library-like features, support type definitions, and 
automation helpers.
  - `Common/GRel.v` contains an implementation of relations and operations for relation algebra.
