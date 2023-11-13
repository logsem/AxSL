This repositary contains the artifact of POPL 2024 paper 
"An axiomatic basis for computer programming on the relaxed Arm-A architecture: the AxSL Logic".

## About the Artifact

This artifact is a mechanised proof development that contains formalised definitions and proofs that 
can be checked by the Coq proof assistant. It contains all the results presented in the paper.

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
  of state interpretation.
  - `low/instantiation.v` contains the instantiation of the base weakest precondition with a specific 
  state interpretation implementation.
  - `low/rules/*.v` contain base proof rules and their soundness proofs.
  - `low/lifting.v` and `low/adequacy.v` contain the adequacy proof with respect to the base weakest 
  precondition.
  - `low/lib/annotations.v` contains the definitions of protocols and flow implications.

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
  

## Reference for the Results of the Paper

| § | Result(s) in paper        | Location in code           | Object(s) in code                                          | Remarks/Diffs                                                                                                                                                                                                                                                                                                |
|---|--------------------------|----------------------------|------------------------------------------------------------|--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 2 | Fig. 3                   | `lang/mm.v`                | Module `AAConsistent`                                      | Consistency axioms are in the record `t`.                                                                                                                                                                                                                                                                         |
| 3 | The splitting rule used in Fig. 7  | `low/rules/prelude.v`   | `annot_split_iupd`                                         | `↦ₐ` is the notation for tied assertions.                                                                                                                                                                                                                                                                         |
| 4 | Fig. 8                   | `lang/instrs.v`            | Section `instructions`                                     | `os` and `vr` are defined in `system-semantics-coq`.                                                                                                                                                                                                                                                                         |
|   | Fig. 9                   |                            | Section `interpretation`                                   | The outcome interface is from `system-semantics-coq`. `;;` corresponds to `>>=`.                                                                                                                                                                                                                                             |
|   | `Whole-system-execution` | `low/adequacy.v`           | `tpsteps`, `tpstate_done`, `tp_state_init`                 | There is no formal definition of the rule; we instead only defined the premises.                                                                                                                                                                                                                           |
|   | Fig. 10                  | `lang/opsem.v`             | Module `LThreadStep`                                       | `t` of the module defines the reduction relation; see below for more.                                                                                                                                                                                                                                         |
|   | Graph `X` and Instruction memory `I` |                    | Module `GlobalState`                                       |                                                                                                                                                                                                                                                                                                              |
|   | `H-mem-read`             |                            | `TStepReadMem`                                             | We use `⊆` instead of `=` for `addr` and `ctrl`; `po1` is handled differently in our formalisation.                                                                                                                                                                                               |
|   | `H-reg-write`            |                            | `TStepRegWrite`                                            | `po1` is handled differently in our formalisation.                                                                                                                                                                                                                                                            |
|   | `H-reload`               |                            | `TStepReload`                                              | `ts_is_done_instr` is omitted in the rule.                                                                                                                                                                                                                                                                    |
|   | `H-term`                 |                            | `TStepTerm`                                                | `ts_is_done_thd` implements the last premise.                                                                                                                                                                                                                                                                 |
|   | `T` of `Ctd T` and `R` of `Done R`  |                 | Module `ThreadState`                                       | Field `ts.reqs` of record `t` corresponds to program `T.p`; `R` is the rest of the fields, except for that we have an extra `ts_rmw_pred` to handle exclusive; `iis_iid` and `iis_cntr` together correspond to `e`; `next-e` is inline; `e_{po}` is defined separately as `lls_pop` of `LogicalLocalState`. |
|   | `Ctd T` and `Done R`    |                            | Module `LThreadState`                                      | Both take `ThreadState.t` in the code.                                                                                                                                                                                               |
| 5 | Protocol `Φ`             | `low/instantiation.v`      | Typeclass `UserProt`                                       | The type `prot_t` is defined in `low/lib/annotations.v`.                                                                                                                                                                                                                                                      |
|   | Fig. 11                  | `middle/specialised_rules.v` | `mem_read_external`                                    | Hoare triples are implemented in a continuation-passing style using `WP`: the preconditions are premises; the post conditions are in the continuation. The Coq definition is slightly more general: it does not have constraint `(2)`. Detailed correspondence can be found below.                                                     |
|   | `(1) & (10) NoLocalWrites` |                           | `last_local_write`                                         |                                                                                                                                                                                                                                                                                                              |
|   | `(3) & (11) PoPred`      |                            | `o_po_src -{LPo}>`                                         |                                                                                                                                                                                                                                                                                                              |
|   | `(4) & (12) CtrlPreds`   |                            | `ctrl_srcs -{Ctrl}>`                                       |                                                                                                                                                                                                                                                                                                              |
|   | `(5) & (13)`             |                            | `([∗ map] dr ↦ dv ∈ dep_regs, dr ↦ᵣ dv)`                   | `dep_regs` is `regs`.                                                                                                                                                                                                                                                                                         |
|   | `(6)`                    |                            | `([∗ map] node ↦ annot ∈ lob_annot, node ↦ₐ annot)`        | `lob_annot` is `m`.                                                                                                                                                                                                                                                                                           |
|   | `(7) & (14) GraphFacts`  |                            | `R_graph_facts` of `mem_read_external`                     |                                                                                                                                                                                                                                                                                                              |
|   | `(8) Lob`                |                            | Lines between comments `Lob edge formers` and `FE`         |                                                                                                                                                                                                                                                                                                              |
|   | `(9) FlowIn`             |                            | Lines between comment `FE` and `continuation`              | `={⊤}[∅]▷=∗` is the view shift that also supports invariants; `prot` (field of `UserProt`) is the protocol `Φ`. The persistent `R_graph_facts` are assumed again.                                                                                                                                      |
|   | `(15)`                   |                            | `eid ↦ₐ R addr val eid_w`                                  |                                                                                                                                                                                                                                                                                                              |
|   | Fig. 13, 14              | `examples/lb/data_data2.v` | `instrs`, `userprot_val`, `write_val_thread_1`, `write_val_thread_2`   | `instrs` is the LB program, `userprot_val` is `Φ`, and the remaining two are the specs and their proofs.                                                                                                                                                                                                                                                |
|   | Oneshot                  | `one_shot`                | Section `one_shot`                                         |                                                                                                                                                                                                                                                                                                              |
|   | Instruction Hoare triple |                            | `SSWPi`                                                    | Defined using single-step instruction weakest precondition `SSWPi`.                                                                                                                                                                                                                                                                                   |
|   | Fig. 15                  |                            | `wpi_pln_read`, `wpi_pln_write_data`                       |                                                                                                                                                                                                                                                                                                              |
|   | Fig. 16                  | `examples/mp.v`            | `send_instrs`, `dep_receive_instrs`                        |                                                                                                                                                                                                                                                                                                              |
|   | `Φ(flag,v,e)`            |                            | `flag_prot`                                                |                                                                                                                                                                                                                                                                                                              |
|   | The invariant for exclusives | `middle/excl.v`          | `excl_inv`                                                 |                                                                                                                                                                                                                                                                                                              |
|   | Proof rules for exclusives | `middle/rules.v`           | `mem_write_xcl_Some_inv`, `mem_write_xcl_None`             | Again in the continuation-passing style. For successful and unsuccessful exclusive stores; Exclusive loads are handled in `mem_read_external` with extra machinery.                                                                                                                                                                                   |
| 6 | The microinstruction Hoare triple | `middle/weakestpre.v`  | `wpi_def`                                                  | Defined using weakest preconditions, so `P` is not mentioned. The Coq definition (`WPi`) is actually a weakest precondition for instructions, not microinstructions, but the definition follows the same spirit as the presented microinstruction one.                                                                                                                                                                                                    |
|   | `SI-reg-agree` and `SI-reg-update` |                       | `reg_interp_agree`, `reg_interp_update`                    |                                                                                                                                                                                                                                                                                                              |
|   | Definition of weakest precondition | `low/weakestpre.v`       | `wp_pre`                                                   | The formalisation in Coq is quite different -- the paper only demonstrates the key ideas. Most importantly: `annot_interp` is `SI_{T}`; `gconst_interp` is `SI_{G}`; `flow_eq` is `FlowImp`; `post_lifting` is `PullOutTied`.                                                                                                                                                                                                      |
|   | `FlowImp`                | `low/lib/annotations.v`     | `flow_eq_ea`, `na_splitting_wf`                            | `flow_eq_ea` is the view shift; `na_splitting_wf` is `Detach`; the map extension is inlined in `wp_pre`.                                                                                                                                                                                                      |
|   | Supporting framing       | `low/instantiation.v`       | `annot_split`                                              |                                                                                                                                                                                                                                                                                                              |
|   | Supporting invariants    | `low/lib/annotations.v`     | `={⊤,∅}=∗ ▷ \|={∅,⊤}=>` of `flow_eq_ea`                    | Same as `={⊤}[∅]▷=∗`.                                                                                                                                                                                                                                                                                         |
|   | Theorem 6.1              | `middle/rules.v`, `middle/specialised_rules.v`, `low/rules/*.v` |                                                            | `middle/rules.v` and `middle/specialised_rules.v` contain the soundness proof of all microinstruction proof rules (in continuation style, proved using results in `low/rules/*.v`).                                                                                                                                                                                    |
|   | Theorem 6.2              | `low/adequacy.v`           | `adequacy_pure`                                            | With insignificant details omitted.                                                                                                                                                                                                                                                                                                        |
