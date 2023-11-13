(* This file contains the [CMRA] typeclass that is used by both the logic construction and the RAs *)
From iris.base_logic.lib Require Export iprop.

(* Make Coq aware of Σ with type class search *)
Class CMRA `{Σ: !gFunctors} := {}.
