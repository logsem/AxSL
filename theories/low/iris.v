(* This file contains the typeclass which is the parameter of the low-level logic,
  the weakest precondition and adequacy can be instantiated by any instance of the typeclass*)
From iris.base_logic.lib Require Export fancy_updates.

From self Require Export cmra.
From self.lang Require Export opsem.
From self.low.lib Require Export annotations.
Import uPred.

Class irisG `{CMRA Σ} `{!invGS_gen HasNoLc Σ} := IrisG {
  (* Interpretation of tied assertions *)
  annot_interp : mea Σ -> iProp Σ;
  (* Interpretation of global instruction memory and graph *)
  gconst_interp : GlobalState.t -> iProp Σ;
}.


Class irisGL `{CMRA Σ} := IrisGL {
  (* logical thread state *)
  log_ts_t : Type;
  (* local interpretation (for both 'physical' and logical ts), parametrised by tid *)
  local_interp : GlobalState.t -> Tid -> ThreadState.progress -> log_ts_t ->iProp Σ;
}.
