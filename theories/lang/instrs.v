(* This file contains the instruction semantics *)
Require Import Strings.String.
(* to use monad notations *)
Require Import stdpp.base.
Require Import stdpp.gmap.
Require Import stdpp.unstable.bitvector.

Require Import ISASem.Interface.

Require Import self.lang.machine.

Local Open Scope stdpp_scope.

Section instructions.
  Implicit Type r : RegName.
  Implicit Type w : Val.

  Definition AccessStrength := Access_strength.
  Definition AccessVariety := Access_variety.

  Inductive ArithOp :=
  | AOplus | AOminus | AOtimes.

  Inductive ArithExp :=
  | AEval w
  | AEreg r
  | AEbinop (op: ArithOp) (ae1: ArithExp) (ae2: ArithExp).

  Implicit Type ae : ArithExp.
  Implicit Type dκ : DmbKind.
  Implicit Type addr : Addr.
  Implicit Type kv : AccessVariety.
  Implicit Type ks : AccessStrength.

  Inductive Instruction :=
  | ILoad ks kv r ae
  | IStore ks kv r ae1 ae2 (* src, dst *)
  | IDmb dκ
  | IIsb
  | IAssign r ae
  | IBr addr
  | IBne ae addr
  | INop.

End instructions.

Section interpretation.

  Import AAInter.
  Import AACandExec.

  (* interp of expressions *)
  Fixpoint AEInterp ae : iMon Val :=
    match ae with
    | AEval w => Ret w
    | AEreg r => Next (RegRead r true) (fun w => mret w)
    | AEbinop op ae1 ae2 => w1 ← (AEInterp ae1);
                            w2 ← (AEInterp ae2);
                            Ret (match op with
                                 | AOplus => w1 + w2
                                 | AOminus => w1 - w2
                                 | AOtimes => w1 * w2
                              end)%bv
    end.

  Definition RNPC : string := "pc".

  (* increment PC *)
  Definition IncPCInterp : iMon unit :=
    w ← Next (RegRead RNPC true) (fun w => mret w);
    (* We don't track dependencies for the PC, since it's not a GPR *)
    Next (RegWrite RNPC true None (w `+Z` 4)%bv) (fun _ => Ret tt).

  (* computing dependencies of an expression *)
  Fixpoint dep_of_AE_aux ae :=
    match ae with
    | AEval _ => []
    | AEreg r => [r]
    | AEbinop _ ae1 ae2 => app (dep_of_AE_aux ae1) (dep_of_AE_aux ae2)
    end.

  (* lifting dependencies to [DepOn], with memory dependencies [l] *)
  Definition dep_of_AE_with_m ae l:= DepOn.make (dep_of_AE_aux ae) l.

  (* lifting with no memory dependencies *)
  Definition dep_of_AE ae := DepOn.make (dep_of_AE_aux ae) [].

  (* lifting access kinds to [accessKind] *)
  Definition access_kind_of_AK kind_strength kind_variety : accessKind :=
   AK_explicit (Build_Explicit_access_kind kind_variety kind_strength).

  (* making [WriteReq] *)
  Definition writereq_of_store {n} kind_strength kind_variety w addr dep_a dep_d : WriteReq.t n:=
    WriteReq.make _ addr (access_kind_of_AK kind_strength kind_variety) w None tt false (Some dep_a) (Some dep_d).

  (* making [ReadReq] *)
  Definition readreq_of_store {n} kind_strength kind_variety addr dep_a : ReadReq.t n:=
    ReadReq.make _ addr (access_kind_of_AK kind_strength kind_variety) None tt false (Some dep_a).

  Definition empty_depon := Some (DepOn.make [] []).

  (* interp of instructions *)
  Definition InstrInterp (i : Instruction) : iMon () :=
    match i with
    | ILoad ks kv r ae =>
        addr ← AEInterp ae;
        Next (MemRead AAArch.val_size (readreq_of_store ks kv addr (dep_of_AE ae)))
          (* bool is for cheri tags *)
          (fun (out: (bv _ * option bool + abort)) =>
             match out with
             | inl (w, _) => Next (RegWrite r true (Some (DepOn.make [] [0%N])) w) (fun _ => Ret tt)
             (* Unreachable, since abort is empty *)
             | inr _ => Ret tt end);;
        IncPCInterp
    | IStore ks kv r ae1 ae2 =>
        w ← AEInterp ae1;
        addr ← AEInterp ae2;
        Next (MemWrite _ (writereq_of_store ks kv w addr (dep_of_AE ae2) (dep_of_AE ae1)))
          (* bool is for atomic write success *)
          (fun (out: option bool + abort) =>
             match out with
             | inl None => Ret tt
             (* NOTE: No dependencies on result bit *)
             | inl (Some b) => Next (RegWrite r true empty_depon (bool_to_bv _ b)) (fun _ => Ret tt)
             (* Unreachable, since abort is empty *)
             | _ => Ret tt end);;
        IncPCInterp
    | IDmb dκ => Next (Barrier (AAArch.DMB dκ)) (fun _ => Ret tt);;
              IncPCInterp
    | IIsb => Next (Barrier AAArch.ISB) (fun _ => Ret tt);;
              IncPCInterp
    | IAssign r ae =>
        w ← AEInterp ae;
        Next (RegWrite r true (Some (dep_of_AE ae)) w) (fun _ => Ret tt);;
        IncPCInterp
    | IBr addr => Next (RegWrite RNPC true empty_depon addr) (fun _ => Ret tt)
    | IBne ae addr =>
        w ← AEInterp ae;
        (* NOTE: This is not how [BranchAnnounce] is supposed to be used *)
        Next (BranchAnnounce addr (Some (dep_of_AE ae))) (fun _ => Ret tt);;
        if (bool_decide (w = Z_to_bv _ 0))
        then IncPCInterp
        else Next (RegWrite RNPC true empty_depon addr) (fun _ => Ret tt)
    | INop => IncPCInterp
    end.

  Definition EmptyInterp : iMon () := Ret tt.

End interpretation.
