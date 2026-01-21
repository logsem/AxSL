(**************************************************************************************)
(*  BSD 2-Clause License                                                              *)
(*                                                                                    *)
(*  This applies to all files in this archive except folder                           *)
(*  "system-semantics".                                                               *)
(*                                                                                    *)
(*  Copyright (c) 2023,                                                               *)
(*       Zongyuan Liu                                                                 *)
(*       Angus Hammond                                                                *)
(*       Jean Pichon-Pharabod                                                         *)
(*       Thibaut Pérami                                                               *)
(*                                                                                    *)
(*  All rights reserved.                                                              *)
(*                                                                                    *)
(*  Redistribution and use in source and binary forms, with or without                *)
(*  modification, are permitted provided that the following conditions are met:       *)
(*                                                                                    *)
(*  1. Redistributions of source code must retain the above copyright notice, this    *)
(*     list of conditions and the following disclaimer.                               *)
(*                                                                                    *)
(*  2. Redistributions in binary form must reproduce the above copyright notice,      *)
(*     this list of conditions and the following disclaimer in the documentation      *)
(*     and/or other materials provided with the distribution.                         *)
(*                                                                                    *)
(*  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"       *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE         *)
(*  IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE    *)
(*  DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE      *)
(*  FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL        *)
(*  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR        *)
(*  SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER        *)
(*  CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,     *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE     *)
(*  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.              *)
(*                                                                                    *)
(**************************************************************************************)

(* This file contains the instruction semantics *)
Require Import Strings.String.
(* to use monad notations *)
Require Import stdpp.base.
Require Import stdpp.gmap.
Require Import stdpp.bitvector.definitions.

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

  Inductive BarKind := | BKsy | BKld | BKst | BKisb.

  Implicit Type ae : ArithExp.
  Implicit Type addr : Addr.
  Implicit Type bk : BarKind.
  Implicit Type ks : AccessStrength.
  Implicit Type kv : AccessVariety.

  Inductive Instruction :=
  | ILoad kv ks r ae
  | IStore kv ks r ae1 ae2 (* src, dst *)
  | IBarrier bk
  | IAssign r ae
  | IBr addr
  | IBne ae addr
  | INop.

End instructions.

Section interpretation.

  Implicit Type ks : AccessStrength.
  Implicit Type kv : AccessVariety.
  Implicit Type bk : BarKind.

  Import AAInter.
  Import AACand.

  (* interp of expressions *)
  Fixpoint AEInterp ae : AAInter.iMon Val :=
    match ae with
    | AEval w => Ret w
    | AEreg r => Next (RegRead r ()) (fun w => mret w)
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
  Definition IncPCInterp : iMon :=
    w ← Next (RegRead RNPC ()) (fun w => mret w);
    (* We don't track dependencies for the PC, since it's not a GPR *)
    Next (RegWrite RNPC () (w `+Z` 4)%bv None) (fun _ => Ret tt).

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
  Definition access_kind_of_AK kv ks : machine.AccessKind := AK_explicit (Build_Explicit_access_kind kv ks).

  (* making [WriteReq] *)
  Definition writereq_of_store kv ks w addr adep ddep : WriteReq.t 8:=
    WriteReq.make _ addr (access_kind_of_AK kv ks) w (Some false) adep ddep.

  (* making [ReadReq] *)
  Definition readreq_of_load kv ks addr adep : ReadReq.t 8:=
    ReadReq.make _ addr (access_kind_of_AK kv ks) false adep.

  (* Definition empty_depon := Some (DepOn.make [] []). *)

  Definition barrier_of bk : BarrierKind :=
    match bk with
    | BKsy => Barrier_DMB (Build_DxB MBReqDomain_FullSystem MBReqTypes_All true)
    | BKst => Barrier_DMB (Build_DxB MBReqDomain_FullSystem MBReqTypes_Writes true)
    | BKld => Barrier_DMB (Build_DxB MBReqDomain_FullSystem MBReqTypes_Reads true)
    | BKisb => Barrier_ISB ()
    end.


  (* interp of instructions *)
  Definition InstrInterp (i : Instruction) : iMon:=
    match i with
    | ILoad kv ks r ae =>
        addr ← AEInterp ae;
        Next (MemRead _ (readreq_of_load kv ks addr (Some (dep_of_AE ae))))
          (* bool is for cheri tags *)
          (fun (out: (bv _ * option bool + abort)) =>
             match out with
             | inl (w, _) => Next (RegWrite r () w (Some (DepOn.make [] [0%N]))) (fun _ => Ret tt)
             (* Unreachable, since abort is empty *)
             | inr _ => Ret tt end);;
        IncPCInterp
    | IStore kv ks r ae1 ae2 =>
        w ← AEInterp ae1;
        addr ← AEInterp ae2;
        Next (MemWrite _ (writereq_of_store kv ks w addr (Some (dep_of_AE ae2)) (Some (dep_of_AE ae1))))
          (* bool is for atomic write success *)
          (fun (out: bool + abort) =>
             if bool_decide (kv = AV_exclusive) then
               match out with
               (* NOTE: No dependencies on result bit *)
               | inl b => Next (RegWrite r () (bool_to_bv _ b) None) (fun _ => Ret tt)
               (* Unreachable, since abort is empty *)
               | _ => Ret tt end
             else Ret tt);;
        IncPCInterp
    | IBarrier bk => Next (Barrier (barrier_of bk)) (fun _ => Ret tt);;
              IncPCInterp
    | IAssign r ae =>
        w ← AEInterp ae;
        Next (RegWrite r () w (Some (dep_of_AE ae))) (fun _ => Ret tt);;
        IncPCInterp
    | IBr addr => Next (RegWrite RNPC () addr None) (fun _ => Ret tt)
    | IBne ae addr =>
        w ← AEInterp ae;
        (* (* NOTE: This is not how [BranchAnnounce] is supposed to be used *) *)
        Next (BranchAnnounce addr (Some (dep_of_AE ae))) (fun _ => Ret tt);;
        if (bool_decide (w = Z_to_bv _ 0))
        then IncPCInterp
        else Next (RegWrite RNPC () addr None) (fun _ => Ret tt)
    | INop => IncPCInterp
    end.

  Definition EmptyInterp : iMon := Ret tt.

End interpretation.
