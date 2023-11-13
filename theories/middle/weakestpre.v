(*                                                                                  *)
(*  BSD 2-Clause License                                                            *)
(*                                                                                  *)
(*  This applies to all files in this archive except folder                         *)
(*  "system-semantics".                                                             *)
(*                                                                                  *)
(*  Copyright (c) 2023,                                                             *)
(*     Zongyuan Liu                                                                 *)
(*     Angus Hammond                                                                *)
(*     Jean Pichon-Pharabod                                                         *)
(*     Thibaut Pérami                                                               *)
(*                                                                                  *)
(*  All rights reserved.                                                            *)
(*                                                                                  *)
(*  Redistribution and use in source and binary forms, with or without              *)
(*  modification, are permitted provided that the following conditions are met:     *)
(*                                                                                  *)
(*  1. Redistributions of source code must retain the above copyright notice, this  *)
(*     list of conditions and the following disclaimer.                             *)
(*                                                                                  *)
(*  2. Redistributions in binary form must reproduce the above copyright notice,    *)
(*     this list of conditions and the following disclaimer in the documentation    *)
(*     and/or other materials provided with the distribution.                       *)
(*                                                                                  *)
(*  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"     *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE       *)
(*  IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE  *)
(*  DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE    *)
(*  FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL      *)
(*  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR      *)
(*  SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER      *)
(*  CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,   *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE   *)
(*  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.            *)
(*                                                                                  *)

(** This file contains the instantiation of the middle-level logic,
 this is the file that all helper files import*)
From iris_named_props Require Export named_props.
From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Export agree gset lib.dfrac_agree.
From iris.base_logic.lib Require Export ghost_map.

From self.lang Require Import opsem.
From self.low Require Export weakestpre.

Import uPred.

Module LTSI.
  Import ThreadState.

  Inductive mode : Type :=
    Normal | Done.

  Definition to_lts (mode : mode) (ts : ThreadState.t) :=
    match mode with
    | Normal => LThreadState.LTSNormal ts
    | Done => LThreadState.LTSDone ts
    end.

  Definition t : Type := (mode * Addr).

End LTSI.

Class irisGInst `{CMRA Σ} :=
  {
    inst_thread_interp : ThreadState.t -> iProp Σ;
    inst_addr_is : Addr -> ThreadState.t -> Prop;
  }.

Definition to_lts_Phi `{CMRA Σ} `{!irisGInst} (Φ : LTSI.t -> iProp Σ)
  (lts : LThreadState.t) : iProp Σ :=
  match lts with
  | LThreadState.LTSNormal ts => inst_thread_interp ts ∗
                                ∃ ins_addr', ⌜inst_addr_is ins_addr' ts⌝ ∗
                                             Φ (LTSI.Normal, ins_addr')
  | LThreadState.LTSDone ts => inst_thread_interp ts ∗
                              ∃ ins_addr', ⌜inst_addr_is ins_addr' ts⌝ ∗
                                           Φ (LTSI.Done, ins_addr')
  end.


Definition wpi_def `{CMRA Σ} `{!invGS_gen HasNoLc Σ} `{!irisG} `{!irisGL} `{!Protocol} `{!irisGInst}
  (tid: Tid) (ltsi : LTSI.t) (Φ : LTSI.t -> iProp Σ) : iProp Σ :=
  (∀ (ts : ThreadState.t),
     "%PC" ∷ ⌜inst_addr_is ltsi.2 ts⌝ -∗
     "Hinterp" ∷ inst_thread_interp ts -∗
     WP (LTSI.to_lts ltsi.1 ts) @ tid {{ ltsi, (to_lts_Phi Φ) ltsi}})%I.

Definition wpi_aux : seal (@wpi_def). Proof. by eexists. Qed.
Definition wpi := wpi_aux.(unseal).

Arguments wpi {Σ _ _ _ _ _ _}.
Lemma wpi_eq `{CMRA Σ} `{!invGS_gen HasNoLc Σ} `{!irisG} `{!irisGL} `{!Protocol} `{!irisGInst} : wpi = @wpi_def Σ _ _ _ _ _ _.
Proof. rewrite -wpi_aux.(seal_eq) //. Qed.

Notation "'WPi' m @ id {{ Φ } }" := (wpi id m Φ)
                                      (at level 20, m, Φ at level 200, only parsing) : bi_scope.

Notation "'WPi' m @ id {{ v , Q } }" := (wpi id m (λ v, Q))
                                          (at level 20, m, Q at level 200,
                                             format "'[' 'WPi'  m  '/' '[       ' @  id   {{  v ,  Q  } } ']' ']'") : bi_scope.

Definition sswpi_def `{CMRA Σ} `{!invGS_gen HasNoLc Σ} `{!irisG} `{!irisGL} `{!Protocol} `{!irisGInst}
  (tid: Tid) (ltsi : LTSI.t) (Φ : LTSI.t -> iProp Σ) : iProp Σ :=
  (∀ Ψ,
     "Hcont" ∷ (∀ ltsi', Φ ltsi' -∗ (WPi ltsi' @ tid {{ ltsi, Ψ ltsi}})) -∗
     WPi ltsi @ tid {{ ltsi', Ψ ltsi'}})%I.

Definition sswpi_aux : seal (@sswpi_def). Proof. by eexists. Qed.
Definition sswpi := sswpi_aux.(unseal).

Arguments sswpi {Σ _ _ _ _ _ _}.
Lemma sswpi_eq `{CMRA Σ} `{!invGS_gen HasNoLc Σ} `{!irisG} `{!irisGL} `{!Protocol} `{!irisGInst}: sswpi = @sswpi_def Σ _ _ _ _ _ _.
Proof. rewrite -sswpi_aux.(seal_eq) //. Qed.

Notation "'SSWPi' i @ id {{ Φ } }" := (sswpi id i Φ)
                                        (at level 20, i, Φ at level 200, only parsing) : bi_scope.

Notation "'SSWPi' i @ id {{ v , Q } }" := (sswpi id i (λ v, Q))
                                            (at level 20, i, Q at level 200,
                                               format "'[' 'SSWPi'  i  '/' '[       ' @  id  {{  v ,  Q  } } ']' ']'") : bi_scope.

Section wpi.
  Context `{CMRA Σ}.
  Context `{!invGS_gen HasNoLc Σ}.
  Context `{!irisG}.
  Context `{!irisGL}.
  Context `{!Protocol}.
  Context `{!irisGInst}.
  Implicit Types Φ : LTSI.t → iProp Σ.
  Implicit Types s : LTSI.t.
  Implicit Types id : Tid.

  Lemma sswpi_wpi id s Φ :
    SSWPi s @ id {{s', WPi s' @ id {{ Φ }} }} ⊢ WPi s @ id {{ Φ }}.
  Proof.
    rewrite sswpi_eq /sswpi_def.
    iIntros "SSWP". iDestruct ("SSWP" $! Φ ) as "SSWP".
      iApply "SSWP". iIntros (?) "$".
  Qed.

  #[global] Instance sswpi_ne id s n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (sswpi id s).
  Proof.
    rewrite sswpi_eq /sswpi_def; intros ?? Heq.
    do 6 f_equiv. rewrite /to_lts_Phi /=. repeat f_equiv.
  Qed.

  #[global] Instance wpi_ne id s n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (wpi id s).
  Proof.
    rewrite wpi_eq /wpi_def; intros ?? Heq.
    do 6 f_equiv. rewrite /to_lts_Phi /=. repeat f_equiv.
  Qed.

  #[global] Instance sswpi_proper id s :
    Proper (pointwise_relation _ (≡) ==> (≡)) (sswpi id s).
  Proof.
    by intros Φ Φ' ?; apply equiv_dist=>n; apply sswpi_ne=>v; apply equiv_dist.
  Qed.

  #[global] Instance wpi_proper id s :
    Proper (pointwise_relation _ (≡) ==> (≡)) (wpi id s).
  Proof.
    by intros Φ Φ' ?; apply equiv_dist=>n; apply wpi_ne=>v; apply equiv_dist.
  Qed.

  Lemma to_lts_mono lts Φ Ψ :
    to_lts_Phi Φ lts -∗
    (∀ s', Φ s' -∗ Ψ s') -∗
    to_lts_Phi Ψ lts.
  Proof.
    iIntros "H Himp". rewrite /to_lts_Phi.
    destruct lts;auto;iDestruct "H" as "($ & %&?&H)";iExists _; iFrame;
    iApply ("Himp" with "H").
  Qed.

  Lemma to_lts_strong_mono lts Φ Ψ :
    to_lts_Phi Φ lts -∗
    (∀ s', Φ s' ==∗ Ψ s') ==∗
    to_lts_Phi Ψ lts.
  Proof.
    iIntros "H Himp".
    rewrite /to_lts_Phi.
    destruct lts;auto;iDestruct "H" as "($ & %&?&H)";iExists _; iFrame;
    iApply ("Himp" with "H").
  Qed.

  Lemma wpi_strong_mono id s Φ Ψ :
    WPi s @ id {{ Ψ }} -∗
    (∀ s', Ψ s' ==∗ Φ s') -∗
    WPi s @ id {{ Φ }}.
  Proof.
    rewrite wpi_eq /wpi_def.
    iIntros "WP Himp". iIntros (?). repeat iNamed 1.
    iSpecialize ("WP" with "[//] Hinterp").
    iApply (wp_strong_mono with "WP").
    iIntros (?) "H". by iApply (to_lts_strong_mono with "H").
  Qed.

  Lemma wpi_mono id s Φ Ψ :
    (∀ s', Ψ s' ⊢ Φ s') ->
    WPi s @ id {{ Ψ }} -∗
    WPi s @ id {{ Φ }}.
  Proof.
    rewrite wpi_eq /wpi_def.
    iIntros (Himp) "WP %". repeat iNamed 1.
    iSpecialize ("WP" with "[//] Hinterp").
    iApply (wp_mono with "WP").
    iIntros (?) "H". iApply (to_lts_mono with "H").
    iIntros (?) "?". iApply Himp;done.
  Qed.

  Lemma bupd_wpi id s Φ :
    (|==> WPi s @ id {{ Φ }}) ⊢ WPi s @ id {{ Φ }}.
  Proof.
    rewrite wpi_eq /wpi_def.
    iIntros "WP %". repeat iNamed 1.
    iMod "WP". iApply ("WP" with "[//] Hinterp").
  Qed.

  Lemma iupd_wpi id s Φ :
    (|=i=> WPi s @ id {{ Φ }}) ⊢ WPi s @ id {{ Φ }}.
  Proof.
    rewrite wpi_eq /wpi_def. iIntros "WP %". repeat iNamed 1.
    iMod "WP". iApply ("WP" with "[//] Hinterp").
  Qed.

  Lemma wpi_bupd id s Φ :
    WPi s @ id {{ k, |==> Φ k }} ⊢ WPi s @ id {{ Φ }}.
  Proof. iIntros "H". iApply (wpi_strong_mono id with "H"); auto. Qed.


  Lemma sswpi_strong_mono id s Φ Ψ :
    SSWPi s @ id {{ Ψ }} -∗
    (∀ s', Ψ s' ==∗ Φ s') -∗
    SSWPi s @ id {{ Φ }}.
  Proof.
    rewrite sswpi_eq /sswpi_def.
    iIntros "WP Himp". iIntros (?). repeat iNamed 1.
    iApply ("WP" with "[Himp Hcont]" ).
    iIntros (?) "HΨ".
    iApply bupd_wpi. iApply "Hcont".
    by iApply "Himp".
  Qed.

  Lemma sswpi_mono id s Φ Ψ :
    SSWPi s @ id {{ Ψ }} -∗
    (∀ s', Ψ s' -∗ Φ s') -∗
    SSWPi s @ id {{ Φ }}.
  Proof.
    rewrite sswpi_eq /sswpi_def.
    iIntros "WP Himp". iIntros (?). repeat iNamed 1.
    iApply ("WP" with "[Himp Hcont]" ).
    iIntros (?) "HΨ".
    iApply "Hcont".
    by iApply "Himp".
  Qed.

  Lemma bupd_sswpi id s Φ :
    (|==> SSWPi s @ id {{ Φ }}) ⊢ SSWPi s @ id {{ Φ }}.
  Proof.
    rewrite sswpi_eq /sswpi_def.
    iIntros "WP %". repeat iNamed 1.
    iApply bupd_wpi. iMod "WP". by iApply "WP".
  Qed.

  Lemma iupd_sswpi id s Φ :
    (|=i=> SSWPi s @ id {{ Φ }}) ⊢ SSWPi s @ id {{ Φ }}.
  Proof.
    rewrite sswpi_eq /sswpi_def. iIntros "WP %". repeat iNamed 1.
    iApply iupd_wpi. iMod "WP". by iApply "WP".
  Qed.

  Lemma sswpi_bupd id s Φ :
    WPi s @ id {{ k, |==> Φ k }} ⊢ WPi s @ id {{ Φ }}.
  Proof. iIntros "H". iApply (wpi_strong_mono id with "H"); auto. Qed.

  Lemma sswpi_step_bupd id s P Φ :
    (|==> P) -∗
    SSWPi s @ id {{ k, P ==∗ Φ k }} -∗
                 SSWPi s @ id {{ Φ }}.
  Proof.
    rewrite sswpi_eq /sswpi_def. iIntros "P". iIntros "WP %". repeat iNamed 1.
    iApply "WP".
    iIntros (?) "HP". iApply bupd_wpi.
    iMod "P". iApply "Hcont". by iApply "HP".
  Qed.

  Lemma sswpi_step_iupd id s P Φ :
    (|=i=> P) -∗
    SSWPi s @ id {{ k, P -∗ |=i=> Φ k }} -∗
                 SSWPi s @ id {{ Φ }}.
  Proof.
    rewrite sswpi_eq /sswpi_def. iIntros "P". iIntros "WP %". repeat iNamed 1.
    iApply "WP".
    iIntros (?) "HP". iApply iupd_wpi.
    iMod "P". iApply "Hcont". by iApply "HP".
  Qed.

  Lemma wpi_step_bupd id s P Φ :
    (|==> P) -∗
    WPi s @ id {{ k, P ==∗ Φ k }} -∗
               WPi s @ id {{ Φ }}.
  Proof.
    rewrite wpi_eq /wpi_def. iIntros "P". iIntros "WP %". repeat iNamed 1.
    iSpecialize ("WP" with "[//] Hinterp").
    iApply (wp_strong_mono with "WP").
    iIntros (?) "HP". iApply (to_lts_strong_mono with "HP").
    iIntros (?) "HP". iMod "P". by iApply "HP".
  Qed.

  Lemma wpi_step_iupd id s P Φ :
    (|=i=> P) -∗
    WPi s @ id {{ k, P ==∗ Φ k }} -∗
               WPi s @ id {{ Φ }}.
  Proof.
    rewrite wpi_eq /wpi_def. iIntros "P". iIntros "WP %". repeat iNamed 1.
    iSpecialize ("WP" with "[//] Hinterp"). iMod "P".
    iApply (wp_strong_mono with "WP").
    iIntros (?) "HP". iApply (to_lts_strong_mono with "HP").
    iIntros (?) "HP". by iApply "HP".
  Qed.

  Definition inst_post_lifting tid (addr: Addr) Φ :=
    (∀ na : mea Σ, annot_interp na ==∗
                   annot_interp na ∗
                   (([∗ map] e↦R ∈ na, if bool_decide (Graph.is_local_node_of tid e) then R else True) -∗  ▷ |==> Φ (LTSI.Done, addr)))%I.

  Lemma wpi_terminated {tid :Tid} {addr Φ}:
    inst_post_lifting tid addr Φ -∗
    WPi (LTSI.Done, addr) @ tid {{ Φ }}.
  Proof.
    iIntros "Hpost".
    rewrite wpi_eq /wpi_def. iIntros (?). repeat iNamed 1.
    iApply wp_terminated'; [done|].
    unfold post_lifting. simpl.
    iIntros (?) "L". iDestruct ("Hpost" with "L") as ">[$ Hpost]".
    iModIntro. simpl.
    iIntros "H". iSpecialize  ("Hpost" with "H"). iNext. iMod "Hpost". iModIntro.
    iSplitL "Hinterp"; [iFrame|].
    iExists _; by iFrame.
  Qed.

  (** * Derived rules *)
  Lemma sswpi_mono' id s Φ Ψ :
    (∀ k, Φ k ⊢ Ψ k) → SSWPi s @ id {{ Φ }} ⊢ SSWPi s @ id {{ Ψ }}.
  Proof.
    iIntros (HΦ) "H"; iApply (sswpi_strong_mono with "H"); auto.
    iIntros (v) "?". by iApply HΦ.
  Qed.

  Lemma wpi_mono' id s Φ Ψ :
    (∀ k, Φ k ⊢ Ψ k) → WPi s @ id {{ Φ }} ⊢ WPi s @ id {{ Ψ }}.
  Proof.
    iIntros (HΦ) "H"; iApply (wpi_mono with "H"); auto.
  Qed.

  Global Instance sswpi_mono'' id s :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) (sswpi id s).
  Proof. by intros Φ Φ' ?; apply sswpi_mono'. Qed.

  Global Instance wpi_mono'' id s :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) (wpi id s).
  Proof. by intros Φ Φ' ?; apply wpi_mono'. Qed.

  Global Instance sswpi_flip_mono' id s :
    Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (sswpi id s).
  Proof. by intros Φ Φ' ?; apply sswpi_mono''. Qed.

  Global Instance wpi_flip_mono' id s :
    Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (wpi id s).
  Proof. by intros Φ Φ' ?; apply wpi_mono''. Qed.

  Lemma sswpi_frame_l id s Φ R :
    R ∗ SSWPi s @ id {{ Φ }} ⊢ SSWPi s @ id {{ k, R ∗ Φ k }}.
  Proof. iIntros "[? H]". iApply (sswpi_strong_mono with "H"); auto with iFrame. Qed.

  Lemma wpi_frame_l id s Φ R :
    R ∗ WPi s @ id {{ Φ }} ⊢ WPi s @ id {{ k, R ∗ Φ k }}.
  Proof. iIntros "[? H]". iApply (wpi_strong_mono with "H"); auto with iFrame. Qed.

  Lemma sswpi_frame_r id s Φ R :
    SSWPi s @ id {{ Φ }} ∗ R ⊢ SSWPi s @ id {{ k, Φ k ∗ R }}.
  Proof. iIntros "[H ?]". iApply (sswpi_strong_mono with "H"); auto with iFrame. Qed.

  Lemma wpi_frame_r id s Φ R :
    WPi s @ id {{ Φ }} ∗ R ⊢ WPi s @ id {{ k, Φ k ∗ R }}.
  Proof. iIntros "[H ?]". iApply (wpi_strong_mono with "H"); auto with iFrame. Qed.

  Lemma sswpi_frame_step_l id s Φ R :
    (|==> R) ∗ SSWPi s @ id {{ Φ }} ⊢ SSWPi s @ id {{ k, R ∗ Φ k }}.
  Proof.
    iIntros "[Hu Hwp]". iApply (sswpi_step_bupd with "Hu"); try done.
    iApply (sswpi_mono with "Hwp"). by iIntros (?) "$$".
  Qed.

  Lemma sswpi_frame_step_l'' id s Φ R :
    (|=i=> R) ∗ SSWPi s @ id {{ Φ }} ⊢ SSWPi s @ id {{ k, R ∗ Φ k }}.
  Proof.
    iIntros "[Hu Hwp]". iApply (sswpi_step_iupd with "Hu"); try done.
    iApply (sswpi_mono with "Hwp"). iIntros (?) "??". iModIntro. iFrame.
  Qed.

  Lemma wpi_frame_step_l id s Φ R :
    (|==> R) ∗ WPi s @ id {{ Φ }} ⊢ WPi s @ id {{ k, R ∗ Φ k }}.
  Proof.
    iIntros "[Hu Hwp]". iApply (wpi_step_bupd with "Hu"); try done.
    iApply (wpi_mono with "Hwp"). by iIntros (?) "$$".
  Qed.

  Lemma wpi_frame_step_l'' id s Φ R :
    (|=i=> R) ∗ WPi s @ id {{ Φ }} ⊢ WPi s @ id {{ k, R ∗ Φ k }}.
  Proof.
    iIntros "[Hu Hwp]". iApply (wpi_step_iupd with "Hu"); try done.
    iApply (wpi_mono with "Hwp"). by iIntros (?) "$$".
  Qed.

  Lemma sswpi_frame_step_r id s Φ R :
    SSWPi s @ id {{ Φ }} ∗ (|==> R) ⊢ SSWPi s @ id {{ k, Φ k ∗ R }}.
  Proof.
    rewrite [(SSWPi _ @ _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
    apply sswpi_frame_step_l.
  Qed.

  Lemma sswpi_frame_step_r'' id s Φ R :
    SSWPi s @ id {{ Φ }} ∗ (|=i=> R) ⊢ SSWPi s @ id {{ k, Φ k ∗ R }}.
  Proof.
    rewrite [(SSWPi _ @ _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
    apply sswpi_frame_step_l''.
  Qed.

  Lemma wpi_frame_step_r id s Φ R :
    WPi s @ id {{ Φ }} ∗ (|==> R) ⊢ WPi s @ id {{ k, Φ k ∗ R }}.
  Proof.
    rewrite [(WPi _ @ _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
    apply wpi_frame_step_l.
  Qed.

  Lemma wpi_frame_step_r'' id s Φ R :
    WPi s @ id {{ Φ }} ∗ (|=i=> R) ⊢ WPi s @ id {{ k, Φ k ∗ R }}.
  Proof.
    rewrite [(WPi _ @ _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
    apply wpi_frame_step_l''.
  Qed.

  Lemma sswpi_frame_step_l' id s Φ R :
    R ∗ SSWPi s @ id {{ Φ }} ⊢ SSWPi s @ id {{ k, R ∗ Φ k }}.
  Proof. iIntros "[??]". iApply (sswpi_frame_step_l id); try iFrame; eauto. Qed.

  Lemma sswpi_frame_step_r' id s Φ R :
    SSWPi s @ id {{ Φ }} ∗ R ⊢ SSWPi s @ id {{ k, Φ k ∗ R }}.
  Proof. iIntros "[??]". iApply (sswpi_frame_step_r id); try iFrame; eauto. Qed.

  Lemma wpi_frame_step_l' id s Φ R :
    R ∗ WPi s @ id {{ Φ }} ⊢ WPi s @ id {{ k, R ∗ Φ k }}.
  Proof. iIntros "[??]". iApply (wpi_frame_step_l id); try iFrame; eauto. Qed.

  Lemma wpi_frame_step_r' id s Φ R :
    WPi s @ id {{ Φ }} ∗ R ⊢ WPi s @ id {{ k, Φ k ∗ R }}.
  Proof. iIntros "[??]". iApply (wpi_frame_step_r id); try iFrame; eauto. Qed.

  Lemma sswpi_wand id s Φ Ψ :
    SSWPi s @ id {{ Φ }} -∗ (∀ k, Φ k -∗ Ψ k) -∗ SSWPi s @ id {{ Ψ }}.
  Proof.
    iIntros "Hwp H". iApply (sswpi_mono with "Hwp"); auto.
  Qed.

  Lemma wpi_wand id s Φ Ψ :
    WPi s @ id {{ Φ }} -∗ (∀ k, Φ k -∗ Ψ k) -∗ WPi s @ id {{ Ψ }}.
  Proof.
    iIntros "Hwp H". iApply (wpi_strong_mono with "Hwp"); auto.
    iIntros (?) "?". by iApply "H".
  Qed.

  Lemma sswpi_wand_l id s Φ Ψ :
    (∀ k, Φ k -∗ Ψ k) ∗ SSWPi s @ id {{ Φ }} ⊢ SSWPi s @ id {{ Ψ }}.
  Proof. iIntros "[H Hwp]". iApply (sswpi_wand with "Hwp H"). Qed.

  Lemma wpi_wand_l id s Φ Ψ :
    (∀ v, Φ v -∗ Ψ v) ∗ WPi s @ id {{ Φ }} ⊢ WPi s @ id {{ Ψ }}.
  Proof. iIntros "[H Hwp]". iApply (wpi_wand with "Hwp H"). Qed.

  Lemma sswpi_wand_r id s Φ Ψ :
    SSWPi s @ id {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ SSWPi s @ id {{ Ψ }}.
  Proof. iIntros "[Hwp H]". iApply (sswpi_wand with "Hwp H"). Qed.

  Lemma wpi_wand_r id s Φ Ψ :
    WPi s @ id {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WPi s @ id {{ Ψ }}.
  Proof. iIntros "[Hwp H]". iApply (wpi_wand with "Hwp H"). Qed.

  Lemma sswpi_frame_wand_l id s Q Φ :
    Q ∗ SSWPi s @ id {{ v, Q -∗ Φ v }} -∗ SSWPi s @ id {{ Φ }}.
  Proof.
    iIntros "[HQ HWPi]". iApply (sswpi_wand with "HWPi").
    iIntros (v) "HΦ". by iApply "HΦ".
  Qed.

  Lemma wpi_frame_wand_l id s Q Φ :
    Q ∗ WPi s @ id {{ v, Q -∗ Φ v }} -∗ WPi s @ id {{ Φ }}.
  Proof.
    iIntros "[HQ HWPi]". iApply (wpi_wand with "HWPi").
    iIntros (v) "HΦ". by iApply "HΦ".
  Qed.

End wpi.

Section proofmode_classes.
  Context `{CMRA Σ}.
  Context `{!invGS_gen HasNoLc Σ}.
  Context `{!irisG}.
  Context `{!irisGL}.
  Context `{!irisGInst}.
  Context `{!Protocol}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : LTSI.t → iProp Σ.
  (* Implicit Types E : coPset. *)
  Implicit Types id : Tid.

  #[global] Instance frame_sswpi p id s R Φ Ψ :
    (∀ k, Frame p R (Φ k) (Ψ k)) →
    Frame p R (SSWPi s @ id {{ Φ }}) (SSWPi s @ id {{ Ψ }}).
  Proof. rewrite /Frame=> HR. rewrite sswpi_frame_l. apply sswpi_mono', HR. Qed.

  #[global] Instance frame_wpi p id s R Φ Ψ :
    (∀ k, Frame p R (Φ k) (Ψ k)) →
    Frame p R (WPi s @ id {{ Φ }}) (WPi s @ id {{ Ψ }}).
  Proof. rewrite /Frame=> HR. rewrite wpi_frame_l. apply wpi_mono', HR. Qed.

  #[global] Instance elim_modal_bupd_sswpi p id s P Φ :
    ElimModal True p false (|==> P) P (SSWPi s @ id {{ Φ }}) (SSWPi s @ id {{ Φ }}).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim
       bupd_frame_r bi.wand_elim_r bupd_sswpi //.
  Qed.

  #[global] Instance elim_modal_iupd_sswpi p id s P Φ :
    ElimModal True p false (|=i=> P) P (SSWPi s @ id {{ Φ }}) (SSWPi s @ id {{ Φ }}).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim
       interp_mod_frame_r bi.wand_elim_r iupd_sswpi //.
  Qed.

  #[global] Instance elim_modal_bupd_wpi p id s P Φ :
    ElimModal True p false (|==> P) P (WPi s @ id {{ Φ }}) (WPi s @ id {{ Φ }}).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim
       bupd_frame_r bi.wand_elim_r bupd_wpi //.
  Qed.

  #[global] Instance elim_modal_iupd_wpi p id s P Φ :
    ElimModal True p false (|=i=> P) P (WPi s @ id {{ Φ }}) (WPi s @ id {{ Φ }}).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim
       interp_mod_frame_r bi.wand_elim_r iupd_wpi //.
  Qed.

  #[global] Instance add_modal_bupd_sswpi id s P Φ :
    AddModal (|==> P) P (SSWPi s @ id {{ Φ }}).
  Proof. rewrite /AddModal bupd_frame_r bi.wand_elim_r bupd_sswpi //. Qed.

  #[global] Instance add_modal_iupd_sswp id s P Φ :
    AddModal (|=i=> P) P (SSWPi s @ id {{ Φ }}).
  Proof. rewrite /AddModal interp_mod_frame_r bi.wand_elim_r iupd_sswpi //. Qed.

  #[global] Instance add_modal_bupd_wpi id s P Φ :
    AddModal (|==> P) P (WPi s @ id {{ Φ }}).
  Proof. rewrite /AddModal bupd_frame_r bi.wand_elim_r bupd_wpi //. Qed.

  #[global] Instance add_modal_iupd_wp id s P Φ :
    AddModal (|=i=> P) P (WPi s @ id {{ Φ }}).
  Proof. rewrite /AddModal interp_mod_frame_r bi.wand_elim_r iupd_wpi //. Qed.

End proofmode_classes.
