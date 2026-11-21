(* Gmo_instances.v — the gmo-form contraction theorem on the running example and on the
   masked run. Every premise of `Gmo_consistency.ML_T1_gmo` is discharged, in particular that the
   faulting run's preserved program order is contained in its global memory order.

   0 Admitted / 0 axioms. Modifies no existing .v file. Coq 8.15. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import RestartV.Frozen_mainmodel.
Require Import RestartV.PPO_union.
Require Import RestartV.Gmo_consistency.
Require Import RestartV.Gmo_counterpart.
Require RestartV.L1_abstract_erasure RestartV.Normal_instance RestartV.ML_T1.
Require RestartV.ML_instance_2h.
Require RestartV.ML_instance_masked.
Import ListNotations.

Module Nat2hGmo.
  Import RestartV.ML_instance_2h.

  Lemma ppo_gmo : forall x y,
      Frozen_mainmodel.fault_ppo Ev Lb is_write is_read is_read is_write touches same_addr addr data
        ctrl fence E0 rf po x y -> In x E0 /\ In y E0 /\ gmo x y.
  Proof.
    intros x y H. split; [apply all_in_E0 |]. split; [apply all_in_E0 |]. unfold gmo.
    destruct H as [Hp | [bx Hr2]].
    - exact (ppoF_rank x y Hp).
    - unfold PPO_union.r2F, PPO_union.polnw_F in Hr2.
      destruct Hr2 as [[_ [_ [_ [_ [Hpo _]]]]] _]. exact (proj1 Hpo).
  Qed.

  Lemma rf_in : forall w b r, rf w b r -> In r E0.
  Proof. intros. apply all_in_E0. Qed.

  Definition ml2_T1_gmo_instance :=
    Gmo_consistency.ML_T1_gmo Ev ev_eq_dec Lb nat nat gmo is_write is_read is_read is_write touches
      wval same_addr addr data ctrl fence hart E0 rf po LS
      h_Hirr h_Htr h_Htot h_potrans h_rfC4 ppo_gmo rf_in s_rf_tgt h_rwdisj n_po_hart
      h_rffun s_lanes h_keep.


  Theorem ml2_gen_ppo_in_gmo : forall a b,
      Normal_instance.ppow_G Ev Lb is_write is_read is_read is_write touches same_addr addr data ctrl
        fence E0 rf po LS is_lane_write a b -> gmo a b.
  Proof.
    exact (Gmo_counterpart.gen_ppo_in_gmo Ev ev_eq_dec Lb nat nat gmo is_write is_read is_read is_write
             touches wval same_addr addr data ctrl fence hart E0 rf po LS is_lane_write
             h_Hirr h_Htr h_Htot h_potrans h_rfC4 ppo_gmo rf_in s_rf_tgt h_rwdisj n_po_hart
             h_rffun s_lanes h_keep s_lane_write_is_write).
  Qed.

  Theorem ml2_gen_load_value :
    L1_abstract_erasure.L1_consistent Ev Lb is_write is_read touches gmo
      (Normal_instance.po_G Ev po is_lane_write)
      (Normal_instance.E_MK Ev ev_eq_dec E0 LS Ctx ctx_dec is_chk chk_dec) (ML_T1.rfL Ev Lb rf LS).
  Proof.
    exact (Gmo_counterpart.gen_load_value Ev ev_eq_dec Lb nat nat gmo is_write is_read is_read is_write
             touches wval same_addr addr data ctrl fence hart E0 rf po LS Ctx ctx_dec is_chk chk_dec
             is_lane_write h_Hirr h_Htr h_Htot h_potrans h_rfC4 ppo_gmo rf_in s_rf_tgt h_rwdisj
             n_po_hart h_rffun s_lanes h_keep s_ctx_silent s_chk_nonmem s_lane_write_is_write).
  Qed.
End Nat2hGmo.

Module MaskedGmo.
  Import RestartV.ML_instance_masked.

  Lemma ppo_gmo : forall x y,
      Frozen_mainmodel.fault_ppo Ev Lb is_write is_read is_read is_write touches same_addr addr data
        ctrl fence E0 rf po x y -> In x E0 /\ In y E0 /\ gmo x y.
  Proof.
    intros x y H. split; [apply all_in_E0 |]. split; [apply all_in_E0 |]. unfold gmo.
    destruct H as [Hp | [bx Hr2]].
    - exact (ppoF_rank x y Hp).
    - unfold PPO_union.r2F, PPO_union.polnw_F in Hr2.
      destruct Hr2 as [[_ [_ [_ [_ [Hpo _]]]]] _]. exact (proj1 Hpo).
  Qed.

  Lemma rf_in : forall w b r, rf w b r -> In r E0.
  Proof. intros. apply all_in_E0. Qed.

  Definition mk_T1_gmo_instance :=
    Gmo_consistency.ML_T1_gmo Ev ev_eq_dec Lb nat nat gmo is_write is_read is_read is_write touches
      wval same_addr addr data ctrl fence hart E0 rf po LS
      h_Hirr h_Htr h_Htot h_potrans h_rfC4 ppo_gmo rf_in s_rf_tgt h_rwdisj n_po_hart
      h_rffun s_lanes h_keep.


  Theorem mk_gen_ppo_in_gmo : forall a b,
      Normal_instance.ppow_G Ev Lb is_write is_read is_read is_write touches same_addr addr data ctrl
        fence E0 rf po LS is_lane_write a b -> gmo a b.
  Proof.
    exact (Gmo_counterpart.gen_ppo_in_gmo Ev ev_eq_dec Lb nat nat gmo is_write is_read is_read is_write
             touches wval same_addr addr data ctrl fence hart E0 rf po LS is_lane_write
             h_Hirr h_Htr h_Htot h_potrans h_rfC4 ppo_gmo rf_in s_rf_tgt h_rwdisj n_po_hart
             h_rffun s_lanes h_keep s_lane_write_is_write).
  Qed.

  Theorem mk_gen_load_value :
    L1_abstract_erasure.L1_consistent Ev Lb is_write is_read touches gmo
      (Normal_instance.po_G Ev po is_lane_write)
      (Normal_instance.E_MK Ev ev_eq_dec E0 LS Ctx ctx_dec is_chk chk_dec) (ML_T1.rfL Ev Lb rf LS).
  Proof.
    exact (Gmo_counterpart.gen_load_value Ev ev_eq_dec Lb nat nat gmo is_write is_read is_read is_write
             touches wval same_addr addr data ctrl fence hart E0 rf po LS Ctx ctx_dec is_chk chk_dec
             is_lane_write h_Hirr h_Htr h_Htot h_potrans h_rfC4 ppo_gmo rf_in s_rf_tgt h_rwdisj
             n_po_hart h_rffun s_lanes h_keep s_ctx_silent s_chk_nonmem s_lane_write_is_write).
  Qed.
End MaskedGmo.
