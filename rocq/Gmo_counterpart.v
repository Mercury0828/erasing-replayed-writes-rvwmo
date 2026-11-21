(* Gmo_counterpart.v — the trap-free counterpart G in RVWMO's own (gmo) form.

   G (Normal_instance.v) keeps the memory kernel E_MK of the faulting run (replays, trap region and
   PMP checks erased), with the reads-from of the contraction and program order po_G (the faulting
   run's program order without the pairs of two element writes). This file shows that G, with the
   faulting run's gmo restricted to E_MK, is RVWMO-consistent in the gmo form whenever the faulting run
   is: its preserved program order is contained in gmo (`gen_ppo_in_gmo`), and gmo is a strict total
   order on E_MK under which every read obeys the load-value axiom with po_G (`gen_load_value`).

   0 Admitted / 0 axioms. Modifies no existing .v file. Coq 8.15. *)

Require Import Coq.Lists.List.
Require Import Coq.Relations.Relations.
Require Import RestartV.L1_abstract_erasure.
Require Import RestartV.Frozen_mainmodel.
Require Import RestartV.Ctx_erasure.
Require Import RestartV.Stage2_normal_candidate.
Require Import RestartV.ML_base.
Require Import RestartV.ML_T1.
Require Import RestartV.ML_stage2.
Require Import RestartV.Perbyte.
Require Import RestartV.Normal_instance.
Require Import RestartV.Gmo_consistency.

Section GmoCounterpart.

  Variable Event : Type.
  Variable eq_ev_dec : forall x y : Event, {x = y} + {x <> y}.
  Variable Byte Hart Value : Type.
  Variable gmo : Event -> Event -> Prop.
  Variable is_write is_read is_load is_store : Event -> Prop.
  Variable touches : Event -> Byte -> Prop.
  Variable wval : Event -> Byte -> Value.
  Variable same_addr addr data ctrl fence : Event -> Event -> Prop.
  Variable hart : Event -> Hart.
  Variable E0 : list Event.
  Variable rf : Event -> Byte -> Event -> Prop.
  Variable po : Event -> Event -> Prop.
  Variable LS : list (Event * Event).
  Variable Ctx : Event -> Prop.
  Variable ctx_dec : forall e, {Ctx e} + {~ Ctx e}.
  Variable is_chk : Event -> Prop.
  Variable chk_dec : forall e, {is_chk e} + {~ is_chk e}.
  Variable is_lane_write : Event -> Prop.

  (* the faulting execution is RVWMO-consistent in the gmo form (as in Gmo_consistency) *)
  Hypothesis Hirr : forall e, In e E0 -> ~ gmo e e.
  Hypothesis Htr  : forall a b c, In a E0 -> In b E0 -> In c E0 -> gmo a b -> gmo b c -> gmo a c.
  Hypothesis Htot : forall a b, In a E0 -> In b E0 -> a <> b -> gmo a b \/ gmo b a.
  Hypothesis Hpo_trans : forall a b c, po a b -> po b c -> po a c.
  Hypothesis rf_is_C4 : forall b r w, is_read r -> In r E0 -> rf w b r ->
      L1_abstract_erasure.C4_source Event Byte is_write touches gmo po E0 b r w.
  Hypothesis Hppo_gmo : forall x y,
      Frozen_mainmodel.fault_ppo Event Byte is_write is_read is_load is_store touches same_addr addr
        data ctrl fence E0 rf po x y ->
      In x E0 /\ In y E0 /\ gmo x y.
  Hypothesis rf_in_E0 : forall w b r, rf w b r -> In r E0.
  Hypothesis rf_tgt_read : forall w b r, rf w b r -> is_read r.
  Hypothesis Hrw : forall e, is_read e -> is_write e -> False.
  Hypothesis Hpo_hart : forall a b, po a b -> hart a = hart b.
  Hypothesis rf_functional : forall w1 w2 x r, rf w1 x r -> rf w2 x r -> w1 = w2.
  Hypothesis Hlanes : forall k d, In (k, d) LS ->
    ML_T1.LaneOK Event Byte Hart Value gmo is_write is_read touches wval addr data hart E0 rf po k d.
  Hypothesis keeper_survives : forall k d, In (k, d) LS -> ~ ML_T1.isdelL Event LS k.
  (* the trap region and the checks are memory-silent; element writes are writes *)
  Hypothesis Hctx_silent :
    forall e, Ctx e -> (~ is_read e) /\ (~ is_write e) /\ (forall b, ~ touches e b).
  Hypothesis Hchk_nonmem :
    forall e, is_chk e -> (~ is_read e) /\ (~ is_write e) /\ (forall b, ~ touches e b).
  Hypothesis Hlane_write_is_write : forall e, is_lane_write e -> is_write e.

  Definition E_C := ML_T1.E_L Event eq_ev_dec E0 LS.
  Definition E_MK := Normal_instance.E_MK Event eq_ev_dec E0 LS Ctx ctx_dec is_chk chk_dec.
  Definition rf_C := ML_T1.rfL Event Byte rf LS.
  Definition po_G := Normal_instance.po_G Event po is_lane_write.

  (* membership in the memory kernel *)
  Lemma In_E_MK : forall e, In e E_MK <-> In e E_C /\ ~ Ctx e /\ ~ is_chk e.
  Proof.
    intro e. unfold E_MK, Normal_instance.E_MK, Perbyte.E_MK, Stage2_normal_candidate.mem_kernel,
               Perbyte.E_K, ML_stage2.E_K, Ctx_erasure.EK.
    rewrite filter_In. rewrite filter_In.
    destruct (chk_dec e) as [C | NC]; destruct (ctx_dec e) as [X | NX].
    - split; [intros [[_ H] _]; discriminate H | intros [_ [N _]]; contradiction].
    - split; [intros [_ H]; discriminate H | intros [_ [_ N]]; contradiction].
    - split; [intros [[_ H] _]; discriminate H | intros [_ [N _]]; contradiction].
    - split.
      + intros [[H _] _]. split; [exact H |]. split; assumption.
      + intros [H _]. split; [split; [exact H | reflexivity] | reflexivity].
  Qed.

  Lemma E_C_sub_E0 : forall e, In e E_C -> In e E0.
  Proof. exact (ML_stage2.E_C_sub_E0 Event eq_ev_dec E0 LS). Qed.

  (* HEADLINE 1: G's preserved program order is contained in gmo *)
  Theorem gen_ppo_in_gmo : forall a b,
      Normal_instance.ppow_G Event Byte is_write is_read is_load is_store touches same_addr addr data
        ctrl fence E0 rf po LS is_lane_write a b -> gmo a b.
  Proof.
    intros a b H.
    apply (proj1 (Gmo_consistency.ML_T1_gmo Event eq_ev_dec Byte Hart Value gmo is_write is_read
                    is_load is_store touches wval same_addr addr data ctrl fence hart E0 rf po LS
                    Hirr Htr Htot Hpo_trans rf_is_C4 Hppo_gmo rf_in_E0 rf_tgt_read Hrw Hpo_hart
                    rf_functional Hlanes keeper_survives)).
    exact (Normal_instance.ppow_G_sub Event Byte is_write is_read is_load is_store touches same_addr addr
             data ctrl fence E0 rf po LS is_lane_write Hrw Hlane_write_is_write a b H).
  Qed.

  (* HEADLINE 2: the load-value axiom of G over gmo and po_G, on the memory kernel *)
  Theorem gen_load_value :
    L1_abstract_erasure.L1_consistent Event Byte is_write is_read touches gmo po_G E_MK rf_C.
  Proof.
    pose proof (Gmo_consistency.ML_T1_gmo Event eq_ev_dec Byte Hart Value gmo is_write is_read
                  is_load is_store touches wval same_addr addr data ctrl fence hart E0 rf po LS
                  Hirr Htr Htot Hpo_trans rf_is_C4 Hppo_gmo rf_in_E0 rf_tgt_read Hrw Hpo_hart
                  rf_functional Hlanes keeper_survives) as [_ [[_ C4C] _]].
    assert (Hsub : forall e, In e E_MK -> In e E0)
      by (intros e He; exact (E_C_sub_E0 e (proj1 (proj1 (In_E_MK e) He)))).
    constructor.
    - split; [intros e He; exact (Hirr e (Hsub e He)) |].
      split; [intros a b c Ha Hb Hc; exact (Htr a b c (Hsub a Ha) (Hsub b Hb) (Hsub c Hc)) |].
      intros a b Ha Hb; exact (Htot a b (Hsub a Ha) (Hsub b Hb)).
    - intros b r w Rr Ir Hrf.
      destruct (proj1 (In_E_MK r) Ir) as [IrC _].
      destruct (C4C b r w Rr IrC Hrf) as [[IwC [Ww [Tw Ord]]] Hlatest].
      split.
      + split; [| split; [exact Ww | split; [exact Tw |]]].
        * apply (proj2 (In_E_MK w)). split; [exact IwC |].
          split; [intro X; exact (proj1 (proj2 (Hctx_silent w X)) Ww)
                 | intro X; exact (proj1 (proj2 (Hchk_nonmem w X)) Ww)].
        * destruct Ord as [G | P]; [left; exact G | right].
          split; [exact P |]. intros [_ Lr]. exact (Hrw r Rr (Hlane_write_is_write r Lr)).
      + intros w' [Iw' [Ww' [Tw' Ord']]]. apply Hlatest.
        split; [exact (proj1 (proj1 (In_E_MK w') Iw')) |].
        split; [exact Ww' |]. split; [exact Tw' |].
        destruct Ord' as [G | [P _]]; [left; exact G | right; exact P].
  Qed.

End GmoCounterpart.
