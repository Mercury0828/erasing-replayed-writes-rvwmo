(* Gmo_consistency.v — the contraction theorem in RVWMO's own (global-memory-order) form.

   RVWMO defines consistency through a strict total global memory order gmo: preserved program order
   is contained in gmo, and every read obeys the load-value axiom over gmo and program order (the
   atomicity axiom is vacuous without AMOs and LR/SC, and progress is automatic for finite executions).
   The development states the contraction theorem with the graph checks (per byte, and the main-model
   acyclicity). This file connects the two forms:

     * `FRfF_in_gmo`: if the faulting execution is RVWMO-consistent in the gmo form, every edge of its
       main-model relation co | fr | rfe | ppo goes forward in gmo; so its main-model check holds
       (`fault_main_from_gmo`);
     * `ML_T1_gmo`: the erased execution, with the SAME gmo restricted to its events, is again
       RVWMO-consistent in the gmo form: its preserved program order is contained in gmo, and the
       load-value axiom holds over gmo and program order.

   0 Admitted / 0 axioms. Modifies no existing .v file. Coq 8.15. *)

Require Import Coq.Lists.List.
Require Import Coq.Relations.Relations.
Require Import RestartV.L1_abstract_erasure.
Require Import RestartV.Rlift_mainmodel.
Require Import RestartV.Frozen_mainmodel.
Require Import RestartV.ML_base.
Require Import RestartV.ML_T1.

Section GmoConsistency.

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

  (* ---- the faulting execution is RVWMO-consistent in the gmo form ---- *)
  Hypothesis Hirr : forall e, In e E0 -> ~ gmo e e.
  Hypothesis Htr  : forall a b c, In a E0 -> In b E0 -> In c E0 -> gmo a b -> gmo b c -> gmo a c.
  Hypothesis Htot : forall a b, In a E0 -> In b E0 -> a <> b -> gmo a b \/ gmo b a.
  Hypothesis Hpo_trans : forall a b c, po a b -> po b c -> po a c.
  (* the load-value axiom *)
  Hypothesis rf_is_C4 : forall b r w, is_read r -> In r E0 -> rf w b r ->
      L1_abstract_erasure.C4_source Event Byte is_write touches gmo po E0 b r w.
  (* preserved program order is contained in gmo *)
  Hypothesis Hppo_gmo : forall x y,
      Frozen_mainmodel.fault_ppo Event Byte is_write is_read is_load is_store touches same_addr addr
        data ctrl fence E0 rf po x y ->
      In x E0 /\ In y E0 /\ gmo x y.
  (* well-formedness *)
  Hypothesis rf_in_E0 : forall w b r, rf w b r -> In r E0.
  Hypothesis rf_tgt_read : forall w b r, rf w b r -> is_read r.
  Hypothesis Hrw : forall e, is_read e -> is_write e -> False.
  Hypothesis Hpo_hart : forall a b, po a b -> hart a = hart b.
  (* ---- the pair premises of the contraction theorem ---- *)
  Hypothesis rf_functional : forall w1 w2 x r, rf w1 x r -> rf w2 x r -> w1 = w2.
  Hypothesis Hlanes : forall k d, In (k, d) LS ->
    ML_T1.LaneOK Event Byte Hart Value gmo is_write is_read touches wval addr data hart E0 rf po k d.
  Hypothesis keeper_survives : forall k d, In (k, d) LS -> ~ ML_T1.isdelL Event LS k.

  Definition FRfF := ML_T1.FRfF Event Byte Hart gmo is_write is_read is_load is_store touches same_addr
                       addr data ctrl fence hart E0 rf po.

  (* every main-model edge of the faulting run goes forward in gmo, between events of the run *)
  Lemma FRfF_in_gmo : forall x y, FRfF x y -> In x E0 /\ In y E0 /\ gmo x y.
  Proof.
    intros x y H. unfold FRfF, ML_T1.FRfF, Frozen_mainmodel.FRf, Rlift_mainmodel.Rf in H.
    destruct H as [[b Hco] | [[b [Rx Hfr]] | [Hrfe | Hppo]]].
    - unfold Rlift_mainmodel.co_flt, Rlift_mainmodel.coOn, Rlift_mainmodel.inE0 in Hco.
      destruct Hco as [Ix [Iy [_ [_ [_ [_ G]]]]]]. auto.
    - (* x reads b from w1, w1 is co-before y: x must be gmo-before y *)
      destruct Hfr as [w1 [Hrf Hco]].
      unfold Rlift_mainmodel.co_flt, Rlift_mainmodel.coOn, Rlift_mainmodel.inE0 in Hco.
      destruct Hco as [Iw1 [Iy [Ww1 [Wy [Tw1 [Ty G1y]]]]]].
      assert (Ix : In x E0) by exact (rf_in_E0 w1 b x Hrf).
      split; [exact Ix |]. split; [exact Iy |].
      assert (Hne : x <> y) by (intro E; subst; exact (Hrw y Rx Wy)).
      destruct (Htot x y Ix Iy Hne) as [G | G]; [exact G |].
      exfalso. destruct (rf_is_C4 b x w1 Rx Ix Hrf) as [_ Hlatest].
      destruct (Hlatest y (conj Iy (conj Wy (conj Ty (or_introl G))))) as [E | Gy1].
      + rewrite E in G1y. exact (Hirr w1 Iw1 G1y).
      + exact (Hirr y Iy (Htr y w1 y Iy Iw1 Iy Gy1 G1y)).
    - (* an external read takes its value from a write that is gmo-before it *)
      destruct Hrfe as [b [Hrf Hext]].
      assert (Iy : In y E0) by exact (rf_in_E0 x b y Hrf).
      destruct (rf_is_C4 b y x (rf_tgt_read x b y Hrf) Iy Hrf) as [[Ix [_ [_ [G | P]]]] _].
      + auto.
      + exfalso. exact (Hext (Hpo_hart x y P)).
    - exact (Hppo_gmo x y Hppo).
  Qed.

  (* hence the faulting run passes the main-model check *)
  Theorem fault_main_from_gmo : forall x, ~ clos_trans Event FRfF x x.
  Proof.
    assert (Hct : forall x y, clos_trans Event FRfF x y -> In x E0 /\ In y E0 /\ gmo x y).
    { intros x y H. induction H as [x y Hxy | x y z _ [Ix [Iy G1]] _ [_ [Iz G2]]].
      - exact (FRfF_in_gmo x y Hxy).
      - split; [exact Ix |]. split; [exact Iz |]. exact (Htr x y z Ix Iy Iz G1 G2). }
    intros x H. destruct (Hct x x H) as [Ix [_ G]]. exact (Hirr x Ix G).
  Qed.

  (* HEADLINE: the erased execution is RVWMO-consistent in the gmo form, with the same gmo:
     its preserved program order is contained in gmo, and the load-value axiom holds *)
  Theorem ML_T1_gmo :
    (forall x y, ML_T1.ppo_wit_L Event Byte is_write is_read is_load is_store touches same_addr addr
                   data ctrl fence E0 rf po LS x y -> gmo x y)
    /\ L1_abstract_erasure.L1_consistent Event Byte is_write is_read touches gmo po
         (ML_T1.E_L Event eq_ev_dec E0 LS) (ML_T1.rfL Event Byte rf LS)
    /\ (forall x, ~ clos_trans Event FRfF x x).
  Proof.
    split; [| split].
    - intros x y H.
      exact (proj2 (proj2 (FRfF_in_gmo x y
               (ML_T1.ppo_wit_L_lifts Event eq_ev_dec Byte Hart Value gmo is_write is_read is_load
                  is_store touches wval same_addr addr data ctrl fence hart E0 rf po LS rf_functional
                  Hlanes keeper_survives x y H)))).
    - exact (ML_T1.ML_erasure_preserves_consistency Event eq_ev_dec Byte Hart Value gmo is_write is_read
               touches wval addr data hart E0 rf po LS Hirr Htr Htot Hpo_trans rf_is_C4 Hlanes
               keeper_survives).
    - exact fault_main_from_gmo.
  Qed.

End GmoConsistency.
