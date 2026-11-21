(* Shape_instances.v — the unit-stride store as an instance of the store-shape interface.

   (1) For the unit-stride shape (every listed element active, element l at
       [dst + 8 * idx l, dst + 8 * idx l + 8)) the shape premises hold as soon as idx is injective on
       the listed elements, and `Shape.GenStoreS` coincides with `Normal_instance.GenStore` when every
       element is listed.
   (2) The two existing runs of the running example (ML_instance_2h.v: natural order;
       ML_instance_unord.v: unordered lane writes in each attempt) instantiate `Shape.stage2_shape`
       with that shape. So the earlier results are the unit-stride case of the interface.

   0 Admitted / 0 axioms. Modifies no existing .v file. Coq 8.15. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import RestartV.Frozen_pmp.
Require Import RestartV.Normal_instance.
Require Import RestartV.Shape.
Require RestartV.ML_instance_2h.
Require RestartV.ML_instance_unord.
Import ListNotations.

(* ==================================================================================================
   1. The unit-stride shape
   ================================================================================================== *)

Section UnitShape.

  Variable Lane : Type.
  Variable lanes : list Lane.
  Variable idx : Lane -> nat.
  Variable dst : nat.
  Hypothesis idx_inj : forall l1 l2, In l1 lanes -> In l2 lanes -> idx l1 = idx l2 -> l1 = l2.

  Definition unit_active (_ : Lane) : bool := true.
  Definition unit_lo (l : Lane) : nat := Frozen_pmp.lane_lo dst (idx l).
  Definition unit_hi (l : Lane) : nat := Frozen_pmp.lane_hi dst (idx l).

  Lemma unit_shape_nonempty : forall l, In l lanes -> unit_lo l < unit_hi l.
  Proof. intros l _. unfold unit_lo, unit_hi, Frozen_pmp.lane_lo, Frozen_pmp.lane_hi. lia. Qed.

  Lemma unit_shape_disjoint : forall l1 l2, In l1 lanes -> In l2 lanes ->
      unit_active l1 = true -> unit_active l2 = true -> l1 <> l2 ->
      unit_hi l1 <= unit_lo l2 \/ unit_hi l2 <= unit_lo l1.
  Proof.
    intros l1 l2 H1 H2 _ _ Hne.
    assert (Hi : idx l1 <> idx l2) by (intro E; exact (Hne (idx_inj l1 l2 H1 H2 E))).
    unfold unit_lo, unit_hi, Frozen_pmp.lane_lo, Frozen_pmp.lane_hi.
    assert (H : idx l1 < idx l2 \/ idx l2 < idx l1) by lia.
    destruct H; [left | right]; lia.
  Qed.

  Variable Event Byte Value : Type.
  Variable is_write : Event -> Prop.
  Variable touches : Event -> Byte -> Prop.
  Variable wval : Event -> Byte -> Value.
  Variable lane : Event -> Lane.
  Variable is_lane_write : Event -> Prop.
  Variable vdata : Lane -> Byte -> Value.
  Variable byte_addr : Byte -> nat.
  Hypothesis lanes_complete : forall l : Lane, In l lanes.

  (* with every element listed and active, the shape predicate is the unit-stride predicate *)
  Theorem unit_shape_GenStore_iff : forall C poR addrR dataR ctrlR,
      Shape.GenStoreS Event Byte Value Lane is_write touches wval lane is_lane_write vdata byte_addr
        lanes unit_active unit_lo unit_hi C poR addrR dataR ctrlR
      <-> Normal_instance.GenStore Event Byte Value Lane is_write touches wval lane is_lane_write lanes
            vdata dst idx byte_addr C poR addrR dataR ctrlR.
  Proof.
    intros C poR addrR dataR ctrlR. split.
    - intros [G1 G2 G3 G4 G5 G6 G7 G8]. constructor.
      + intros l Hl. exact (G1 l Hl eq_refl).
      + exact G2.
      + exact G4.
      + exact G5.
      + exact G6.
      + exact G7.
      + exact G8.
    - intros [G1 G2 G4 G5 G6 G7 G8]. constructor.
      + intros l Hl _. exact (G1 l Hl).
      + exact G2.
      + intros w _ _. split; [apply lanes_complete | reflexivity].
      + exact G4.
      + exact G5.
      + exact G6.
      + exact G7.
      + exact G8.
  Qed.

End UnitShape.

(* ==================================================================================================
   1b. A unit-stride shape read off the register state, and its invariance under alpha_regs
   ================================================================================================== *)

Require RestartV.Alpha_regs.

Section RegShape.

  Variable State Value : Type.
  Variable get_base : State -> nat.            (* base address register *)
  Variable get_data : State -> nat -> Value.   (* data vector register *)
  Variable get_vl get_eew : State -> nat.      (* vl and the element width in bits *)
  Variable get_mask : State -> nat -> bool.    (* mask register v0 *)
  Variable H : State -> State.                 (* the handler *)
  Variable Lane : Type.
  Variable idx : Lane -> nat.

  (* element l is active iff its mask bit is set and idx l < vl; it occupies the eew/8 bytes from
     base + (eew/8) * idx l *)
  Definition reg_active (s : State) (l : Lane) : bool :=
    Alpha_regs.lact State get_vl get_mask s (idx l).
  Definition reg_lo (s : State) (l : Lane) : nat := get_base s + (Nat.div (get_eew s) 8) * idx l.
  Definition reg_hi (s : State) (l : Lane) : nat := reg_lo s l + Nat.div (get_eew s) 8.

  (* HEADLINE: a handler satisfying alpha_regs leaves the whole register-derived shape unchanged:
     the replay sees the same active elements at the same byte ranges *)
  Theorem mask_shape_from_regs : forall s,
      Alpha_regs.alpha_regs State nat Value get_base get_data get_vl get_eew get_mask H s ->
      forall l, reg_active (H s) l = reg_active s l /\ reg_lo (H s) l = reg_lo s l /\
                reg_hi (H s) l = reg_hi s l.
  Proof.
    intros s Ha l. assert (Hc := Ha). unfold Alpha_regs.alpha_regs in Hc.
    destruct Hc as [Hb [_ [_ [He _]]]].
    split; [exact (Alpha_regs.replay_lane_active State nat Value get_base get_data get_vl get_eew
                     get_mask H s (idx l) Ha) |].
    unfold reg_hi, reg_lo. rewrite Hb, He. split; reflexivity.
  Qed.

End RegShape.

(* ==================================================================================================
   2. The running example (natural order) through the interface
   ================================================================================================== *)

Module Nat2h.
  Import RestartV.ML_instance_2h.

  Definition ln_eq_dec : forall x y : Ln, {x = y} + {x <> y}.
  Proof. decide equality. Defined.

  Lemma inj : forall l1 l2, In l1 lanes -> In l2 lanes -> lane_index l1 = lane_index l2 -> l1 = l2.
  Proof. exact s_inj. Qed.

  Lemma one_active : forall l, In l lanes -> unit_active Ln l = true ->
      exists w, In w (Shape.E_K Ev ev_eq_dec E0 LS Ctx ctx_dec) /\ is_lane_write w /\ lane w = l /\
                (forall w', In w' (Shape.E_K Ev ev_eq_dec E0 LS Ctx ctx_dec) -> is_lane_write w' ->
                            lane w' = l -> w' = w).
  Proof. intros l Hl _. exact (s_one_write_per_lane l Hl). Qed.

  Lemma writes_active : forall w, In w (Shape.E_K Ev ev_eq_dec E0 LS Ctx ctx_dec) -> is_lane_write w ->
      In (lane w) lanes /\ unit_active Ln (lane w) = true.
  Proof. intros w _ _. split; [apply s_complete | reflexivity]. Qed.

  Lemma foot : forall e b, In e (Shape.E_K Ev ev_eq_dec E0 LS Ctx ctx_dec) -> is_lane_write e ->
      (touches e b <-> unit_lo Ln lane_index 64 (lane e) <= byte_addr b /\
                       byte_addr b < unit_hi Ln lane_index 64 (lane e)).
  Proof. intros e b He Hl. exact (s_footprint e (lane e) b He Hl eq_refl). Qed.

  Lemma bg : forall l, In l lanes -> unit_active Ln l = true ->
      0 <= unit_lo Ln lane_index 64 l /\ unit_hi Ln lane_index 64 l <= 1000.
  Proof. intros l _ _. unfold unit_lo, unit_hi. apply s_bg. destruct l; simpl; lia. Qed.

  Definition pos_before :=
    Normal_instance.position_before Ev ev_eq_dec nat hart E0 po LS Ctx ctx_dec is_chk chk_dec
      is_lane_write n_po_hart n_po_total n_inst_hart n_window.
  Definition pos_after :=
    Normal_instance.position_after Ev ev_eq_dec nat hart E0 po LS Ctx ctx_dec is_chk chk_dec
      is_lane_write n_po_hart n_po_total n_inst_hart n_window.

  Definition ml2_stage2_shape_instance :=
    Shape.stage2_shape Ev ev_eq_dec Lb nat nat Ln ln_eq_dec gmo is_write is_read is_read is_write
      touches wval same_addr addr data ctrl fence hart E0 rf po poloc LS Ctx ctx_dec is_chk chk_dec
      lane is_lane_write vdata byte_addr lanes (unit_active Ln) (unit_lo Ln lane_index 64)
      (unit_hi Ln lane_index 64)
      h_Hirr h_Htr h_Htot h_potrans h_rfC4 h_rftouch h_rffun s_lanes h_keep Hpb2 Hfrf
      s_rf_src s_rf_tgt s_ctx_silent s_chk_nonmem h_rwdisj s_lane_write_is_write
      one_active writes_active foot n_value n_deps
      ln1 0 1000
      (unit_shape_nonempty Ln lanes lane_index 64)
      (unit_shape_disjoint Ln lanes lane_index 64 inj)
      (s_complete ln1) eq_refl bg
      pos_before pos_after.
End Nat2h.

(* ==================================================================================================
   3. The variant with unordered lane writes through the interface
   ================================================================================================== *)

Module Unord.
  Import RestartV.ML_instance_unord.

  Definition ln_eq_dec : forall x y : Ln, {x = y} + {x <> y}.
  Proof. decide equality. Defined.

  Lemma one_active : forall l, In l lanes -> unit_active Ln l = true ->
      exists w, In w (Shape.E_K Ev ev_eq_dec E0 LS Ctx ctx_dec) /\ is_lane_write w /\ lane w = l /\
                (forall w', In w' (Shape.E_K Ev ev_eq_dec E0 LS Ctx ctx_dec) -> is_lane_write w' ->
                            lane w' = l -> w' = w).
  Proof. intros l Hl _. exact (s_one_write_per_lane l Hl). Qed.

  Lemma writes_active : forall w, In w (Shape.E_K Ev ev_eq_dec E0 LS Ctx ctx_dec) -> is_lane_write w ->
      In (lane w) lanes /\ unit_active Ln (lane w) = true.
  Proof. intros w _ _. split; [apply s_complete | reflexivity]. Qed.

  Lemma foot : forall e b, In e (Shape.E_K Ev ev_eq_dec E0 LS Ctx ctx_dec) -> is_lane_write e ->
      (touches e b <-> unit_lo Ln lane_index 64 (lane e) <= byte_addr b /\
                       byte_addr b < unit_hi Ln lane_index 64 (lane e)).
  Proof. intros e b He Hl. exact (s_footprint e (lane e) b He Hl eq_refl). Qed.

  Lemma bg : forall l, In l lanes -> unit_active Ln l = true ->
      0 <= unit_lo Ln lane_index 64 l /\ unit_hi Ln lane_index 64 l <= 1000.
  Proof. intros l _ _. unfold unit_lo, unit_hi. apply s_bg. destruct l; simpl; lia. Qed.

  Definition mu_stage2_shape_instance :=
    Shape.stage2_shape Ev ev_eq_dec Lb nat nat Ln ln_eq_dec gmo is_write is_read is_read is_write
      touches wval same_addr addr data ctrl fence hart E0 rf po poloc LS Ctx ctx_dec is_chk chk_dec
      lane is_lane_write vdata byte_addr lanes (unit_active Ln) (unit_lo Ln lane_index 64)
      (unit_hi Ln lane_index 64)
      h_Hirr h_Htr h_Htot h_potrans h_rfC4 h_rftouch h_rffun s_lanes h_keep Hpb2 Hfrf
      s_rf_src s_rf_tgt s_ctx_silent s_chk_nonmem h_rwdisj s_lane_write_is_write
      one_active writes_active foot n_value n_deps
      ln1 0 1000
      (unit_shape_nonempty Ln lanes lane_index 64)
      (unit_shape_disjoint Ln lanes lane_index 64 s_inj)
      (s_complete ln1) eq_refl bg
      n_position_before n_position_after.
End Unord.
