(* ML_instance_masked.v — a MASKED unit-stride vector store, a second complete instance.

   Hart 0 executes a masked vse64.v with VL = 4 and mask v0 = (1,1,0,1): element 2 is masked off.
   Element 1 faults on its PMP check. Before the trap hart 0 writes element 0 (W0) and, early, the
   active element 3 (K3). The handler repairs the PMP entry and returns; the replay from vstart = 1
   writes element 1 (F1) and element 3 again (D3). Element 2 is never written, in either attempt.
   Hart 1 reads element 2 (R2) and element 3 (R3); hart 2 holds the initial writes (Wi2, Wi3). One byte
   stands for each element, as in ML_instance_2h.v.

   The activity of an element is read off the register state: s_active l = Alpha_regs.lact s0 (idx l)
   = mask bit && idx l < vl (`mk_active_from_regs`), and a handler that satisfies alpha_regs leaves it
   unchanged (`mk_replay_same_active`). The file proves every premise of the per-byte contraction
   theorem (`Perbyte.ML_T1_refinement_pb`) and of the shape counterpart (`Shape.stage2_shape`) for this
   run, with the masked shape, and applies both:

     * mk_T1_pb_instance          the contraction theorem on the masked run, pair list [(K3, D3)];
     * mk_stage2_shape_instance   the trap-free counterpart: Stage-2 chain over the active elements
                                  [0;1;3], generation by one masked execution (no write of element 2),
                                  both checks of G, and the PMP conclusion for the active elements;
     * mk_instance_observation    after erasure R2 still reads 0 (the masked-off element keeps its
                                  old value), R3 still reads 6, and the final values are 0 and 6;
     * mk_shape_not_unit          element 2 is listed but inactive, so this is not the unit-stride
                                  instance.

   0 Admitted / 0 axioms. Modifies no existing .v file. Coq 8.15. *)

Require Import Coq.Lists.List.
Require Import Coq.Relations.Relations.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import RestartV.L1_abstract_erasure.
Require Import RestartV.Clift_coherence.
Require Import RestartV.Rlift_mainmodel.
Require Import RestartV.PPO_union.
Require Import RestartV.Frozen_mainmodel.
Require Import RestartV.Obs_final_state.
Require Import RestartV.Ctx_erasure.
Require Import RestartV.Frozen_pmp.
Require Import RestartV.ML_base.
Require Import RestartV.ML_T1.
Require Import RestartV.Perbyte.
Require Import RestartV.Normal_instance.
Require Import RestartV.Alpha_regs.
Require Import RestartV.Shape.
Require Import RestartV.Shape_instances.
Import ListNotations.

(* ============================ the register state and the mask ============================ *)

Record St := mkSt { base : nat; dat : nat -> nat; vl : nat; eew : nat; mask : nat -> bool;
                    vstart : nat; pmp_w : bool }.

(* the state at the cut, just before the faulting instruction: VL = 4, mask (1,1,0,1) *)
Definition s0 : St :=
  mkSt 64 (fun i => match i with 0 => 4 | 1 => 1 | 2 => 9 | _ => 6 end) 4 64
       (fun i => match i with 2 => false | _ => true end) 0 false.

(* the handler: repairs the PMP entry, records vstart = 1, touches no input of the store *)
Definition Hdl (s : St) : St :=
  mkSt (base s) (dat s) (vl s) (eew s) (mask s) 1 true.

Lemma mk_alpha_regs : Alpha_regs.alpha_regs St nat nat base dat vl eew mask Hdl s0.
Proof. unfold Alpha_regs.alpha_regs. simpl. repeat split; intros; reflexivity. Qed.

(* ============================ the concrete model ============================ *)

Inductive Ev := Wi2 | Wi3 | W0 | K3 | Tr | Xr | F1 | D3 | R2 | R3.
Inductive Lb := L0 | L1 | L2 | L3.          (* one byte per element footprint *)

Definition ev_eq_dec : forall x y : Ev, {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition rank (e : Ev) : nat :=
  match e with
  | Wi2 => 0 | Wi3 => 1 | W0 => 2 | K3 => 3 | Tr => 4 | Xr => 5 | F1 => 6 | D3 => 7
  | R2 => 8 | R3 => 9
  end.

Definition hart (e : Ev) : nat :=
  match e with R2 | R3 => 1 | Wi2 | Wi3 => 2 | _ => 0 end.
Definition po  (a b : Ev) : Prop := rank a < rank b /\ hart a = hart b.
Definition gmo (a b : Ev) : Prop := rank a < rank b.

Definition is_write (e : Ev) : Prop :=
  match e with Wi2 | Wi3 | W0 | K3 | F1 | D3 => True | _ => False end.
Definition is_read (e : Ev) : Prop := match e with R2 | R3 => True | _ => False end.

Definition touches (e : Ev) (b : Lb) : Prop :=
  match e, b with
  | Wi2, L2 | R2, L2 => True
  | Wi3, L3 | K3, L3 | D3, L3 | R3, L3 => True
  | W0, L0 | F1, L1 => True
  | _, _ => False
  end.

Definition wval (e : Ev) (_ : Lb) : nat :=
  match e with K3 | D3 => 6 | W0 => 4 | F1 => 1 | _ => 0 end.

Definition rf (w : Ev) (b : Lb) (r : Ev) : Prop :=
  match w, b, r with
  | Wi2, L2, R2 | D3, L3, R3 => True
  | _, _, _ => False
  end.

Definition addr (_ _ : Ev) : Prop := False.
Definition data (_ _ : Ev) : Prop := False.
Definition ctrl (_ _ : Ev) : Prop := False.
Definition fence (_ _ : Ev) : Prop := False.
Definition same_addr (a b : Ev) : Prop := exists x, touches a x /\ touches b x.
Definition poloc (a b : Ev) : Prop := po a b /\ same_addr a b.

Definition E0 : list Ev := [Wi2; Wi3; W0; K3; Tr; Xr; F1; D3; R2; R3].
Definition LS : list (Ev * Ev) := [(K3, D3)].     (* the one early active element *)

Ltac inE0tac := unfold E0; simpl; repeat (first [ left; reflexivity | right ]).

Lemma all_in_E0 : forall e, In e E0.
Proof. intro e; destruct e; inE0tac. Qed.

(* ============================ the two acyclicity certificates ============================ *)

Lemma ct_rank : forall (R : Ev -> Ev -> Prop),
  (forall x y, R x y -> rank x < rank y) ->
  forall x y, clos_trans Ev R x y -> rank x < rank y.
Proof. intros R Hedge x y Hct. induction Hct; [apply Hedge; assumption | lia]. Qed.

Lemma acyc_from_rank : forall (R : Ev -> Ev -> Prop),
  (forall x y, R x y -> rank x < rank y) -> forall x, ~ clos_trans Ev R x x.
Proof. intros R Hedge x Hct. pose proof (ct_rank R Hedge x x Hct). lia. Qed.

Lemma rf_rank : forall w b r, rf w b r -> rank w < rank r.
Proof. intros w b r H. destruct w, b, r; simpl in H; try contradiction; simpl; lia. Qed.

Lemma fr_rank : forall w1 b x y,
  rf w1 b x -> is_write y -> touches y b -> gmo w1 y -> rank x < rank y.
Proof.
  intros w1 b x y Hrf Hw Ht Hg. unfold gmo in Hg.
  destruct w1, b, x; simpl in Hrf; try contradiction;
    destruct y; simpl in Hw, Ht; try contradiction; simpl in *; lia.
Qed.

Lemma ppoF_rank : forall x y,
  PPO_union.ppoF Ev Lb po is_read is_write same_addr addr data ctrl fence rf x y -> rank x < rank y.
Proof.
  intros x y H.
  destruct H as [ a b Hpo Hsa Hst | a b Hf | a b Ha | a b Hd | a b Hc Hst
                | a b Hst Hex | a b Hlb Hex ].
  - exact (proj1 Hpo).
  - destruct Hf.
  - destruct Ha.
  - destruct Hd.
  - destruct Hc.
  - destruct Hex as [m [_ [_ Ham]]]; destruct Ham.
  - destruct Hex as [m [bb [_ [_ [[Ha | Hd] _]]]]]; [destruct Ha | destruct Hd].
Qed.

Definition CfC := Clift_coherence.Cf Ev Lb gmo is_write is_read touches E0 rf poloc.
Definition FRfC :=
  Frozen_mainmodel.FRf Ev Lb nat gmo is_write is_read is_read is_write
    touches same_addr addr data ctrl fence hart E0 rf po.

Lemma edge_Cf : forall x y, CfC x y -> rank x < rank y.
Proof.
  intros x y H. unfold CfC, Clift_coherence.Cf in H.
  destruct H as [ [b Hco] | [ [b [Hrx Hfr]] | [ [b Hrf] | [Hpo _] ] ] ].
  - unfold Clift_coherence.co_flt, Clift_coherence.coOn in Hco.
    destruct Hco as [_ [_ [_ [_ [_ [_ G]]]]]]. exact G.
  - destruct Hfr as [w1 [Hrf Hco]].
    unfold Clift_coherence.co_flt, Clift_coherence.coOn in Hco.
    destruct Hco as [_ [_ [_ [Wy [_ [Ty G]]]]]].
    exact (fr_rank w1 b x y Hrf Wy Ty G).
  - exact (rf_rank x b y Hrf).
  - exact (proj1 Hpo).
Qed.

Lemma edge_FRf : forall x y, FRfC x y -> rank x < rank y.
Proof.
  intros x y H. unfold FRfC, Frozen_mainmodel.FRf, Rlift_mainmodel.Rf in H.
  destruct H as [ [b Hco] | [ [b [Hrx Hfr]] | [ Hrfe | Hppo ] ] ].
  - unfold Rlift_mainmodel.co_flt, Rlift_mainmodel.coOn in Hco.
    destruct Hco as [_ [_ [_ [_ [_ [_ G]]]]]]. exact G.
  - destruct Hfr as [w1 [Hrf Hco]].
    unfold Rlift_mainmodel.co_flt, Rlift_mainmodel.coOn in Hco.
    destruct Hco as [_ [_ [_ [Wy [_ [Ty G]]]]]].
    exact (fr_rank w1 b x y Hrf Wy Ty G).
  - destruct Hrfe as [b [Hrf _]]. exact (rf_rank x b y Hrf).
  - unfold Frozen_mainmodel.fault_ppo in Hppo. destruct Hppo as [Hpf | [bx Hr2]].
    + exact (ppoF_rank x y Hpf).
    + unfold PPO_union.r2F, PPO_union.polnw_F in Hr2.
      destruct Hr2 as [[_ [_ [_ [_ [Hpo _]]]]] _]. exact (proj1 Hpo).
Qed.

Definition Hcf  : forall x, ~ clos_trans Ev CfC  x x := acyc_from_rank CfC  edge_Cf.
Definition Hfrf : forall x, ~ clos_trans Ev FRfC x x := acyc_from_rank FRfC edge_FRf.

(* ============================ the contraction premises, discharged ============================ *)

Lemma h_potrans : forall a b c, po a b -> po b c -> po a c.
Proof. unfold po; intros a b c [H1 H2] [H3 H4]; split; [lia | congruence]. Qed.

Lemma h_rwdisj : forall e, is_read e -> is_write e -> False.
Proof. intros e Hr Hw. destruct e; simpl in Hr, Hw; contradiction. Qed.

Lemma h_Hirr : forall e, In e E0 -> ~ gmo e e.
Proof. unfold gmo; intros; lia. Qed.

Lemma h_Htr : forall a b c, In a E0 -> In b E0 -> In c E0 -> gmo a b -> gmo b c -> gmo a c.
Proof. unfold gmo; intros; lia. Qed.

Lemma h_Htot : forall a b, In a E0 -> In b E0 -> a <> b -> gmo a b \/ gmo b a.
Proof.
  intros a b _ _ Hne. unfold gmo.
  destruct a, b; simpl; try lia; exfalso; apply Hne; reflexivity.
Qed.

Lemma h_rfC4 : forall b r w, is_read r -> In r E0 -> rf w b r ->
  L1_abstract_erasure.C4_source Ev Lb is_write touches gmo po E0 b r w.
Proof.
  intros b r w Hr _ Hrf.
  unfold L1_abstract_erasure.C4_source, L1_abstract_erasure.cand.
  destruct w, b, r; simpl in Hrf; try contradiction;
    (split;
     [ split; [apply all_in_E0 |]; split; [exact I |]; split; [exact I |];
       left; unfold gmo; simpl; lia
     | intros w' [_ [Ww' [Tw' Ord]]];
       destruct w'; simpl in Ww', Tw'; try contradiction;
       unfold gmo, po in *; simpl in *;
       first [ left; reflexivity | right; lia | exfalso; destruct Ord; lia ] ]).
Qed.

Lemma h_rftouch : forall w b r, rf w b r -> touches w b.
Proof. intros w b r H. destruct w, b, r; simpl in H; try contradiction; exact I. Qed.

Lemma h_rffun : forall w1 w2 x r, rf w1 x r -> rf w2 x r -> w1 = w2.
Proof.
  intros w1 w2 x r H1 H2.
  destruct w1, x, r; simpl in H1; try contradiction;
    destruct w2; simpl in H2; try contradiction; reflexivity.
Qed.

Lemma h_lanes : forall k d, In (k, d) LS ->
  ML_T1.LaneTok Ev Lb nat nat gmo is_write is_read touches wval addr data hart E0 rf po k d.
Proof.
  intros k d H. unfold LS in H. simpl in H.
  destruct H as [E | []]; inversion E; subst;
  (constructor;
  [ apply all_in_E0 | apply all_in_E0 | exact I | exact I
  | unfold gmo; simpl; lia | unfold po; simpl; split; [lia | reflexivity] | reflexivity
  | intros b H; exact H
  | intros b _; reflexivity
  | intros b Tdb w _ Ww Tw [G1 G2]; destruct b; simpl in Tdb; try contradiction;
      destruct w; simpl in Ww, Tw; try contradiction; unfold gmo in *; simpl in *; lia
  | intros e Hne Hpo; unfold po in *; destruct e; simpl in *; try lia;
      exfalso; apply Hne; reflexivity
  | intros a x Ra Tax Tdx [G1 G2]; destruct x; simpl in Tdx; try contradiction;
      destruct a; simpl in Ra, Tax; try contradiction; unfold po in *; simpl in *; lia
  | intros e; split; intro H; destruct H
  | intros bb c Hkc Hrf; destruct bb, c; simpl in Hrf; try contradiction;
      unfold po in Hkc; simpl in Hkc; destruct Hkc as [_ Hh]; discriminate Hh ]).
Qed.

Lemma s_lanes : forall k d, In (k, d) LS ->
  ML_T1.LaneOK Ev Lb nat nat gmo is_write is_read touches wval addr data hart E0 rf po k d.
Proof.
  intros k d H.
  exact (ML_T1.LaneTok_LaneOK Ev Lb nat nat gmo is_write is_read touches wval addr data hart E0 rf
           po h_potrans h_rwdisj k d (h_lanes k d H)).
Qed.

Lemma h_keep : forall k d, In (k, d) LS -> ~ ML_base.isdel Ev LS k.
Proof.
  intros k d H. unfold LS in H. simpl in H.
  unfold ML_base.isdel, ML_base.dels, LS. simpl.
  destruct H as [E | []]; inversion E; subst.
  intros [X | []]; discriminate X.
Qed.

Definition Hpb : forall b x, ~ clos_trans Ev (CfB Ev Lb gmo is_write is_read touches E0 rf poloc b) x x :=
  union_to_perbyte Ev Lb gmo is_write is_read touches E0 rf poloc Hcf.

Definition mk_T1_pb_instance :=
  Perbyte.ML_T1_refinement_pb Ev ev_eq_dec Lb nat nat gmo is_write is_read is_read is_write touches
    wval same_addr addr data ctrl fence hart E0 rf po poloc LS
    h_Hirr h_Htr h_Htot h_potrans h_rfC4 h_rftouch h_rffun s_lanes h_keep Hpb Hfrf.

(* ============================ the Stage-2 data and the masked shape ============================ *)

Definition Ctx (e : Ev) : Prop := e = Tr \/ e = Xr.

Definition ctx_dec : forall e, {Ctx e} + {~ Ctx e}.
Proof.
  intro e. unfold Ctx.
  destruct e;
    first [ left; left; reflexivity | left; right; reflexivity
          | right; intros [H | H]; discriminate H ].
Defined.

Definition is_chk (_ : Ev) : Prop := False.
Definition chk_dec : forall e, {is_chk e} + {~ is_chk e} := fun e => right (fun H => H).

Inductive Ln := ln0 | ln1 | ln2 | ln3.

Definition ln_eq_dec : forall x y : Ln, {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition lane (e : Ev) : Ln :=
  match e with W0 => ln0 | F1 => ln1 | K3 | D3 => ln3 | _ => ln0 end.
Definition is_lane_write (e : Ev) : Prop :=
  match e with W0 | F1 | K3 | D3 => True | _ => False end.
Definition lanes : list Ln := [ln0; ln1; ln2; ln3].
Definition lane_index (l : Ln) : nat := match l with ln0 => 0 | ln1 => 1 | ln2 => 2 | ln3 => 3 end.
Definition byte_addr (b : Lb) : nat := match b with L0 => 64 | L1 => 72 | L2 => 80 | L3 => 88 end.

(* the mask, read off the register state at the cut *)
Definition m_active (l : Ln) : bool := Alpha_regs.lact St vl mask s0 (lane_index l).
Definition m_lo (l : Ln) : nat := Shape_instances.unit_lo Ln lane_index 64 l.
Definition m_hi (l : Ln) : nat := Shape_instances.unit_hi Ln lane_index 64 l.
(* the element values come from the data register of the state at the cut *)
Definition vdata (l : Ln) (_ : Lb) : nat := dat s0 (lane_index l).

Lemma mk_active_from_regs : forall l,
    m_active l = andb (mask s0 (lane_index l)) (Nat.ltb (lane_index l) (vl s0)).
Proof. intro l. reflexivity. Qed.

(* the replay sees the same active elements: the handler satisfies alpha_regs *)
Lemma mk_replay_same_active : forall l,
    Alpha_regs.lact St vl mask (Hdl s0) (lane_index l) = m_active l.
Proof.
  intro l. exact (Alpha_regs.replay_lane_active St nat nat base dat vl eew mask Hdl s0 (lane_index l)
                    mk_alpha_regs).
Qed.

(* the masked shape IS the register-derived shape of Shape_instances at the state s0, and the
   handler leaves that whole shape (activity and byte ranges) unchanged *)
Theorem mk_shape_is_reg_shape : forall l,
    m_active l = Shape_instances.reg_active St vl mask Ln lane_index s0 l /\
    m_lo l = Shape_instances.reg_lo St base eew Ln lane_index s0 l /\
    m_hi l = Shape_instances.reg_hi St base eew Ln lane_index s0 l.
Proof.
  intro l. unfold m_lo, m_hi, Shape_instances.unit_lo, Shape_instances.unit_hi,
             Frozen_pmp.lane_lo, Frozen_pmp.lane_hi, Shape_instances.reg_hi, Shape_instances.reg_lo.
  destruct l; simpl; repeat split; reflexivity.
Qed.

Theorem mk_replay_same_shape : forall l,
    Shape_instances.reg_active St vl mask Ln lane_index (Hdl s0) l = m_active l /\
    Shape_instances.reg_lo St base eew Ln lane_index (Hdl s0) l = m_lo l /\
    Shape_instances.reg_hi St base eew Ln lane_index (Hdl s0) l = m_hi l.
Proof.
  intro l.
  destruct (Shape_instances.mask_shape_from_regs St nat base dat vl eew mask Hdl Ln lane_index s0
              mk_alpha_regs l) as [A [B C]].
  destruct (mk_shape_is_reg_shape l) as [A' [B' C']].
  rewrite A, B, C, A', B', C'. repeat split; reflexivity.
Qed.

Lemma mk_active_values : m_active ln0 = true /\ m_active ln1 = true /\ m_active ln2 = false /\
                         m_active ln3 = true.
Proof. repeat split; reflexivity. Qed.

(* the masked shape is not the unit-stride shape: element 2 is listed and inactive *)
Theorem mk_shape_not_unit : In ln2 lanes /\ m_active ln2 = false.
Proof. split; [simpl; tauto | reflexivity]. Qed.

Lemma mk_kernel :
  Shape.E_K Ev ev_eq_dec E0 LS Ctx ctx_dec = [Wi2; Wi3; W0; K3; F1; R2; R3].
Proof. reflexivity. Qed.

Lemma mk_act_lanes : Shape.act_lanes Ln lanes m_active = [ln0; ln1; ln3].
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------- the Stage-2 premises *)

Lemma s_rf_src : forall w b r, rf w b r -> is_write w.
Proof. intros w b r H. destruct w, b, r; simpl in H; try contradiction; exact I. Qed.

Lemma s_rf_tgt : forall w b r, rf w b r -> is_read r.
Proof. intros w b r H. destruct w, b, r; simpl in H; try contradiction; exact I. Qed.

Lemma s_ctx_silent :
  forall e, Ctx e -> (~ is_read e) /\ (~ is_write e) /\ (forall b, ~ touches e b).
Proof.
  intros e [E | E]; subst e;
    (split; [intro H; exact H | split; [intro H; exact H | intros b H; destruct b; exact H]]).
Qed.

Lemma s_chk_nonmem :
  forall e, is_chk e -> (~ is_read e) /\ (~ is_write e) /\ (forall b, ~ touches e b).
Proof. intros e H. destruct H. Qed.

Lemma s_lane_write_is_write : forall e, is_lane_write e -> is_write e.
Proof. intros e H. destruct e; simpl in H; try contradiction; exact I. Qed.

Lemma s_one_write_per_active : forall l, In l lanes -> m_active l = true ->
  exists w, In w (Shape.E_K Ev ev_eq_dec E0 LS Ctx ctx_dec) /\ is_lane_write w /\ lane w = l /\
            (forall w', In w' (Shape.E_K Ev ev_eq_dec E0 LS Ctx ctx_dec) ->
                        is_lane_write w' -> lane w' = l -> w' = w).
Proof.
  intros l _ Ha. rewrite mk_kernel.
  destruct l; [exists W0 | exists F1 | discriminate Ha | exists K3];
    (split; [simpl; tauto |]); (split; [exact I |]); (split; [reflexivity |]);
    intros w' Hin Hw' Hl'; simpl in Hin;
    repeat (destruct Hin as [Hin | Hin]; [subst w'; simpl in Hw', Hl'; first
              [ reflexivity | contradiction | discriminate Hl' ] |]);
    destruct Hin.
Qed.

(* no element write of the masked-off element 2, in the kernel or anywhere in the run *)
Lemma s_writes_active : forall w, In w (Shape.E_K Ev ev_eq_dec E0 LS Ctx ctx_dec) -> is_lane_write w ->
    In (lane w) lanes /\ m_active (lane w) = true.
Proof.
  intros w _ Hw. destruct w; simpl in Hw; try contradiction;
    (split; [simpl; tauto | reflexivity]).
Qed.

Lemma mk_no_write_of_masked : forall e, In e E0 -> is_lane_write e -> lane e <> ln2.
Proof. intros e _ He. destruct e; simpl in He; try contradiction; discriminate. Qed.

Lemma s_foot : forall e b, In e (Shape.E_K Ev ev_eq_dec E0 LS Ctx ctx_dec) -> is_lane_write e ->
    (touches e b <-> m_lo (lane e) <= byte_addr b /\ byte_addr b < m_hi (lane e)).
Proof.
  intros e b _ Hw. unfold m_lo, m_hi, Shape_instances.unit_lo, Shape_instances.unit_hi,
                     Frozen_pmp.lane_lo, Frozen_pmp.lane_hi.
  destruct e; simpl in Hw; try contradiction;
    destruct b; simpl; split; intro H; first [ exact I | lia | contradiction ].
Qed.

Lemma s_value : forall e b, In e (Shape.E_K Ev ev_eq_dec E0 LS Ctx ctx_dec) -> is_lane_write e ->
    touches e b -> wval e b = vdata (lane e) b.
Proof. intros e b _ He _. destruct e; simpl in He; try contradiction; reflexivity. Qed.

Lemma s_deps : forall x a b,
    In x (Shape.E_MK Ev ev_eq_dec E0 LS Ctx ctx_dec is_chk chk_dec) ->
    ~ is_lane_write x -> is_lane_write a -> is_lane_write b ->
    (addr x a <-> addr x b) /\ (data x a <-> data x b) /\ (ctrl x a <-> ctrl x b).
Proof. intros. unfold addr, data, ctrl. tauto. Qed.

(* ---- the position premises, from per-hart total program order and the window ---- *)

Lemma n_po_hart : forall a b, po a b -> hart a = hart b.
Proof. intros a b [_ H]; exact H. Qed.

Lemma n_po_total : forall a b, In a E0 -> In b E0 -> hart a = hart b -> a <> b -> po a b \/ po b a.
Proof.
  intros a b _ _ Hh H. unfold po. rewrite Hh.
  destruct a, b; simpl; first [ left; split; [lia | reflexivity] | right; split; [lia | reflexivity]
                              | exfalso; apply H; reflexivity ].
Qed.

Lemma n_inst_hart : forall a b, is_lane_write a -> is_lane_write b -> hart a = hart b.
Proof.
  intros a b Ha Hb. destruct a; simpl in Ha; try contradiction;
    destruct b; simpl in Hb; try contradiction; reflexivity.
Qed.

Lemma n_window : forall a x b, In x E0 -> is_lane_write a -> is_lane_write b ->
    po a x -> po x b -> is_lane_write x \/ Ctx x \/ is_chk x.
Proof.
  intros a x b _ Ha Hb [P1 _] [P2 _].
  destruct a; simpl in Ha; try contradiction; destruct b; simpl in Hb; try contradiction;
    destruct x; simpl in *; try lia;
    first [ left; exact I | right; left; unfold Ctx; auto ].
Qed.

Definition pos_before :=
  Normal_instance.position_before Ev ev_eq_dec nat hart E0 po LS Ctx ctx_dec is_chk chk_dec
    is_lane_write n_po_hart n_po_total n_inst_hart n_window.
Definition pos_after :=
  Normal_instance.position_after Ev ev_eq_dec nat hart E0 po LS Ctx ctx_dec is_chk chk_dec
    is_lane_write n_po_hart n_po_total n_inst_hart n_window.

(* ---- the shape premises and the PMP data ---- *)

Lemma m_inj : forall l1 l2, In l1 lanes -> In l2 lanes -> lane_index l1 = lane_index l2 -> l1 = l2.
Proof. intros l1 l2 _ _ H. destruct l1, l2; simpl in H; try reflexivity; discriminate H. Qed.

Lemma m_nonempty : forall l, In l lanes -> m_lo l < m_hi l.
Proof. exact (Shape_instances.unit_shape_nonempty Ln lanes lane_index 64). Qed.

Lemma m_disjoint : forall l1 l2, In l1 lanes -> In l2 lanes ->
    m_active l1 = true -> m_active l2 = true -> l1 <> l2 ->
    m_hi l1 <= m_lo l2 \/ m_hi l2 <= m_lo l1.
Proof.
  intros l1 l2 H1 H2 _ _ Hne.
  exact (Shape_instances.unit_shape_disjoint Ln lanes lane_index 64 m_inj l1 l2 H1 H2
           eq_refl eq_refl Hne).
Qed.

Lemma m_K_listed : In ln1 lanes.
Proof. simpl; tauto. Qed.

Lemma m_K_active : m_active ln1 = true.
Proof. reflexivity. Qed.

Lemma m_bg : forall l, In l lanes -> m_active l = true -> 0 <= m_lo l /\ m_hi l <= 1000.
Proof.
  intros l _ _. unfold m_lo, m_hi, Shape_instances.unit_lo, Shape_instances.unit_hi,
                  Frozen_pmp.lane_lo, Frozen_pmp.lane_hi.
  destruct l; simpl; lia.
Qed.

(* HEADLINE: the trap-free counterpart of the masked run, through the shape interface *)
Definition mk_stage2_shape_instance :=
  Shape.stage2_shape Ev ev_eq_dec Lb nat nat Ln ln_eq_dec gmo is_write is_read is_read is_write
    touches wval same_addr addr data ctrl fence hart E0 rf po poloc LS Ctx ctx_dec is_chk chk_dec
    lane is_lane_write vdata byte_addr lanes m_active m_lo m_hi
    h_Hirr h_Htr h_Htot h_potrans h_rfC4 h_rftouch h_rffun s_lanes h_keep Hpb Hfrf
    s_rf_src s_rf_tgt s_ctx_silent s_chk_nonmem h_rwdisj s_lane_write_is_write
    s_one_write_per_active s_writes_active s_foot s_value s_deps
    ln1 0 1000 m_nonempty m_disjoint m_K_listed m_K_active m_bg
    pos_before pos_after.

(* ============================ what the masked instance shows ============================ *)

Lemma mk_carrier : ML_base.carrier_L Ev ev_eq_dec E0 LS = [Wi2; Wi3; W0; K3; Tr; Xr; F1; R2; R3].
Proof. reflexivity. Qed.

Lemma comax_Wi2 : Obs_final_state.co_max_of Ev Lb gmo is_write touches
                   (Obs_final_state.inE0 Ev E0) L2 Wi2.
Proof.
  split; [exact I |]. split; [exact I |]. split; [apply all_in_E0 |].
  intros w' _ Ww' Tw'. destruct w'; simpl in Ww', Tw'; try contradiction;
    first [ left; reflexivity | right; unfold gmo; simpl; lia ].
Qed.

Lemma comax_D3 : Obs_final_state.co_max_of Ev Lb gmo is_write touches
                  (Obs_final_state.inE0 Ev E0) L3 D3.
Proof.
  split; [exact I |]. split; [exact I |]. split; [apply all_in_E0 |].
  intros w' _ Ww' Tw'. destruct w'; simpl in Ww', Tw'; try contradiction;
    first [ left; reflexivity | right; unfold gmo; simpl; lia ].
Qed.

Lemma comax_W0 : Obs_final_state.co_max_of Ev Lb gmo is_write touches
                  (Obs_final_state.inE0 Ev E0) L0 W0.
Proof.
  split; [exact I |]. split; [exact I |]. split; [apply all_in_E0 |].
  intros w' _ Ww' Tw'. destruct w'; simpl in Ww', Tw'; try contradiction;
    first [ left; reflexivity | right; unfold gmo; simpl; lia ].
Qed.

Lemma comax_F1 : Obs_final_state.co_max_of Ev Lb gmo is_write touches
                  (Obs_final_state.inE0 Ev E0) L1 F1.
Proof.
  split; [exact I |]. split; [exact I |]. split; [apply all_in_E0 |].
  intros w' _ Ww' Tw'. destruct w'; simpl in Ww', Tw'; try contradiction;
    first [ left; reflexivity | right; unfold gmo; simpl; lia ].
Qed.

(* After erasing the duplicate of element 3: the reader still sees 0 at the masked-off element 2
   and 6 at element 3; the final values of the active elements 0, 1, 3 are 4, 1, 6 and the masked-off
   element 2 keeps 0. The value 9 that the data register holds for element 2 is never written. *)
Theorem mk_instance_observation :
  ML_base.carrier_L Ev ev_eq_dec E0 LS = [Wi2; Wi3; W0; K3; Tr; Xr; F1; R2; R3] /\
  (exists w, Obs_final_state.co_max_of Ev Lb gmo is_write touches
               (ML_base.survivor_L Ev E0 LS) L0 w /\ wval w L0 = 4) /\
  (exists w, Obs_final_state.co_max_of Ev Lb gmo is_write touches
               (ML_base.survivor_L Ev E0 LS) L1 w /\ wval w L1 = 1) /\
  (exists w, ML_base.rf_L Ev LS Lb rf w L2 R2 /\ wval w L2 = 0) /\
  (exists w, ML_base.rf_L Ev LS Lb rf w L3 R3 /\ wval w L3 = 6) /\
  (exists w, Obs_final_state.co_max_of Ev Lb gmo is_write touches
               (ML_base.survivor_L Ev E0 LS) L2 w /\ wval w L2 = 0) /\
  (exists w, Obs_final_state.co_max_of Ev Lb gmo is_write touches
               (ML_base.survivor_L Ev E0 LS) L3 w /\ wval w L3 = 6) /\
  vdata ln2 L2 = 9.
Proof.
  destruct mk_T1_pb_instance as
    [E_N [rf_N [HE [Hrf [_ [_ [_ [Hread Hcomax]]]]]]]].
  assert (HR2 : In R2 E_N) by (rewrite HE, mk_carrier; simpl; tauto).
  assert (HR3 : In R3 E_N) by (rewrite HE, mk_carrier; simpl; tauto).
  split; [exact mk_carrier |].
  split; [destruct (Hcomax L0 W0 comax_W0) as [w [Hw Hv]]; exists w; split; [exact Hw | symmetry; exact Hv] |].
  split; [destruct (Hcomax L1 F1 comax_F1) as [w [Hw Hv]]; exists w; split; [exact Hw | symmetry; exact Hv] |].
  split; [| split; [| split; [| split]]].
  - destruct (Hread R2 L2 Wi2 HR2 I I) as [w [Hw Hv]]. rewrite Hrf in Hw.
    exists w. split; [exact Hw | exact Hv].
  - destruct (Hread R3 L3 D3 HR3 I I) as [w [Hw Hv]]. rewrite Hrf in Hw.
    exists w. split; [exact Hw | exact Hv].
  - destruct (Hcomax L2 Wi2 comax_Wi2) as [w [Hw Hv]]. exists w. split; [exact Hw | symmetry; exact Hv].
  - destruct (Hcomax L3 D3 comax_D3) as [w [Hw Hv]]. exists w. split; [exact Hw | symmetry; exact Hv].
  - reflexivity.
Qed.
