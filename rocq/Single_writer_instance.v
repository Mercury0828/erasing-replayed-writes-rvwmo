(* Single_writer_instance.v — Proposition 4 applied to a run with a trap and a replay.

   The run is the one of ML_instance_2h.v, on which the per-byte Theorem 2 is applied: hart 0 runs
   the faulting store (early writes K2 K3, trap region Tr Xr, replay F1 D2 D3), hart 1 reads, and
   hart 2 holds the initial writes Wi2 Wi3. The trap events lie po-between each early write and its
   replay (sw_trap_between), so a premise asking the two attempts to have the same po relation to
   every other event fails here. The premises of L2_gamma.gamma_D_implies_gamma_adj, which constrain
   only writes of the byte, all hold, and the theorem gives adjacency for both element pairs
   (sw_instance_adj).

   0 Admitted / 0 axioms. Coq 8.15. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import RestartV.L2_gamma.
Require Import RestartV.ML_instance_2h.
Import ListNotations.

Definition init (e : Ev) : Prop := e = Wi2 \/ e = Wi3.

Lemma init_dec : forall e, init e \/ ~ init e.
Proof. intro e; unfold init; destruct e; (left; auto; fail) || (right; intros [H|H]; discriminate). Qed.

Lemma sw_gmo_wf : gmo_wf Ev E0 gmo.
Proof. split; unfold gmo; intros; lia. Qed.

Lemma sw_po_trans : forall a c e, po a c -> po c e -> po a e.
Proof. unfold po; intros a c e [H1 H2] [H3 H4]; split; [lia | congruence]. Qed.

Lemma sw_po_total : forall a c, In a E0 -> In c E0 -> hart a = 0 -> hart c = 0 -> a <> c ->
  po a c \/ po c a.
Proof.
  unfold po; intros a c _ _ Ha Hc Hne.
  destruct a, c; simpl in *; try discriminate; try (exfalso; apply Hne; reflexivity);
    first [left; split; [lia | reflexivity] | right; split; [lia | reflexivity]].
Qed.

(* the trap region lies po-between each early write and its replay *)
Lemma sw_trap_between : po K2 Tr /\ po Tr D2 /\ po K3 Xr /\ po Xr D3 /\ ~ po Tr K2 /\ ~ po Xr K3.
Proof. unfold po; simpl; repeat split; lia. Qed.

Ltac sw_close :=
  repeat match goal with
  | x : Ev |- _ => destruct x
  end; simpl in *; unfold po, gmo, init in *; simpl in *;
  try tauto; try lia; try (intuition discriminate); try (intuition lia).

Lemma sw_adj_at (b : Lb) (p q : Ev) :
  (b = L2 /\ p = K2 /\ q = D2) \/ (b = L3 /\ p = K3 /\ q = D3) ->
  gamma_adj Ev Lb is_write touches E0 gmo b p q.
Proof.
  intros Hsel.
  destruct Hsel as [[-> [-> ->]]|[-> [-> ->]]];
  (eapply (gamma_D_implies_gamma_adj Ev Lb is_write touches E0 gmo po nat hart 0 init);
    [ exact sw_gmo_wf | apply all_in_E0 | apply all_in_E0 | simpl; exact I | simpl; exact I
    | simpl; exact I | simpl; exact I | exact init_dec
    | unfold init; intros [H|H]; discriminate | unfold init; intros [H|H]; discriminate
    | reflexivity | reflexivity | unfold po; simpl; split; [lia | reflexivity]
    | intros a c _ _ Wa Wc Ta Tc Hpo; destruct a, c; simpl in *; try contradiction;
      unfold po, gmo in *; simpl in *; lia
    | intros a c _ _ Wa Wc Ta Tc Ia Ic; unfold init in *;
      destruct a, c; simpl in *; try contradiction; unfold gmo; simpl;
      first [lia | destruct Ia as [Ia|Ia]; discriminate | solve [exfalso; apply Ic; auto]]
    | exact sw_po_trans
    | exact sw_po_total
    | intros z _ Wz Tz Nzp Nzq [H1 H2]; destruct z; simpl in *; try contradiction;
      try congruence; unfold po in *; simpl in *; lia
    | intros w _ Ww Tw Iw; unfold init in Iw; destruct w; simpl in *; try contradiction;
      first [reflexivity | solve [exfalso; apply Iw; auto]] ]).
Qed.

Theorem sw_instance_adj :
  gamma_adj Ev Lb is_write touches E0 gmo L2 K2 D2 /\
  gamma_adj Ev Lb is_write touches E0 gmo L3 K3 D3.
Proof. split; apply sw_adj_at; auto. Qed.
