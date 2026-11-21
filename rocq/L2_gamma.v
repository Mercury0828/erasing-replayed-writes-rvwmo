(* L2_gamma.v — Proposition 4 (a sufficient condition for adjacency): single writer => gamma_adj.

   Statement. Let p, q be two non-initial writes of a byte b on the faulting hart h0, with p po-before
   q. Assume rule r1 (a write po-before a write of the same byte is gmo-before it), that initial
   writes are gmo-before every non-initial write of their byte, and that po is transitive and total
   on the events of h0. If every non-initial write of b is on h0 (gamma_D_at) and no write of b lies
   po-between p and q, then no write of b lies between p and q in gmo (gamma_adj).

   The premise constrains only writes of b. Events of the trap region and the handler lie po-between
   the two attempts of an element in every replay, so a premise over all events would never hold;
   Single_writer_instance.v applies this theorem to the trap-and-replay run of ML_instance_2h.v.

   Proof: an initial write is gmo-before both attempts. Any other write z of b is on h0, hence
   po-before p or po-after p; in the first case it is po-before q by transitivity, in the second it
   is po-after q because it is not po-between p and q. Rule r1 turns this into gmo-before both or
   gmo-after both, so z does not lie between them.

   Self-contained; 0 Admitted / 0 axioms (checked by Print Assumptions). Coq 8.15. *)

Require Import Coq.Lists.List.
Import ListNotations.

Section L2_gamma.

  Variable Event : Type.
  Variable Byte  : Type.
  Variable is_write : Event -> Prop.
  Variable touches  : Event -> Byte -> Prop.

  Variable E0  : list Event.
  Variable gmo : Event -> Event -> Prop.

  Record gmo_wf : Prop := {
    gmo_irrefl : forall e, In e E0 -> ~ gmo e e;
    gmo_trans  : forall a b c, In a E0 -> In b E0 -> In c E0 ->
                               gmo a b -> gmo b c -> gmo a c
  }.

  Variable po : Event -> Event -> Prop.

  (* The faulting hart h0 owns both attempts; init marks the initial writes. *)
  Variable Hart : Type.
  Variable hart : Event -> Hart.
  Variable h0   : Hart.
  Variable init : Event -> Prop.

  (* Same definitions of between / gamma_adj as L1. *)
  Definition between (b : Byte) (p q z : Event) : Prop :=
    is_write z /\ touches z b /\ z <> p /\ z <> q /\
    ((gmo p z /\ gmo z q) \/ (gmo q z /\ gmo z p)).

  Definition gamma_adj (b : Byte) (p q : Event) : Prop :=
    ~ exists z, In z E0 /\ between b p q z.

  (* gamma_D at the duplicated byte b: every non-initial write touching b is on h0. *)
  Definition gamma_D_at (b : Byte) : Prop :=
    forall w, In w E0 -> is_write w -> touches w b -> ~ init w -> hart w = h0.

  Theorem gamma_D_implies_gamma_adj :
    gmo_wf ->
    forall b p q,
      In p E0 -> In q E0 ->
      is_write p -> touches p b -> is_write q -> touches q b ->
      (forall e, init e \/ ~ init e) ->
      ~ init p -> ~ init q -> hart p = h0 -> hart q = h0 -> po p q ->
      (* r1 (subset of gmo): a write po-before a write to the same byte is gmo-before it. *)
      (forall a c, In a E0 -> In c E0 -> is_write a -> is_write c ->
                   touches a b -> touches c b -> po a c -> gmo a c) ->
      (* initial writes come first in gmo at their byte *)
      (forall a c, In a E0 -> In c E0 -> is_write a -> is_write c ->
                   touches a b -> touches c b -> init a -> ~ init c -> gmo a c) ->
      (* po is transitive, and total on the events of h0 *)
      (forall a c e, po a c -> po c e -> po a e) ->
      (forall a c, In a E0 -> In c E0 -> hart a = h0 -> hart c = h0 -> a <> c ->
                   po a c \/ po c a) ->
      (* no write of b lies po-between the two attempts *)
      (forall z, In z E0 -> is_write z -> touches z b -> z <> p -> z <> q ->
                 ~ (po p z /\ po z q)) ->
      gamma_D_at b ->
      gamma_adj b p q.
  Proof.
    intros Hwf b p q Hp Hq Wp Tp Wq Tq Hidec Ip Iq Hhp Hhq Hpq Hr1 Hinit Htrans Htot Hno HgD.
    destruct Hwf as [Hirr Htr].
    (* a gmo 2-cycle is impossible *)
    assert (Hcyc : forall a c, In a E0 -> In c E0 -> gmo a c -> gmo c a -> False).
    { intros a c Ia Ic Hac Hca. apply (Hirr a Ia). apply (Htr a c a Ia Ic Ia Hac Hca). }
    intros [z [Inz Hbtw]].
    destruct Hbtw as [Wz [Tz [Nzp [Nzq Hdisj]]]].
    (* bracket: z is gmo-before both attempts, or gmo-after both. *)
    assert (Hbr : (gmo z p /\ gmo z q) \/ (gmo p z /\ gmo q z)).
    { destruct (Hidec z) as [Iz|Iz].
      - left. split.
        + exact (Hinit z p Inz Hp Wz Wp Tz Tp Iz Ip).
        + exact (Hinit z q Inz Hq Wz Wq Tz Tq Iz Iq).
      - assert (Hhz : hart z = h0) by (apply HgD; assumption).
        destruct (Htot z p Inz Hp Hhz Hhp Nzp) as [Pzp|Ppz].
        + left. split.
          * exact (Hr1 z p Inz Hp Wz Wp Tz Tp Pzp).
          * exact (Hr1 z q Inz Hq Wz Wq Tz Tq (Htrans z p q Pzp Hpq)).
        + destruct (Htot z q Inz Hq Hhz Hhq Nzq) as [Pzq|Pqz].
          * exfalso. exact (Hno z Inz Wz Tz Nzp Nzq (conj Ppz Pzq)).
          * right. split.
            -- exact (Hr1 p z Hp Inz Wp Wz Tp Tz Ppz).
            -- exact (Hr1 q z Hq Inz Wq Wz Tq Tz Pqz). }
    (* contradiction: "between" needs before-one/after-other, bracket gives before-both/after-both *)
    destruct Hbr as [[Bzp Bzq]|[Bpz Bqz]]; destruct Hdisj as [[Hpz Hzq]|[Hqz Hzp]].
    - exact (Hcyc z p Inz Hp Bzp Hpz).
    - exact (Hcyc z q Inz Hq Bzq Hqz).
    - exact (Hcyc z q Inz Hq Hzq Bqz).
    - exact (Hcyc z p Inz Hp Hzp Bpz).
  Qed.

End L2_gamma.
