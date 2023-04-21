(* Modular network inference *)
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Lia.

Lemma map_combine :
  forall {T1 T2 T3 T4 : Type} (l1 : list T1) (l2 : list T2) (f1 : T1 -> T3) (f2 : T2 -> T4),
    map (fun p => (f1 (fst p), f2 (snd p))) (combine l1 l2) =
      combine (map f1 l1) (map f2 l2).
  Proof.
    intros; generalize dependent l2.
    induction l1; auto.
    intros l2.
    rewrite map_cons.
    induction l2; auto.
    simpl.
    rewrite IHl1. reflexivity.
Qed.

Lemma Forall_map :
  forall {T1 T2 : Type} (l : list T1) (f : T1 -> T2) (g : T2 -> Prop),
    Forall g (map f l) <-> Forall (fun x => g (f x)) l.
Proof.
  induction l; intros; split; intro; auto.
  - apply Forall_nil.
  - rewrite map_cons in H. apply Forall_cons.
    + apply Forall_inv in H. assumption.
    + apply IHl. eapply Forall_inv_tail. apply H.
  - simpl. apply Forall_cons.
    + apply Forall_inv in H. assumption.
    + apply IHl. eapply Forall_inv_tail. apply H.
Qed.

Section timepiece.
  Variable S : Type.

  Definition Node := nat.
  Definition Edge : Type := (Node * Node).

  Variable Merge : S -> S -> S.
  Variable F : Edge -> S -> S.
  Variable I : Node -> S.

  Definition φ := S -> Prop.
  Definition Q := nat -> φ.
  Variable A : Node -> Q.

  (* Computing a new route at a node given routes of its neighbors. *)
  Definition updated_state (node : Node)
    (neighbors : list (Node * S)) : S :=
    fold_right (fun (neighbor : (Node * S)) (st : S) =>
                  let (m, ms) := neighbor in
                  Merge st (F (m, node) ms)) (I node) neighbors.

  (* The until temporal operator. *)
  Definition until (tau : nat) (before after : φ) : Q :=
    fun t s => if t <? tau then before s else after s.

  (* The until operator, with a boolean instead of a time bound. *)
  Definition buntil (b : bool) (before after : φ) : φ :=
    fun s => if b then before s else after s.

  Example until_example1 :
    forall s φ, (until 0 φ (fun _ => True)) 1 s.
  Proof. reflexivity. Qed.

  Example buntil_example1 :
    forall s φ, buntil false φ (fun _ => True) s.
  Proof. reflexivity. Qed.

  (* A record to bundle together the elements of an until temporal operator. *)
  Record Until := mkUntil
    {
      tau : nat
    ; before : φ
    ; after : φ
    }.

  Definition construct_until (u : Until) : Q :=
    until (tau u) (before u) (after u).

  (* Review of how fst/snd work with tuples of > 2 elements. *)
  Compute (snd (fst (1, 2, 3))). (* --> 2 *)

  (* A helper definition for writing out the inductive condition with times
     erased: all invariants are specified as [S -> Prop] functions. *)
  Definition inductive_condition_untimed
    (node : Node) (node_invariant : φ)
    (neighbors : list (Node * S)) (neighbor_invariants : list φ) :=
    length neighbors = length neighbor_invariants ->
    (* if every neighbor's route satisfies the invariant φ *)
    (Forall (fun (c : Node * S * φ) => ((snd c) (snd (fst c)))) (combine neighbors neighbor_invariants)) ->
    (* then the node's invariant holds on the updated state *)
    (node_invariant (updated_state node neighbors)).

  (* The original inductive condition for a node [n]. *)
  Definition inductive_condition (n : Node) (neighbors : list Node) :=
    forall (t : nat) (states : list S),
      length states = length neighbors ->
      inductive_condition_untimed
        n (A n (1 + t))
        (combine neighbors states) (map (fun m => A m t) neighbors).

  Definition boolean_equals_time_bound (b : bool) (t tau : nat) :=
    b = (t <? tau).

  (* Lemma relating until and buntil. *)
  Lemma until_has_equivalent_buntil :
    forall (b : bool) (t tau : nat) (φ1 φ2 : φ),
      boolean_equals_time_bound b t tau ->
      (until tau φ1 φ2) t = (buntil b φ1 φ2).
  Proof.
    intros.
    extensionality s.
    unfold boolean_equals_time_bound in H.
    subst.
    reflexivity.
  Qed.

  (* associate all the boolean * witness time pairs *)
  Definition booleans_are_time_bounds (BTs : list (bool * nat)) (t : nat) : Prop :=
    Forall (fun bt => boolean_equals_time_bound (fst bt) t (snd bt)) BTs.

  (** For all until invariants, if every invariant has an associated boolean B,
      then the list of invariants is equal to the associated list of boolean untils. *)
  Lemma untils_have_equivalent_buntils :
    forall (neighbor_invariants : list Until) (B : list bool) (t : nat),
      length B = length neighbor_invariants ->
      (* if every boolean is associated with a time bound, *)
      booleans_are_time_bounds (combine B (map tau neighbor_invariants)) t ->
        (* then a list of invariants with explicit times *)
        map (fun u => (construct_until u) t) neighbor_invariants =
          (* equals a list of invariants with Bs *)
          map (fun bu => buntil (fst bu) (before (snd bu)) (after (snd bu)))
            (combine B neighbor_invariants).
  Proof.
    intros neighbor_invariants.
    induction neighbor_invariants.
    - intros. rewrite combine_nil. reflexivity.
    - intros. induction B.
      + inversion H.
      + inversion H.
        simpl in *.
        inversion H0.
        simpl in H4.
        apply (until_has_equivalent_buntil _ _ _ (before a) (after a)) in H4.
        unfold construct_until.
        subst.
        rewrite H4.
        f_equal.
        apply IHneighbor_invariants.
        * assumption.
        * assumption.
  Qed.

  Definition invariant_is_until (n : Node) (u : Until) :=
    forall t, A n t = construct_until u t.

  Definition boolean_inductive_condition
    (n : Node) (b : bool) (u : Until)
    (neighbors : list Node) (neighbor_invariants : list Until) (B : list bool) :=
      (* enforce that all invariants are Untils *)
      invariant_is_until n u ->
      Forall (fun p => invariant_is_until (fst p) (snd p)) (combine neighbors neighbor_invariants) ->
      (* associate the booleans with the neighbor witness times *)
      forall (t : nat),
        booleans_are_time_bounds (combine B (map tau neighbor_invariants)) t ->
        boolean_equals_time_bound b (1 + t) (tau u) ->
      (* define the inductive condition check again, but now using booleans *)
      (forall (states : list S),
          length states = length neighbors ->
          inductive_condition_untimed
            n (buntil b (before u) (after u))
            (combine neighbors states)
            (* construct the neighbor invariants with booleans *)
            (map (fun p => buntil (fst p) (before (snd p)) (after (snd p))) (combine B neighbor_invariants))).

  (** Proof that the inductive condition implies the boolean inductive condition. *)
  Lemma ind_vc_until_implies_boolean_ind_vc :
    forall (n : Node) (b : bool) (tau : nat) (node_before node_after : φ)
      (neighbors : list Node) (neighbor_invariants : list Until) (B : list bool),
      length neighbors = length neighbor_invariants ->
      length B = length neighbor_invariants ->
      inductive_condition n neighbors ->
      boolean_inductive_condition n b (mkUntil tau node_before node_after)
        neighbors neighbor_invariants B.
  Proof.
    unfold
      inductive_condition,
      boolean_inductive_condition,
      booleans_are_time_bounds.
    simpl.
    intros n b tau' node_before node_after neighbors neighbor_invariants B Hnbrlen Hblen Hindvc
      HnUntil HneighborsUntil t Hnbr_bounds Hn_bound states Hstateslen.
    (* match up the until and buntil *)
    apply (until_has_equivalent_buntil _ _ _ node_before node_after) in Hn_bound.
    rewrite <- Hn_bound.
    apply (untils_have_equivalent_buntils neighbor_invariants B t) in Hblen.
    2: { assumption. }
    rewrite <- Hblen.
    apply (Hindvc t states) in Hstateslen.
    unfold invariant_is_until in *.
    unfold construct_until in HnUntil. simpl in HnUntil.
    rewrite <- HnUntil.
    replace (map (fun u : Until => construct_until u t) neighbor_invariants) with (map (fun m : Node => A m t) neighbors).
    2: {
      clear - HneighborsUntil Hnbrlen.
      assert (Forall (fun p => fst p = snd p)
                (combine (map (fun m => A m) neighbors) (map (fun u => construct_until u) neighbor_invariants))).
      - rewrite <- map_combine.
        simpl.
        apply Forall_map.
        simpl.
        assert (H: (fun x => A (fst x) = construct_until (snd x)) = (fun x => forall t, (compose A fst) x t = (compose construct_until snd) x t)).
        { apply functional_extensionality.
          intro x.
          replace (A (fst x) = construct_until (snd x)) with (forall t1, A (fst x) t1 = construct_until (snd x) t1).
          reflexivity.
        }
        assumption.
        apply functional_extensionality.
        intro x.
        assert (H: (forall t0 : nat, compose A fst x t0 = compose construct_until snd x t0) <-> (compose A fst x = compose construct_until snd x)).
        + split.
          * apply functional_extensionality.
          * intro. rewrite H. auto.
        + destruct H as [H1 H2].
          rewrite H0.
        reflexivity.
        extensionality.
        rewrite <- (equal_f ((compose A fst) x) ((compose construct_until snd x))).
        rewrite (functional_extensionality (compose A fst) (compose construct_until snd)).
        { simpl. }
      - simpl.
        replace (forall t : nat, A (fst p) t = construct_until (snd p) t) with (forall t : nat, A (fst p) = construct_until (snd p)) in HneighborsUntil. functional_extensionality in HneighborsUntil.
        apply map_ext_Forall in H.
    }
    assumption.
  Qed.

  (** Proof that the boolean inductive condition implies the inductive condition
      when the premises of the boolean inductive condition are met.
   *)
  Lemma boolean_ind_vc_until_implies_ind_vc_aux :
    forall n b tau' before' after' neighbors neighbor_invariants B t,
      length B = length neighbor_invariants ->
      booleans_are_time_bounds (combine B (map tau neighbor_invariants)) t ->
      boolean_equals_time_bound b (Datatypes.S t) tau' ->
      boolean_inductive_condition n b (mkUntil tau' before' after') neighbors neighbor_invariants B ->
      forall states : list S,
        length states = length neighbors ->
        inductive_condition_untimed n (until tau' before' after' (1 + t)) (combine neighbors states)
          (map (fun x : Until => construct_until x t) neighbor_invariants).
    Proof.
      intros.
      apply (H2 t H0 H1 states) in H3.
      rewrite (untils_have_equivalent_buntils neighbor_invariants B t); try congruence.
      rewrite (until_has_equivalent_buntil b).
      2: { simpl. assumption. }
      assumption.
    Qed.
End timepiece.
