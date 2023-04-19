(* Modular network inference *)
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
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

Lemma combine_equal :
  forall {T1 T2 : Type} (l1 l11 : list T1) (l2 l22 : list T2),
    l1 = l11 -> l2 = l22 -> combine l1 l2 = combine l11 l22.
  Proof. intros. subst. reflexivity. Qed.

Lemma map_project_combine1 :
  forall {T1 T2 T3 : Type} (l1 : list T1) (l2 : list T2) (f : T1 -> T3),
    length l1 = length l2 ->
    map (fun p => f (fst p)) (combine l1 l2) = map f l1.
  Proof.
    intros. generalize dependent l2.
    induction l1; auto.
    intros l2 Hlength.
    induction l2.
    - inversion Hlength.
    - inversion Hlength.
      apply IHl1 in H0. rewrite map_cons.
      rewrite <- H0.
      simpl. reflexivity.
Qed.

Lemma map_project_combine2 :
  forall {T1 T2 T3 : Type} (l1 : list T1) (l2 : list T2) (f : T2 -> T3),
    length l1 = length l2 ->
    map (fun p => f (snd p)) (combine l1 l2) = map f l2.
  Proof.
    intros. generalize dependent l1.
    induction l2.
    - intros l1 Hlength. inversion Hlength. simpl. rewrite combine_nil. reflexivity.
    - induction l1; intros Hlength; inversion Hlength.
      rewrite map_cons.
      apply IHl2 in H0.
      rewrite <- H0.
      simpl. reflexivity.
Qed.

Section timepiece.
  Variable S : Type.

  Definition Node := nat.
  Definition Edge : Type := (Node * Node).

  Variable Merge : S -> S -> S.
  Variable F : Edge -> S -> S.

  Definition φ := S -> Prop.
  Definition A := nat -> φ.

  (* Computing a new route at a node given routes of its neighbors. *)
  Definition updated_state (node : Node) (initial : S)
    (neighbors : list (Node * S)) : S :=
    fold_right (fun (neighbor : (Node * S)) (st : S) =>
                  let (m, ms) := neighbor in
                  Merge st (F (m, node) ms)) initial neighbors.

  (* The until temporal operator. *)
  Definition until (tau : nat) (before after : φ) : A :=
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

  Definition construct_until (u : Until) : A :=
    until (tau u) (before u) (after u).

  (* Review of how fst/snd work with tuples of > 2 elements. *)
  Compute (snd (fst (1, 2, 3))). (* --> 2 *)

  (* A helper definition for writing out the inductive condition with times
     erased: all invariants are specified as [S -> Prop] functions. *)
  Definition inductive_condition_untimed
    (node : Node) (initial : S) (node_invariant : φ)
    (neighbors : list (Node * S * φ)) :=
    (* if every neighbor's route satisfies the invariant φ *)
    (Forall (fun (c : Node * S * φ) => ((snd c) (snd (fst c)))) neighbors) ->
    (* then the node's invariant holds on the updated state *)
    (node_invariant (updated_state node initial (map (fun c => fst c) neighbors))).

  (* A helper definition for writing out the inductive condition
     given a particular set of states and a particular time [t]. *)
  Definition inductive_condition_fixed_time
    (node : Node) (initial : S) (node_invariant : A)
    (neighbors : list (Node * S * A)) (t : nat) :=
    inductive_condition_untimed
      (* apply the node's invariant at time [t + 1] *)
      node initial (node_invariant (1 + t))
      (* apply the neighbors' invariants at time [t] *)
      (map (fun (c : Node * S * A) => (fst c, (snd c) t)) neighbors).

  (* The original inductive condition for a node [n]. *)
  Definition inductive_condition (n : Node) (initial : S) (node_invariant : A)
                                 (neighbors : list (Node * A)) :=
    forall (t : nat) (states : list S),
      length states = length neighbors ->
      inductive_condition_fixed_time
        n initial node_invariant
        (* squeeze the states in between the Node and the invariant *)
        (map (fun (c : Node * A * S) => (fst (fst c), snd c, snd (fst c)))
           (combine neighbors states)) t.

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

  Lemma untils_have_equivalent_buntils :
    forall (neighbor_invariants : list Until) (B : list bool) (t : nat),
      length neighbor_invariants = length B ->
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

  (* helper to construct all the neighbors' boolean until invariants *)
  Definition zip_boolean_untils
    (neighbors : list (Node * Until)) (B : list bool) (states : list S)
    : list (Node * S * φ) :=
    map (fun (c : Node * Until * S * bool) =>
      let (c1, nbrb) := c in
      let (c2, st) := c1 in
      let (nbr, u) := c2 in
      (nbr, st, buntil nbrb (before u) (after u)))
      (combine (combine neighbors states) B).

  (* helper lemma stating that the invariants generated using zip_boolean_untils
     are the same as the invariants generated by mapping construct_until over the
     Untils *)
  Lemma zip_boolean_untils_produces_equivalent_invariants :
    forall (neighbors : list Node)
      (neighbor_invariants : list Until)
      (B : list bool)
      (states : list S)
      (t : nat),
      (* all lists are the same length *)
      length neighbors = length neighbor_invariants /\ length neighbor_invariants = length B /\ length B = length states ->
      (* all booleans are associated with the taus *)
      booleans_are_time_bounds (combine B (map tau neighbor_invariants)) t ->
      (* zip produces a list of [Node * S * φ] which we must then relate to
         a list of [Node * S * A] *)
      zip_boolean_untils (combine neighbors neighbor_invariants) B states =
        combine (combine neighbors states) (map (fun u => (construct_until u) t) neighbor_invariants).
  Proof.
    unfold zip_boolean_untils, booleans_are_time_bounds, boolean_equals_time_bound.
    induction neighbors.
    - induction neighbor_invariants; auto.
    - induction neighbor_invariants; intros B states t [Hlen1 [Hlen2 Hlen3]] Hbtb; inversion Hlen1; inversion Hlen2; inversion Hlen3.
      clear Hlen1 Hlen2 Hlen3.
      induction B; inversion H1.
      induction states; inversion H2.
      unfold zip_boolean_untils in *.
      simpl in *.
      inversion Hbtb.
      unfold buntil, construct_until, until.
      simpl in H6.
      subst.
      f_equal.
      admit.
  Admitted.

  Definition boolean_inductive_condition
    (n : Node) (initial : S) (b : bool) (u : Until)
    (neighbors : list (Node * Until)) :=
    forall (B : list bool),
      length B = length neighbors ->
      (* associate the booleans with the neighbor witness times *)
      (exists (t : nat), booleans_are_time_bounds
                    (combine B (map (fun nbr => tau (snd nbr)) neighbors)) t
      /\ boolean_equals_time_bound b (1 + t) (tau u)) ->
      (* define the inductive condition check again, but now using booleans *)
      (forall (states : list S),
          length states = length neighbors ->
          inductive_condition_untimed n initial (buntil b (before u) (after u))
              (zip_boolean_untils neighbors B states)).

  Lemma ind_vc_until_implies_boolean_ind_vc :
    forall (n : Node) (initial : S) (b : bool) (tau : nat) (before after : φ)
      (neighbors : list Node) (neighbor_invariants : list Until),
      (* node_invariant = until node_tau nbefore nafter -> *)
      length neighbors = length neighbor_invariants ->
      inductive_condition n initial (until tau before after)
        (combine neighbors (map construct_until neighbor_invariants)) ->
      boolean_inductive_condition n initial b (mkUntil tau before after)
        (combine neighbors neighbor_invariants).
  Proof.
    unfold
      inductive_condition,
      boolean_inductive_condition,
      inductive_condition_fixed_time,
      booleans_are_time_bounds.
    simpl.
    intros n initial b tau' before' after'.
    intros neighbors neighbor_invariants Hnbrlen Hindvc B Hblen [t [Hnbr_bounds Hn_bound]] states Hstateslen.
    (* match up the until and buntil *)
    apply (until_has_equivalent_buntil _ _ _ before' after') in Hn_bound.
    rewrite <- Hn_bound.
    rewrite (zip_boolean_untils_produces_equivalent_invariants neighbors neighbor_invariants B states t).
    2: { repeat split; try auto.
         - rewrite Hblen. rewrite combine_length. lia.
         - lia. }
    2: { unfold booleans_are_time_bounds. simpl.
         (* rewrite <- map_combine2 in Hnbr_bounds. *)
         rewrite map_project_combine2 in Hnbr_bounds.
         assumption.
         assumption.
    }
    rewrite combine_length in *.
    rewrite Hnbrlen in *.
    rewrite map_length in Hindvc.
    rewrite PeanoNat.Nat.min_id in *.
    apply (Hindvc t states) in Hstateslen.
    assert (H: (map (fun c : Node * S * A => (fst c, snd c t))
                    (map (fun c : Node * A * S => (fst (fst c), snd c, snd (fst c)))
                       (combine
                          (combine neighbors (map construct_until neighbor_invariants))
                          states))) = (combine (combine neighbors states)
       (map (fun u : Until => construct_until u t) neighbor_invariants))).
    {
      admit.
    }
    rewrite <- H.
    assumption.
  Admitted.

  Lemma boolean_ind_vc_until_implies_ind_vc :
    forall (n : Node) (initial : S) (b : bool) (tau : nat) (before after : φ)
      (neighbors : list Node) (neighbor_invariants : list Until),
      (* node_invariant = until node_tau nbefore nafter -> *)
      length neighbors = length neighbor_invariants ->
      boolean_inductive_condition n initial b (mkUntil tau before after)
        (combine neighbors neighbor_invariants) ->
      inductive_condition n initial (until tau before after)
        (combine neighbors (map construct_until neighbor_invariants)).
  Proof.
  intros n initial b tau' before' after' neighbors neighbor_invariants Hnbrlen.
  intros Hbindvc.
  unfold inductive_condition.
  intros t states Hlenstates.
  unfold inductive_condition_fixed_time.

  unfold zip_boolean_untils in Hbindvc.

  rewrite (zip_boolean_untils_produces_equivalent_invariants neighbors neighbor_invariants B states t).

  (* *)
  Definition time_bounds B T :=
    (* Associate each b in B with a t in T. *)
    Admitted.
End timepiece.
