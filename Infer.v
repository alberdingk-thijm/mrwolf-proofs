(* Modular network inference *)
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Lia.
Require Import Coq.Structures.Orders.
Require Import Coq.Structures.OrdersLists.
Require Import Coq.Structures.GenericMinMax.

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

Lemma map_combine_map :
  forall {T1 T2 T3 T4 T5 : Type} (l1 : list T1) (l2 : list T2) (f1 : T1 -> T3) (f2 : T2 -> T4) (g : (T3 * T4) -> T5),
    map (fun p => g (f1 (fst p), f2 (snd p))) (combine l1 l2) =
      map g (combine (map f1 l1) (map f2 l2)).
Proof.
  intros.
  rewrite <- map_combine.
  rewrite map_map.
  reflexivity.
Qed.

Lemma Forall_forall2 :
  forall { T1 T2 : Type } (R : T1 -> T2 -> Prop) (l1 : list T1) (l2 : list T2),
    length l1 = length l2 ->
    Forall2 (fun x y => R x y) l1 l2 <-> Forall (fun p => R (fst p) (snd p)) (combine l1 l2).
Proof.
  intros.
  generalize dependent l2.
  induction l1.
  - intros. induction l2; repeat constructor. inversion H.
  - intros. induction l2.
    + inversion H.
    + split.
      * intro. simpl. inversion H0. constructor.
        { assumption. }
        { apply IHl1. inversion H. reflexivity. assumption. }
      * intro. inversion H0. constructor. simpl in H3. assumption.
        apply IHl1. inversion H. reflexivity. assumption.
Qed.

Lemma map_ext_curried_Forall2 :
  forall { T1 T2 T3 T4 : Type }
    (l1 : list T1) (l2 : list T2)
    (f1 : T1 -> T3 -> T4) (f2 : T2 -> T3 -> T4) (w : T3),
    length l1 = length l2 ->
    Forall2 (fun x y => forall z, f1 x z = f2 y z) l1 l2 ->
    map (fun x => f1 x w) l1 = map (fun y => f2 y w) l2.
Proof.
  intros.
  (* join the two lists together *)
  rewrite <- (map_project_combine1 _ _ _ H).
  rewrite <- (map_project_combine2 _ _ _ H).
  (* now convert to a Forall *)
  apply map_ext_Forall.
  apply (Forall_forall2 _ _ _ H) in H0.
  eapply Forall_impl.
  intros.
  2: apply H0.
  simpl in H1.
  apply H1.
Qed.

Lemma fold_right_map :
  forall { T1 T2 : Type }
    (l : list T1) (f : T2 -> T2 -> T2) (g : T1 -> T2) (z : T2),
    fold_right (fun x y => f (g x) y) z l =
      fold_right f z (map g l).
Proof.
  intros.
  induction l.
  - simpl. reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Section Net.
  Parameter S : Type.
  Definition V := nat.
  Definition E : Type := V * V.

  Parameter Merge : S -> S -> S.
  Parameter F : E -> S -> S.
  Parameter I : V -> S.

  Axiom merge_associativity : forall s1 s2 s3, Merge (Merge s1 s2) s3 = Merge s1 (Merge s2 s3).
  Axiom merge_commutativity : forall s1 s2, Merge s1 s2 = Merge s2 s1.

  (* interface and predicate definitions *)
  Definition φ := S -> Prop.
  Definition Q := nat -> φ.
  Parameter A : V -> Q.

  (* Applying the transfer function to each neighbor's route. *)
  Definition transfer_routes (node : V) (neighbors : list (V * S)) : list S :=
    (map (fun (neighbor : (V * S)) => F (fst neighbor, node) (snd neighbor)) neighbors).

  (* Computing a new route at a node given routes of its neighbors. *)
  Definition updated_state (node : V) (neighbors : list (V * S)) : S :=
    fold_right Merge (I node) (transfer_routes node neighbors).

  (* A helper definition for writing out the inductive condition with times
     erased: all invariants are specified as [S -> Prop] functions. *)
  Definition inductive_condition_untimed
    (node : V) (node_invariant : φ)
    (neighbors : list (V * S)) (neighbor_invariants : list φ) :=
    length neighbors = length neighbor_invariants ->
    (* if every neighbor's route satisfies the invariant φ *)
    (Forall2 (fun m p => p (snd m)) neighbors neighbor_invariants) ->
    (* then the node's invariant holds on the updated state *)
    (node_invariant (updated_state node neighbors)).

  (* The original inductive condition for a node [n]. *)
  Definition inductive_condition (n : V) (neighbors : list V) :=
    forall (t : nat) (states : list S),
      length states = length neighbors ->
      inductive_condition_untimed
        n (A n (1 + t))
        (combine neighbors states) (map (fun m => A m t) neighbors).
End Net.

Section UntilNet.
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

  Definition A_is_until (n : V) (u : Until) :=
    forall t, A n t = construct_until u t.

  Definition boolean_equals_time_bound (b : bool) (t tau : nat) :=
    b = (t <? tau).

  (* Lemma relating until and buntil. *)
  Lemma until_has_equivalent_buntil :
    forall (b : bool) (t tau : nat) (φ1 φ2 : φ),
      boolean_equals_time_bound b t tau ->
      (until tau φ1 φ2) t = (buntil b φ1 φ2).
  Proof using Type.
    intros.
    extensionality s.
    unfold boolean_equals_time_bound in H.
    subst.
    reflexivity.
  Qed.

  (* associate all the boolean * witness time pairs *)
  Definition booleans_are_time_bounds (B : list bool)  (T : list nat) (t : nat) : Prop :=
    Forall2 (fun b tau => boolean_equals_time_bound b t tau) B T.

  (** For all until invariants, if every invariant has an associated boolean B,
      then the list of invariants is equal to the associated list of boolean untils. *)
  Lemma untils_have_equivalent_buntils :
    forall (neighbor_invariants : list Until) (B : list bool) (t : nat),
      length B = length neighbor_invariants ->
      (* if every boolean is associated with a time bound, *)
      booleans_are_time_bounds B (map tau neighbor_invariants) t ->
        (* then a list of invariants with explicit times *)
        map (fun u => (construct_until u) t) neighbor_invariants =
          (* equals a list of invariants with Bs *)
          map (fun bu => buntil (fst bu) (before (snd bu)) (after (snd bu)))
            (combine B neighbor_invariants).
  Proof using Type.
    intros neighbor_invariants.
    induction neighbor_invariants.
    - intros. rewrite combine_nil. reflexivity.
    - intros. induction B; inversion H.
      simpl in *.
      inversion H0.
      simpl in H4.
      apply (until_has_equivalent_buntil _ _ _ (before a) (after a)) in H5.
      unfold construct_until.
      subst.
      rewrite H5.
      f_equal.
      apply IHneighbor_invariants; assumption.
  Qed.

  Definition boolean_inductive_condition
    (n : V) (u : Until) (neighbors : list V) (neighbor_invariants : list Until) :=
      forall (b : bool) (B : list bool) (t : nat),
        length B = length neighbor_invariants ->
        A_is_until n u ->
        Forall2 A_is_until neighbors neighbor_invariants ->
        booleans_are_time_bounds B (map tau neighbor_invariants) t ->
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
    forall (n : V) (u : Until) (neighbors : list V) (neighbor_invariants : list Until),
      length neighbors = length neighbor_invariants ->
      inductive_condition n neighbors ->
      boolean_inductive_condition n u neighbors neighbor_invariants.
  Proof using Type.
    unfold inductive_condition, boolean_inductive_condition, booleans_are_time_bounds.
    simpl.
    intros n u neighbors neighbor_invariants Hnbrlen Hindvc
      b B t Hblen HnUntil HneighborsUntil Hnbr_bounds Hn_bound states Hstateslen.
    (* match up the until and buntil *)
    apply (until_has_equivalent_buntil _ _ _ (before u) (after u)) in Hn_bound.
    rewrite <- Hn_bound.
    apply (untils_have_equivalent_buntils neighbor_invariants B t Hblen) in Hnbr_bounds.
    rewrite <- Hnbr_bounds.
    apply (Hindvc t states) in Hstateslen.
    unfold A_is_until, construct_until in HnUntil.
    rewrite <- HnUntil.
    rewrite <- (map_ext_curried_Forall2 _ _ _ _ _ Hnbrlen HneighborsUntil).
    apply Hstateslen.
  Qed.

  (** Proof that the boolean inductive condition implies the inductive condition. *)
  Lemma boolean_ind_vc_until_implies_ind_vc :
    forall n u neighbors neighbor_invariants (b : bool) (B : list bool),
      length B = length neighbor_invariants ->
      length neighbors = length neighbor_invariants ->
      A_is_until n u ->
      Forall2 A_is_until neighbors neighbor_invariants ->
      (forall t,
          booleans_are_time_bounds B (map tau neighbor_invariants) t /\
          boolean_equals_time_bound b (1 + t) (tau u)) ->
      boolean_inductive_condition n u neighbors neighbor_invariants ->
       inductive_condition n neighbors.
  Proof.
    unfold inductive_condition, boolean_inductive_condition.
    intros n u neighbors neighbor_invariants b B HBlen Hnbrlen HnUntil HnbrUntil
      HB Hbindvc t states Hstateslen.
    specialize (HB t).
    destruct HB as [HnbrBounds HnBound].
    apply (Hbindvc b B t HBlen HnUntil HnbrUntil HnbrBounds HnBound states) in Hstateslen.
    rewrite <- (untils_have_equivalent_buntils neighbor_invariants B t HBlen HnbrBounds) in Hstateslen.
    rewrite <- (until_has_equivalent_buntil b (1 + t) (tau u) _ _ HnBound) in Hstateslen.
    rewrite HnUntil.
    rewrite (map_ext_curried_Forall2 neighbors neighbor_invariants _ _ t Hnbrlen HnbrUntil).
    apply Hstateslen.
  Qed.

  (** Proof that the inductive condition is equivalent to a boolean inductive condition
      when the booleans represent the time bounds of untils. *)
  Theorem ind_vc_until_boolean_equivalent :
    forall n u neighbors neighbor_invariants (b : bool) (B : list bool),
      length B = length neighbor_invariants ->
      length neighbors = length neighbor_invariants ->
      A_is_until n u ->
      Forall2 A_is_until neighbors neighbor_invariants ->
      (forall t,
          booleans_are_time_bounds B (map tau neighbor_invariants) t /\
          boolean_equals_time_bound b (1 + t) (tau u)) ->
      boolean_inductive_condition n u neighbors neighbor_invariants <->
       inductive_condition n neighbors.
  Proof.
    split.
    apply (boolean_ind_vc_until_implies_ind_vc _ _ _ _ b B H H0 H1 H2 H3).
    apply (ind_vc_until_implies_boolean_ind_vc _ _ _ _ H0).
  Qed.

End UntilNet.

Section SelectiveNet.
  Axiom merge_selectivity : forall s1 s2, s1 = Merge s1 s2 \/ s2 = Merge s1 s2.

  Lemma merge_idempotent :
    forall s, s = Merge s s.
  Proof.
    intros.
    remember (merge_selectivity s s) as H.
    destruct H; auto.
  Qed.

  Definition better_or_eq (s1 s2 : S) :=
    s1 = Merge s1 s2.

  Definition better (s1 s2 : S) :=
    better_or_eq s1 s2 /\ s1 <> s2.

  Infix "⪯" := better_or_eq (at level 20).
  Infix "≺" := better (at level 20).

  Definition better_inv (φ1 φ2 : φ) :=
    forall s1 s2, φ1(s1) -> φ2(s2) -> s1 ⪯ s2.

  Example better_inv1 :
    forall s1 s2, s1 ⪯ s2 -> better_inv (fun s => s = s1) (fun s => s = s2).
  Proof.
    intros s1 s2 Hle.
    unfold better_inv.
    intros s0 s3 Hle1 Hle2.
    congruence.
  Qed.

  Lemma better_or_eq_transitive :
    forall s1 s2 s3 : S, s1 ⪯ s2 -> s2 ⪯ s3 -> s1 ⪯ s3.
  Proof.
    intros.
    rewrite H.
    unfold better_or_eq.
    rewrite merge_associativity.
    rewrite <- H0.
    reflexivity.
  Qed.

  Lemma selective_merge_fold :
    forall s states, In (fold_right Merge s states) (s :: states).
  Proof.
    intros s states.
    induction states.
    - simpl. left. reflexivity.
    - simpl in *. destruct IHstates as [IHs | IHstates].
      + rewrite <- IHs.
        rewrite <- or_assoc.
        left.
        rewrite or_comm.
        apply (merge_selectivity a s).
      + right.
        remember (merge_selectivity a (fold_right Merge s states)) as H.
        destruct H as [Habetter | Hstatesbetter].
        * left. assumption.
        * rewrite <- Hstatesbetter.
          right. assumption.
  Qed.

  Lemma selective_updated_state :
    forall v neighbors states,
      length neighbors = length states ->
      In (updated_state v (combine neighbors states))
        ((I v) :: transfer_routes v (combine neighbors states)).
  Proof.
    intros v neighbors states Hstateslen.
    unfold updated_state.
    (* rewrite fold_right_map. *)
    apply (selective_merge_fold (I v) (transfer_routes v (combine neighbors states))).
  Qed.

  Lemma selective_inductive_condition_selects :
    forall (v : V) (node_invariant : φ) (neighbors : list V) (states : list S) (invariants : list φ),
      length neighbors = length states ->
      length neighbors = length invariants ->
      (* if the inductive condition holds for the given set of invariants... *)
      inductive_condition_untimed v node_invariant (combine neighbors states)
        invariants ->
      Forall2 (fun s p => p (snd s)) (combine neighbors states) invariants  ->
      (* then there exists a state from a particular node that satisfies the invariant and is selected *)
      Exists node_invariant
        ((I v) :: transfer_routes v (combine neighbors states)).
  Proof.
    intros.
    apply Exists_exists.
    exists (updated_state v (combine neighbors states)).
    split.
    apply (selective_updated_state _ _ _ H).
    unfold inductive_condition_untimed in H1.
    rewrite combine_length in H1.
    rewrite <- H in H1.
    rewrite PeanoNat.Nat.min_id in H1.
    apply H1 in H0.
    assumption.
    apply Forall_forall2 in H2.
    2: { rewrite combine_length. rewrite <- H. rewrite PeanoNat.Nat.min_id. apply H0. }
    apply Forall_forall2.
    { rewrite combine_length. rewrite <- H. rewrite PeanoNat.Nat.min_id. apply H0. }
    apply H2.
  Qed.

  Lemma selective_neighbor_pairs_cover_selective_neighbors :
    forall v u1 u2 u3,
      (inductive_condition v (u1 :: u2 :: nil)) ->
      (inductive_condition v (u2 :: u3 :: nil)) ->
      (inductive_condition v (u1 :: u3 :: nil)) ->
      (inductive_condition v (u1 :: u2 :: u3 :: nil)).
  Proof.
    intros v u1 u2 u3 H12 H23 H13.
    unfold inductive_condition in *.
    intros t states Hstateslen.
    unfold inductive_condition_untimed.
    simpl in Hstateslen.
    rewrite combine_length.
    rewrite map_length.
    rewrite Hstateslen.
    rewrite PeanoNat.Nat.min_id.
    intros.
    Abort.
End SelectiveNet.
