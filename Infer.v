(* Modular network inference *)
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Lia.

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
    (neighbors : list (Node * S)) (neighbor_invariants : list φ) :=
    length neighbors = length neighbor_invariants ->
    (* if every neighbor's route satisfies the invariant φ *)
    (Forall (fun (c : Node * S * φ) => ((snd c) (snd (fst c)))) (combine neighbors neighbor_invariants)) ->
    (* then the node's invariant holds on the updated state *)
    (node_invariant (updated_state node initial neighbors)).

  (* The original inductive condition for a node [n]. *)
  Definition inductive_condition (n : Node) (initial : S) (node_invariant : A)
                                 (neighbors : list Node) (neighbor_invariants : list A) :=
    forall (t : nat) (states : list S),
      length states = length neighbors ->
      inductive_condition_untimed
        n initial (node_invariant (1 + t))
        (combine neighbors states) (map (fun a => (a t)) neighbor_invariants).

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

  Definition boolean_inductive_condition
    (n : Node) (initial : S) (b : bool) (u : Until)
    (neighbors : list Node) (neighbor_invariants : list Until) (B : list bool) :=
      (* associate the booleans with the neighbor witness times *)
      forall (t : nat),
        booleans_are_time_bounds (combine B (map tau neighbor_invariants)) t ->
        boolean_equals_time_bound b (1 + t) (tau u) ->
      (* define the inductive condition check again, but now using booleans *)
      (forall (states : list S),
          length states = length neighbors ->
          inductive_condition_untimed
            n initial (buntil b (before u) (after u))
            (combine neighbors states)
            (* construct the neighbor invariants with booleans *)
            (map (fun p => buntil (fst p) (before (snd p)) (after (snd p))) (combine B neighbor_invariants))).

  Lemma ind_vc_until_implies_boolean_ind_vc :
    forall (n : Node) (initial : S) (b : bool) (tau : nat) (node_before node_after : φ)
      (neighbors : list Node) (neighbor_invariants : list Until) (B : list bool),
      length neighbors = length neighbor_invariants ->
        length B = length neighbor_invariants ->
      inductive_condition n initial (until tau node_before node_after)
        neighbors (map construct_until neighbor_invariants) ->
      boolean_inductive_condition n initial b (mkUntil tau node_before node_after)
        neighbors neighbor_invariants B.
  Proof.
    unfold
      inductive_condition,
      boolean_inductive_condition,
      booleans_are_time_bounds.
    simpl.
    intros n initial b tau' node_before node_after.
    intros neighbors neighbor_invariants B Hnbrlen Hblen Hindvc t Hnbr_bounds Hn_bound states Hstateslen.
    (* match up the until and buntil *)
    apply (until_has_equivalent_buntil _ _ _ node_before node_after) in Hn_bound.
    rewrite <- Hn_bound.
    apply (untils_have_equivalent_buntils neighbor_invariants B t) in Hblen.
    2: { assumption. }
    rewrite <- Hblen.
    apply (Hindvc t states) in Hstateslen.
    rewrite map_map in Hstateslen.
    assumption.
  Qed.

  Lemma boolean_ind_vc_until_implies_ind_vc_aux :
    forall n initial b tau' before' after' neighbors neighbor_invariants B t,
      length B = length neighbor_invariants ->
      booleans_are_time_bounds (combine B (map tau neighbor_invariants)) t ->
      boolean_equals_time_bound b (Datatypes.S t) tau' ->
      (forall (states : list S),
          length states = length neighbors ->
          inductive_condition_untimed n initial (buntil b before' after')
            (combine neighbors states)
            (* construct the neighbor invariants with booleans *)
            (map (fun p => buntil (fst p) (before (snd p)) (after (snd p))) (combine B neighbor_invariants))) ->
      forall states : list S,
        length states = length neighbors ->
        inductive_condition_untimed n initial (until tau' before' after' (1 + t)) (combine neighbors states)
          (map (fun x : Until => construct_until x t) neighbor_invariants).
    Proof.
      intros.
      specialize (H2 states).
      apply H2 in H3.
      rewrite (untils_have_equivalent_buntils neighbor_invariants B t); try congruence.
      rewrite (until_has_equivalent_buntil b).
      2: { simpl. assumption. }
      assumption.
    Qed.
End timepiece.
