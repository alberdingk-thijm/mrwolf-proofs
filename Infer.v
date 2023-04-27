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

Module Type Graph.
  Parameter V : Type.
  Definition E : Type := V * V.
End Graph.

Module Type Net (S: Typ).
  (* Parameter S : Type. *)
  Include Graph.

  Parameter Merge : S.t -> S.t -> S.t.
  Parameter F : E -> S.t -> S.t.
  Parameter I : V -> S.t.

  Axiom merge_associativity : forall s1 s2 s3, Merge (Merge s1 s2) s3 = Merge s1 (Merge s2 s3).
  Axiom merge_commutativity : forall s1 s2, Merge s1 s2 = Merge s2 s1.

  (* interface and predicate definitions *)
  Definition φ := S.t -> Prop.
  Definition Q := nat -> φ.
  Parameter A : V -> Q.

  (* Computing a new route at a node given routes of its neighbors. *)
  Definition updated_state (node : V) (neighbors : list (V * S.t)) : S.t :=
    fold_right (fun (neighbor : (V * S.t)) (st : S.t) =>
                  let (m, ms) := neighbor in
                  Merge st (F (m, node) ms)) (I node) neighbors.

  (* A helper definition for writing out the inductive condition with times
     erased: all invariants are specified as [S.t -> Prop] functions. *)
  Definition inductive_condition_untimed
    (node : V) (node_invariant : φ)
    (neighbors : list (V * S.t)) (neighbor_invariants : list φ) :=
    length neighbors = length neighbor_invariants ->
    (* if every neighbor's route satisfies the invariant φ *)
    (Forall2 (fun m p => p (snd m)) neighbors neighbor_invariants) ->
    (* then the node's invariant holds on the updated state *)
    (node_invariant (updated_state node neighbors)).

  (* The original inductive condition for a node [n]. *)
  Definition inductive_condition (n : V) (neighbors : list V) :=
    forall (t : nat) (states : list S.t),
      length states = length neighbors ->
      inductive_condition_untimed
        n (A n (1 + t))
        (combine neighbors states) (map (fun m => A m t) neighbors).
End Net.

Module Type UntilNet (S: Typ) (Import N: Net S).
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
    - intros. induction B.
      + inversion H.
      + inversion H.
        simpl in *.
        inversion H0.
        simpl in H4.
        apply (until_has_equivalent_buntil _ _ _ (before a) (after a)) in H5.
        unfold construct_until.
        subst.
        rewrite H5.
        f_equal.
        apply IHneighbor_invariants.
        * assumption.
        * assumption.
  Qed.

  Definition boolean_inductive_condition
    (n : V) (b : bool) (u : Until)
    (neighbors : list V) (neighbor_invariants : list Until) (B : list bool) :=
      (* enforce that all invariants are Untils *)
      A_is_until n u ->
      Forall2 A_is_until neighbors neighbor_invariants ->
      (* associate the booleans with the neighbor witness times *)
      forall (t : nat),
        booleans_are_time_bounds B (map tau neighbor_invariants) t ->
        boolean_equals_time_bound b (1 + t) (tau u) ->
      (* define the inductive condition check again, but now using booleans *)
      (forall (states : list S.t),
          length states = length neighbors ->
          inductive_condition_untimed
            n (buntil b (before u) (after u))
            (combine neighbors states)
            (* construct the neighbor invariants with booleans *)
            (map (fun p => buntil (fst p) (before (snd p)) (after (snd p))) (combine B neighbor_invariants))).

  (** Proof that the inductive condition implies the boolean inductive condition. *)
  Lemma ind_vc_until_implies_boolean_ind_vc :
    forall (n : V) (b : bool) (tau : nat) (node_before node_after : φ)
      (neighbors : list V) (neighbor_invariants : list Until) (B : list bool),
      length neighbors = length neighbor_invariants ->
      length B = length neighbor_invariants ->
      inductive_condition n neighbors ->
      boolean_inductive_condition n b (mkUntil tau node_before node_after)
        neighbors neighbor_invariants B.
  Proof using Type.
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
    unfold A_is_until in *.
    unfold construct_until in HnUntil.
    simpl in HnUntil.
    rewrite <- HnUntil.
    replace (map (fun u : Until => construct_until u t) neighbor_invariants) with (map (fun m : V => A m t) neighbors).
    2: {
      clear - HneighborsUntil Hnbrlen.
      (* join the two lists together *)
      rewrite <- (map_project_combine1 neighbors neighbor_invariants (fun m => A m t) Hnbrlen).
      rewrite <- (map_project_combine2 neighbors neighbor_invariants (fun u => construct_until u t) Hnbrlen).
      (* now convert to a Forall *)
      apply map_ext_Forall.
      eapply Forall_impl.
      2: {
        apply Forall_forall2 in HneighborsUntil.
        apply HneighborsUntil.
        assumption.
      }
      intros a H.
      apply (H t).
    }
    assumption.
  Qed.

  (** Proof that the boolean inductive condition implies the inductive condition
      when the premises of the boolean inductive condition are met.
   *)
  Lemma boolean_ind_vc_until_implies_ind_vc_aux :
    forall n b tau' before' after' neighbors neighbor_invariants B t,
      A_is_until n (mkUntil tau' before' after') ->
      Forall2 A_is_until neighbors neighbor_invariants ->
      length B = length neighbor_invariants ->
      booleans_are_time_bounds B (map tau neighbor_invariants) t ->
      boolean_equals_time_bound b (Datatypes.S t) tau' ->
      boolean_inductive_condition n b (mkUntil tau' before' after') neighbors neighbor_invariants B ->
      (* inductive condition for the same time [t] as above *)
      forall states : list S.t,
        length states = length neighbors ->
        inductive_condition_untimed n (until tau' before' after' (1 + t)) (combine neighbors states)
          (map (fun x : Until => construct_until x t) neighbor_invariants).
    Proof using Type.
      intros.
      unfold boolean_inductive_condition in H4.
      apply (H4 H H0 t H2 H3 states) in H5.
      rewrite (untils_have_equivalent_buntils neighbor_invariants B t); try congruence.
      rewrite (until_has_equivalent_buntil b).
      2: { simpl. assumption. }
      assumption.
    Qed.
End UntilNet.

Module Type SelectiveNet (Import S : OrderedTypeFull) (Import N: Net S).
  Include GenericMinMax S.
  Include OrderedTypeLists S.
  Definition better := S.le.
  Definition strictly_better := S.lt.

  Axiom merge_selectivity : forall s1 s2, better s1 s2 -> Merge s1 s2 = s1.

  Infix "⪯" := better (at level 20).
  Infix "≺" := strictly_better (at level 20).

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
End SelectiveNet.
