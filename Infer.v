(* Modular network inference *)
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Lia.
Require Import Coq.Classes.RelationClasses.
Require Import Classical.
From MrWolf Require Import Combine.

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

Lemma Forall2_app_inv :
  forall { T1 T2 : Type }
    (l1 l2 : list T1) (l3 l4 : list T2)
    (P : T1 -> T2 -> Prop),
    length l1 = length l3 ->
    length l2 = length l4 ->
    Forall2 P (l1 ++ l2) (l3 ++ l4) ->
    Forall2 P l1 l3 /\ Forall2 P l2 l4.
Proof.
  intros.
  generalize dependent l4.
  generalize dependent l3.
  generalize dependent l2.
  induction l1; intros.
  - symmetry in H.
    rewrite length_zero_iff_nil in H.
    subst.
    simpl in H1.
    split; (constructor || assumption).
  - destruct l3 as [| ? l3]; try solve[inversion H].
    inversion H.
    specialize (IHl1 l2 l3 H3 l4 H0).
    simpl in H1.
    apply Forall2_cons_iff in H1.
    destruct H1.
    specialize (IHl1 H2).
    destruct IHl1.
    split; ((constructor; assumption) || (repeat assumption)).
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

Lemma app_inv_Exists :
  forall {T1 T2 : Type} (l1 l2 : list T1) (l : list T2),
    length l = length (l1 ++ l2) ->
    exists (l3 l4 : list T2),
      l = l3 ++ l4 /\ length l3 = length l1 /\ length l4 = length l2.
Proof.
  induction l1; intros.
  - simpl in *. exists nil. exists l.
    rewrite app_nil_l in *.
    repeat split; try reflexivity.
    assumption.
  - simpl in *.
    rewrite app_length in *.
    simpl in H.
    rewrite plus_n_Sm in H.
    specialize (IHl1 (a :: l2) l).
    rewrite H in IHl1.
    rewrite app_length in IHl1.
    simpl in IHl1.
    specialize (IHl1 eq_refl).
    destruct IHl1 as [l3 [l4 [Hl [Hl3 Hl4]]]].
    rewrite <- Hl3.
    destruct l4 as [| ? l4]; try solve[inversion Hl4].
    injection Hl4 as Hl4.
    rewrite Hl.
    simpl.
    exists (l3 ++ (t :: nil)).
    exists l4.
    rewrite <- app_assoc.
    rewrite app_length.
    simpl.
    rewrite PeanoNat.Nat.add_1_r.
    repeat split; try reflexivity.
    assumption.
Qed.

Section Net.
  (* interface and predicate definitions *)
  Definition φ (S : Type) := S -> Prop.
  Definition Q (S : Type) := nat -> φ S.

  Class Net V S : Type :=
    {
      Merge : S -> S -> S;
      F : V -> V -> S -> S;
      I : V -> S;
      merge_assoc : forall s1 s2 s3, Merge s1 (Merge s2 s3) = Merge (Merge s1 s2) s3;
      merge_comm : forall s1 s2, Merge s1 s2 = Merge s2 s1;
      A : V -> nat -> S -> Prop
    }.

  Lemma fold_right_merge_permute {V S : Type} `{H: Net V S} :
    forall s states1 states2,
      Permutation states1 states2 ->
      fold_right Merge s states1 = fold_right Merge s states2.
  Proof.
    intros.
    induction H0.
    - constructor.
    - simpl. rewrite IHPermutation. reflexivity.
    - simpl. rewrite merge_assoc. rewrite merge_assoc.
      replace (Merge y x)
                with (Merge x y).
      2: apply merge_comm.
      reflexivity.
    - congruence.
  Qed.

  Lemma fold_right_merge_comm  {V S : Type} `{H: Net V S}:
    forall s1 s2 states,
      fold_right Merge s1 (s2 :: states) = fold_right Merge s2 (s1 :: states).
  Proof.
    induction states.
    - simpl. apply merge_comm.
    - simpl.
      simpl in IHstates.
      rewrite merge_assoc.
      rewrite (merge_comm s2 a).
      rewrite <- merge_assoc.
      rewrite IHstates.
      rewrite merge_assoc.
      rewrite merge_assoc.
      rewrite (merge_comm a s1).
      reflexivity.
  Qed.

  Definition transfer_routes {V S : Type} `{H: Net V S} (node : V) (neighbors : list (V * S)) :=
    (map (fun (neighbor : (V * S)) => F (fst neighbor) node (snd neighbor)) neighbors).

  Definition updated_state {V S : Type} `{H: Net V S} (node : V) (neighbors : list (V * S)) : S :=
    fold_right Merge (I node) (transfer_routes node neighbors).

  Corollary state_updates_comm {V S : Type} `{H: Net V S} :
    forall (v : V) (neighbors1 : list (V * S)) (neighbors2 : list (V * S)),
      Permutation neighbors1 neighbors2 ->
      updated_state v neighbors1 = updated_state v neighbors2.
  Proof.
    unfold updated_state, transfer_routes.
    intros.
    apply fold_right_merge_permute.
    apply Permutation_map.
    assumption.
  Qed.

  Corollary state_updates_app_comm  {V S : Type} `{H: Net V S} :
    forall (v : V) (neighbors1 : list (V * S)) (neighbors2 : list (V * S)),
      updated_state v (neighbors1 ++ neighbors2) = updated_state v (neighbors2 ++ neighbors1).
  Proof.
    intros.
    apply state_updates_comm.
    apply Permutation_app_comm.
  Qed.

  (* A helper definition for writing out the inductive condition with times
     erased: all invariants are specified as [S -> Prop] functions. *)
  Definition inductive_cond_untimed {V S : Type} `{H: Net V S}
    (node : V) (node_invariant : φ S)
    (neighbors : list (V * S)) (neighbor_invariants : list (φ S)) :=
    length neighbors = length neighbor_invariants ->
    (* if every neighbor's route satisfies the invariant φ *)
    (Forall2 (fun m p => p (snd m)) neighbors neighbor_invariants) ->
    (* then the node's invariant holds on the updated state *)
    (node_invariant (updated_state node neighbors)).

  Lemma inductive_cond_untimed_comm {V S : Type} `{H: Net V S} :
    forall (v : V) (inv : φ S) (neighbors1 neighbors2 : list (V * S)) (invs1 invs2 : list (φ S)),
      Permutation neighbors1 neighbors2 ->
      Permutation invs1 invs2 ->
      Permutation (combine neighbors1 invs1) (combine neighbors2 invs2) ->
      inductive_cond_untimed v inv neighbors1 invs1 <-> inductive_cond_untimed v inv neighbors2 invs2.
  Proof.
    intros v inv neighbors1 neighbors2 invs1 invs2 HPermNeighbors HPermInvs HPermCombined.
    (* get some facts about the list lengths *)
    assert (HPermNeighbors' := HPermNeighbors).
    apply Permutation_length in HPermNeighbors'.
    assert (HPermInvs' := HPermInvs).
    apply Permutation_length in HPermInvs'.
    assert (HPermCombined' := HPermCombined).
    apply Permutation_length in HPermCombined'.
    (* now do induction on HPermNeighbors *)
    induction HPermNeighbors.
    - (* nil cases *)
      split; intro; intros Hstateslen Hnbrs; inversion Hstateslen;
        symmetry in H2; rewrite length_zero_iff_nil in H2; subst.
      + apply Permutation_sym in HPermInvs.
        apply Permutation_nil in HPermInvs.
        subst.
        apply (H0 Hstateslen Hnbrs).
      + apply Permutation_nil in HPermInvs.
        subst.
        apply (H0 Hstateslen Hnbrs).
    - (* skip cases*)
      split; intro; intros Hstateslen Hnbrs; inversion Hstateslen.
      + rewrite (state_updates_comm _ (x :: l') (x :: l));
          try (constructor; apply Permutation_sym; assumption).
        rewrite Forall_forall2 in Hnbrs; try assumption.
        apply H0; try congruence.
        rewrite Forall_forall2.
        apply Permutation_sym in HPermCombined.
        eapply Permutation_Forall in HPermCombined.
        apply HPermCombined.
        apply Hnbrs.
        simpl. simpl in HPermNeighbors'. rewrite HPermNeighbors'. rewrite H2. symmetry. assumption.
      + rewrite (state_updates_comm _ (x :: l) (x :: l'));
          try (constructor; assumption).
        rewrite Forall_forall2 in Hnbrs; try assumption.
        apply H0; try congruence.
        rewrite Forall_forall2.
        eapply Permutation_Forall in HPermCombined.
        apply HPermCombined.
        apply Hnbrs.
        rewrite <- HPermNeighbors. simpl. rewrite H2. assumption.
    - (* swap cases *)
      split; intro; intros Hstateslen Hnbrs; inversion Hstateslen;
        rewrite Forall_forall2 in Hnbrs; try assumption.
      + rewrite (state_updates_comm _ (x :: y :: l) (y :: x :: l)).
        2: constructor.
        apply H0.
        congruence.
        rewrite Forall_forall2.
        apply Permutation_sym in HPermCombined.
        eapply Permutation_Forall in HPermCombined.
        apply HPermCombined.
        apply Hnbrs.
        rewrite HPermNeighbors'. rewrite Hstateslen. symmetry. assumption.
      + rewrite (state_updates_comm _ (y :: x :: l) (x :: y :: l)).
        2: constructor.
        apply H0.
        congruence.
        rewrite Forall_forall2.
        eapply Permutation_Forall in HPermCombined.
        apply HPermCombined.
        apply Hnbrs.
        rewrite <- HPermNeighbors'. rewrite Hstateslen. assumption.
    - (* trans cases*)
      split; intro; intros Hstateslen Hnbrs;
        rewrite Forall_forall2 in Hnbrs; try assumption.
      + rewrite (state_updates_comm _ l'' l').
        2: apply Permutation_sym; assumption.
        rewrite (state_updates_comm _ l' l).
        2: apply Permutation_sym; assumption.
        apply H0.
        congruence.
        rewrite Forall_forall2.
        apply Permutation_sym in HPermCombined.
        eapply Permutation_Forall in HPermCombined.
        apply HPermCombined.
        apply Hnbrs.
        rewrite HPermNeighbors'. rewrite Hstateslen. symmetry. assumption.
      + rewrite (state_updates_comm _ l l'); try assumption.
        rewrite (state_updates_comm _ l' l''); try assumption.
        apply H0; try congruence.
        rewrite Forall_forall2.
        eapply Permutation_Forall in HPermCombined.
        apply HPermCombined.
        apply Hnbrs.
        rewrite <- HPermNeighbors'. rewrite Hstateslen. assumption.
  Qed.

  (* The original inductive condition for a node [n]. *)
  Definition inductive_cond {V S : Type} `{H: Net V S} (n : V) (neighbors : list V) :=
    forall (t : nat) (states : list S),
      length states = length neighbors ->
      inductive_cond_untimed
        n (A n (1 + t))
        (combine neighbors states) (map (fun m => A m t) neighbors).

  Lemma inductive_cond_comm {V S : Type} `{H: Net V S} :
    forall (v : V) (neighbors1 : list V) (neighbors2 : list V),
      Permutation neighbors1 neighbors2 ->
      inductive_cond v neighbors1 <-> inductive_cond v neighbors2.
  Proof.
    intros.
    unfold inductive_cond.
    split; intro.
    - intros t states2 Hstateslen.
      assert (H0' := H0).
      apply Permutation_sym in H0.
      apply (Permutation_combine_Exists neighbors2 neighbors1 states2) in H0.
      destruct H0 as [states1 Hstates].
      eapply inductive_cond_untimed_comm.
      apply Hstates.
      apply Permutation_sym.
      4: apply H1.
      2: apply Permutation_map; apply Permutation_sym; assumption.
      (* We need to prove that, if the inductive condition holds for neighbors [x :: l],
         then it will hold for neighbors [x :: l'] when l' is a permutation of l.
         The inductive hypothesis isn't useful here, since we can't use l or l' to understand
         the result for [x :: l] and [x :: l'].
         Instead, we need to be able to claim that we have two state permutations such that
         [Permutation (combine l states) (combine l' states')], so that the invariants all align. *)
  Abort.
End Net.

Section NetExamples.
  Instance boolNet : Net nat bool :=
    {
      Merge := orb;
      F := fun u v s => s;
      I := fun v => if (v =? 0) then true else false;
      merge_assoc := Bool.orb_assoc;
      merge_comm := Bool.orb_comm;
      A := fun v => if (v =? 0) then (fun t s => s = true) else
                   (fun t s => if (t <? 1) then True else s = true)
    }.

  Example ind_vc0 :
    inductive_cond 0 (1 :: 2 :: nil).
  Proof.
    unfold inductive_cond, inductive_cond_untimed.
    intros.
    do 2 (destruct states as [| ? states]; try solve[inversion H]).
    unfold updated_state.
    simpl.
    do 2 rewrite Bool.orb_true_r.
    reflexivity.
  Qed.

  Example ind_vc1 :
    inductive_cond 1 (0 :: 2 :: nil).
  Proof.
    unfold inductive_cond, inductive_cond_untimed.
    intros.
    do 2 (destruct states as [| ? states]; try solve[inversion H]).
    inversion H1.
    subst.
    inversion H7.
    subst.
    simpl in H6.
    simpl.
    unfold updated_state.
    simpl.
    rewrite Bool.orb_false_r.
    destruct t.
    - simpl in H5. rewrite H5. simpl. reflexivity.
    - simpl in H6. rewrite H6. rewrite Bool.orb_true_r. reflexivity.
  Qed.
End NetExamples.

Section UntilNet.
  (* The until temporal operator. *)
  Definition until {S : Type} (tau : nat) (before after : φ S) : Q S :=
    fun t s => if t <? tau then before s else after s.

  (* The until operator, with a boolean instead of a time bound. *)
  Definition buntil {S : Type} (b : bool) (before after : φ S) : φ S :=
    fun s => if b then before s else after s.

  Example until_example1 :
    forall (S : Type) (s : S) φ, (until 0 φ (fun _ => True)) 1 s.
  Proof. reflexivity. Qed.

  Example buntil_example1 :
    forall (S : Type) (s : S) φ, buntil false φ (fun _ => True) s.
  Proof. reflexivity. Qed.

  (* A type of network where all invariants are untils. *)
  Class UntilNet V S `{Net V S} : Type :=
    {
      τ : V -> nat;
      ϕ : V -> φ S;
      ψ : V -> φ S;
      A_until : forall v t, A v t = until (τ v) (ϕ v) (ψ v) t
    }.

  Lemma A_until_Forall {V S : Type} `{UntilNet V S}:
    forall (nodes : list V) (t : nat),
      Forall (fun n => A n t = until (τ n) (ϕ n) (ψ n) t) nodes.
  Proof.
    intros.
    apply Forall_forall.
    intros.
    rewrite A_until.
    reflexivity.
  Qed.

  Definition boolean_equals_time_bound (b : bool) (t tau : nat) :=
    b = (t <? tau).

  (* Lemma relating until and buntil. *)
  Lemma until_has_equivalent_buntil {S : Type}:
    forall (b : bool) (t tau : nat) (φ1 φ2 : φ S),
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
  Lemma untils_have_equivalent_buntils {V S : Type} `{UntilNet V S}:
    forall (nodes : list V) (B : list bool) (t : nat),
      length nodes = length B ->
      (* if every boolean is associated with a time bound, *)
      booleans_are_time_bounds B (map τ nodes) t ->
        (* then a list of invariants with explicit times *)
        map (fun n => until (τ n) (ϕ n) (ψ n) t) nodes =
          (* equals a list of invariants with Bs *)
          map (fun (bu : bool * V) => buntil (fst bu) (ϕ (snd bu)) (ψ (snd bu)))
            (combine B nodes).
  Proof using Type.
    intros nodes.
    induction nodes.
    - intros. rewrite combine_nil. reflexivity.
    - intros. induction B; inversion H1.
      simpl in *.
      inversion H2.
      apply (until_has_equivalent_buntil _ _ _ (ϕ a) (ψ a)) in H7.
      subst.
      rewrite H7.
      f_equal.
      apply IHnodes; assumption.
  Qed.

  Definition boolean_inductive_cond {V S : Type} `{H : UntilNet V S}
    (n : V) (neighbors : list V) :=
      forall (b : bool) (B : list bool) (t : nat),
        length neighbors = length B ->
        booleans_are_time_bounds B (map τ neighbors) t ->
        (* Forall2 (fun m b => boolean_equals_time_bound b t (τ m)) neighbors B -> *)
        boolean_equals_time_bound b (1 + t) (τ n) ->
        (* define the inductive condition check again, but now using booleans *)
        (forall (states : list S),
            length states = length neighbors ->
            inductive_cond_untimed
              n (buntil b (ϕ n) (ψ n))
              (combine neighbors states)
              (* construct the neighbor invariants with booleans *)
              (map (fun p => buntil (fst p) (ϕ (snd p)) (ψ (snd p))) (combine B neighbors))).

  (** Proof that the inductive condition implies the boolean inductive condition. *)
  Lemma ind_vc_until_implies_boolean_ind_vc {V S : Type} `{H : UntilNet V S}:
    forall (n : V) (neighbors : list V),
      inductive_cond n neighbors ->
      boolean_inductive_cond n neighbors.
  Proof using Type.
    unfold inductive_cond, booleans_are_time_bounds.
    simpl.
    intros n neighbors Hindvc
      b B t Hblen Hnbr_bounds Hn_bound states Hstateslen.
    specialize (Hindvc t states Hstateslen).
    (* match up the until and buntil *)
    apply (until_has_equivalent_buntil _ _ _ (ϕ n) (ψ n)) in Hn_bound.
    rewrite <- Hn_bound.
    apply (untils_have_equivalent_buntils neighbors B t Hblen) in Hnbr_bounds.
    rewrite <- Hnbr_bounds.
    rewrite <- A_until.
    replace (map (fun n0 : V => until (τ n0) (ϕ n0) (ψ n0) t) neighbors) with
      (map (fun n0 => A n0 t) neighbors).
    apply Hindvc.
    apply map_ext_Forall.
    apply A_until_Forall.
  Qed.

  (** Proof that the boolean inductive condition implies the inductive condition. *)
  Lemma boolean_ind_vc_until_implies_ind_vc {V S : Type} `{H : UntilNet V S}:
    forall n neighbors (b : bool) (B : list bool),
      length neighbors = length B ->
      (forall t,
          booleans_are_time_bounds B (map τ neighbors) t /\
          boolean_equals_time_bound b (1 + t) (τ n)) ->
      boolean_inductive_cond n neighbors ->
       inductive_cond n neighbors.
  Proof.
    unfold inductive_cond.
    intros n neighbors b B HBlen HB Hbindvc t states Hstateslen.
    specialize (HB t).
    destruct HB as [HnbrBounds HnBound].
    apply (Hbindvc b B t HBlen HnbrBounds HnBound states) in Hstateslen.
    rewrite <- (untils_have_equivalent_buntils neighbors B t HBlen HnbrBounds) in Hstateslen.
    rewrite <- (until_has_equivalent_buntil b (1 + t) (τ n) _ _ HnBound) in Hstateslen.
    rewrite A_until.
    replace (map (fun n0 => A n0 t) neighbors) with (map (fun n0 : V => until (τ n0) (ϕ n0) (ψ n0) t) neighbors).
    apply Hstateslen.
    symmetry.
    apply map_ext_Forall.
    apply A_until_Forall.
  Qed.

  (** Proof that the inductive condition is equivalent to a boolean inductive condition
      when the booleans represent the time bounds of untils. *)
  Theorem ind_vc_until_boolean_equivalent {V S : Type} `{H : UntilNet V S}:
    forall n neighbors (b : bool) (B : list bool),
      length neighbors = length B ->
      (forall t,
          booleans_are_time_bounds B (map τ neighbors) t /\
          boolean_equals_time_bound b (1 + t) (τ n)) ->
      boolean_inductive_cond n neighbors <->
       inductive_cond n neighbors.
  Proof.
    split.
    apply (boolean_ind_vc_until_implies_ind_vc _ _ b B H1 H2).
    apply (ind_vc_until_implies_boolean_ind_vc _ _).
  Qed.
End UntilNet.

Section SelectiveNet.
  Class SelectiveNet V S `{Net V S} `{O: PartialOrder S} : Type :=
    {
      merge_select : forall s1 s2, s1 = Merge s1 s2 \/ s2 = Merge s1 s2;
      merge_order : forall s1 s2, s1 = Merge s1 s2 <-> R s1 s2
    }.

  Instance NatNet : Net nat nat :=
    {
      Merge := PeanoNat.Nat.min;
      F := fun u v s => 1 + s;
      I := fun v => if (v =? 0) then 0 else 16;
      merge_assoc := PeanoNat.Nat.min_assoc;
      merge_comm := PeanoNat.Nat.min_comm;
      A := fun v => if (v =? 0) then (fun t s => s = 0) else
                   (fun t s => if (t <? 1) then True else s = 1);
      (* merge_order := PeanoNat.Nat.min_l; *)
    }.

  Lemma min_select :
    forall m n, m = min m n \/ n = min m n.
  Proof. lia. Qed.

  Lemma min_order :
    forall m n, m = min m n <-> m <= n.
  Proof. lia. Qed.

  Instance SelectiveNatNet : SelectiveNet nat nat :=
    {
      merge_select := min_select;
      merge_order := min_order;
    }.

  Example ind_vc2 :
    inductive_cond 2 (0 :: 1 :: nil).
  Proof.
    unfold inductive_cond, inductive_cond_untimed, updated_state.
    intros.
    do 3 (destruct states as [| ? states]; try solve[inversion H]).
    simpl.
    inversion H1.
    simpl in H5.
    subst.
    lia.
  Qed.

  Lemma merge_idempotent {V S : Type} `{H: SelectiveNet V S} :
    forall s, s = Merge s s.
  Proof.
    intros.
    apply merge_order.
    apply preo.
  Qed.

  Lemma merge_inv_l {V S : Type} `{H: SelectiveNet V S} :
    forall s1 s2 s3, s1 = s3 -> Merge s1 s2 = Merge s3 s2.
  Proof. intros. congruence. Qed.

  Lemma merge_inv_r {V S : Type} `{H: SelectiveNet V S}:
    forall s1 s2 s3, s2 = s3 -> Merge s1 s2 = Merge s1 s3.
  Proof. intros. congruence. Qed.

  Definition better_or_eq {V S : Type} `{H: SelectiveNet V S} (s1 s2 : S) :=
    R s1 s2.

  Definition better {V S : Type} `{H: SelectiveNet V S} (s1 s2 : S) :=
    R s1 s2 /\ s1 <> s2.

  Infix "⪯" := better_or_eq (at level 20).
  Infix "≺" := better (at level 20).

  Definition better_inv {V S : Type} `{H: SelectiveNet V S} (φ1 φ2 : φ S) :=
    forall s2, exists s1, φ1(s1) -> φ2(s2) -> s1 ⪯ s2.

  Corollary better_inv_trans  {V S : Type} `{H: SelectiveNet V S} :
    forall (φ1 φ2 φ3 : φ S),
      better_inv φ1 φ2 ->
      better_inv φ2 φ3 ->
      better_inv φ1 φ3.
  Proof.
    unfold better_inv in *.
    intros.
    eexists.
    intros.
    apply preo.
  Qed.

  Example better_inv1 {V S : Type} `{H: SelectiveNet V S}:
    forall s1 s2, s1 ⪯ s2 -> better_inv (fun s => s = s1) (fun s => s = s2).
  Proof.
    intros s1 s2 Hle.
    unfold better_inv.
    intros s0.
    exists s0. intros Hle1 Hle2.
    congruence.
  Qed.

  Lemma fold_right_merge_In {V S : Type} `{H: SelectiveNet V S}:
    forall s states, In (fold_right Merge s states) (s :: states).
  Proof.
    intros.
    induction states.
    - simpl. left. reflexivity.
    - simpl.
      inversion IHstates.
      + rewrite <- H1.
        rewrite <- or_assoc.
        left.
        rewrite merge_comm.
        apply merge_select.
      + remember (merge_select a (fold_right Merge s states)) as Hselect.
        destruct Hselect as [Ha | Hfold].
        right. left. assumption.
        right. right. rewrite <- Hfold. assumption.
  Qed.

  Lemma fold_right_merge_Forall_neg {V S : Type} `{H: SelectiveNet V S} :
    forall s states P,
      Forall (fun x => ~ P x) (s :: states) ->
      ~ P (fold_right Merge s states).
  Proof.
    intros.
    rewrite Forall_Exists_neg in H1.
    rewrite Exists_exists in H1.
    intro contra.
    apply H1.
    exists (fold_right Merge s states).
    split.
    - apply fold_right_merge_In.
    - apply contra.
  Qed.

  Lemma fold_right_merge_idemp  {V S : Type} `{H: SelectiveNet V S}:
    forall s states,
      fold_right Merge s (s :: states) = fold_right Merge s states.
  Proof.
    intros.
    induction states.
    - simpl. symmetry. apply merge_idempotent.
    - simpl. rewrite (merge_comm a (fold_right Merge s states)). rewrite merge_assoc.
      simpl in IHstates.
      rewrite IHstates.
      reflexivity.
  Qed.

  Lemma fold_right_merge_init2 {V S : Type} `{H: SelectiveNet V S}:
    forall s states1 states2,
      Merge (fold_right Merge s states1) (fold_right Merge s states2)
      = fold_right Merge s (states1 ++ states2).
  Proof.
    intros s states1.
    induction states1; intros.
    - simpl.
      replace (Merge s (fold_right Merge s states2)) with (fold_right Merge s (s :: states2)) by reflexivity.
      rewrite fold_right_merge_idemp.
      reflexivity.
    - simpl. rewrite <- merge_assoc. apply merge_inv_r. apply IHstates1.
  Qed.

  (* Proof that the result of merge is the best of all states. *)
  Lemma selective_merge_best {V S : Type} `{H: SelectiveNet V S}:
    forall s1 s2 states, In s2 (s1 :: states) -> (fold_right Merge s1 states) ⪯ s2.
  Proof.
    intros s1 s2 states.
    induction states; intros Hin.
    - inversion Hin.
      + simpl. subst. apply preo.
      + inversion H1.
    - (* we now need to show that, if the best route is the merge of
         s1, a and states, then all [s2] in [s1 :: a :: states] will be greater than best. *)
      simpl.
      apply merge_order.
      rewrite <- merge_assoc.
      assert (Hin_swap: In s2 (s1 :: a :: states) -> In s2 (a :: s1 :: states)).
      { intro. inversion Hin. subst. apply in_cons. apply in_eq.
        inversion H2. subst. apply in_eq. apply in_cons. apply in_cons. apply H3. }
      apply Hin_swap in Hin.
      inversion Hin.
      + subst. symmetry. rewrite merge_comm. rewrite <- merge_assoc. rewrite <- merge_idempotent.
        rewrite merge_comm. reflexivity.
      + apply IHstates in H1.
        apply merge_order in H1.
        rewrite <- H1. reflexivity.
  Qed.

  Lemma selective_updated_state {V S : Type} `{H: SelectiveNet V S}:
    forall v neighbors s states,
      length neighbors = length states ->
      (* every state received at the node... *)
      In s ((I v) :: transfer_routes v (combine neighbors states)) ->
      (* is at best equal to the updated state *)
      (updated_state v (combine neighbors states)) ⪯ s.
  Proof.
    intros v neighbors s states Hstateslen Hin.
    unfold updated_state.
    apply selective_merge_best.
    apply Hin.
  Qed.

  Corollary updated_state_chosen { V S : Type } `{H: SelectiveNet V S}:
    forall v neighbors states,
      length neighbors = length states ->
      In (updated_state v (combine neighbors states)) ((I v) :: transfer_routes v (combine neighbors states)).
  Proof.
    intros.
    unfold updated_state.
    apply fold_right_merge_In.
  Qed.

  Lemma selective_inductive_cond_selects {V S : Type} `{H: SelectiveNet V S}:
    forall (v : V) (node_invariant : φ S) (neighbors : list V) (states : list S) (invariants : list (φ S)),
      length neighbors = length states ->
      length neighbors = length invariants ->
      (* if the inductive condition holds for the given set of invariants... *)
      inductive_cond_untimed v node_invariant (combine neighbors states) invariants ->
      Forall2 (fun s p => p (snd s)) (combine neighbors states) invariants  ->
      (* then there exists a state from a particular node that satisfies the invariant and is selected *)
      Exists node_invariant
        ((I v) :: transfer_routes v (combine neighbors states)).
  Proof.
    intros.
    unfold inductive_cond_untimed in H3.
    rewrite combine_length in H3.
    rewrite <- H1 in H3.
    rewrite PeanoNat.Nat.min_id in H3.
    specialize (H3 H2 H4).
    apply Exists_exists.
    exists (updated_state v (combine neighbors states)).
    split; try assumption.
    (* show that the updated state is one of the choices *)
    apply updated_state_chosen.
    apply H1.
  Qed.

  Lemma selective_inductive_cond_untimed_join {V S : Type} `{H: SelectiveNet V S}:
    forall (v : V) (inv : φ S) (neighbors1 neighbors2 : list V) (states1 states2 : list S) (invs1 invs2 : list (φ S)),
      length neighbors1 = length states1 ->
      length neighbors1 = length invs1 ->
      length neighbors2 = length states2 ->
      length neighbors2 = length invs2 ->
      inductive_cond_untimed v inv (combine neighbors1 states1) invs1 ->
      inductive_cond_untimed v inv (combine neighbors2 states2) invs2 ->
      inductive_cond_untimed v inv (combine neighbors1 states1 ++ combine neighbors2 states2) (invs1 ++ invs2).
  Proof.
    intros.
    unfold inductive_cond_untimed in *.
    simpl.
    intros Hstateslen Hnbrs.
    apply Forall2_app_inv in Hnbrs.
    destruct Hnbrs as [Hnbrs1 Hnbrs2].
    rewrite combine_length in H5, H6.
    2,3: rewrite combine_length.
    rewrite <- H1 in H5.
    2: rewrite <- H1.
    rewrite <- H3 in H6.
    3: rewrite <- H3.
    rewrite PeanoNat.Nat.min_id in H5, H6.
    2, 3: rewrite PeanoNat.Nat.min_id; assumption.
    specialize (H5 H2 Hnbrs1).
    specialize (H6 H4 Hnbrs2).
    unfold updated_state.
    unfold transfer_routes.
    rewrite map_app.
    fold (transfer_routes v (combine neighbors1 states1)).
    fold (transfer_routes v (combine neighbors2 states2)).
    destruct (merge_select (updated_state v (combine neighbors1 states1))
                           (updated_state v (combine neighbors2 states2))).
    - rewrite H7 in H5.
      unfold updated_state in H5.
      rewrite fold_right_merge_init2 in H5.
      apply H5.
    - rewrite H7 in H6.
      unfold updated_state in H6.
      rewrite fold_right_merge_init2 in H6.
      apply H6.
  Qed.

  Lemma selective_inductive_cond_untimed_join_fail {V S : Type} `{H: SelectiveNet V S}:
    forall (v : V) (inv : φ S) (neighbors1 neighbors2 : list V) (states1 states2 : list S) (invs1 invs2 : list (φ S)),
      length neighbors1 = length states1 ->
      length neighbors1 = length invs1 ->
      length neighbors2 = length states2 ->
      length neighbors2 = length invs2 ->
      ~ inductive_cond_untimed v inv (combine neighbors1 states1) invs1 ->
      ~ inductive_cond_untimed v inv (combine neighbors2 states2) invs2 ->
      ~ inductive_cond_untimed v inv (combine neighbors1 states1 ++ combine neighbors2 states2) (invs1 ++ invs2).
  Proof.
    intros.
    unfold inductive_cond_untimed in *.
    repeat (apply imply_to_and in H5; destruct H5 as [? H5]).
    repeat (apply imply_to_and in H6; destruct H6 as [? H6]).
    intro contra.
    do 2 rewrite app_length in contra.
    do 2 rewrite combine_length in contra.
    rewrite <- H1, <- H3 in contra.
    do 2 rewrite PeanoNat.Nat.min_id in contra.
    rewrite H2, H4 in contra.
    specialize (contra eq_refl).
    assert (HForallcombine:
           Forall2 (fun (m : V * S) (p : S -> Prop) => p (snd m))
            (combine neighbors1 states1 ++ combine neighbors2 states2)
            (invs1 ++ invs2)).
    { apply List.Forall2_app; assumption. }
    specialize (contra HForallcombine).
    unfold updated_state, transfer_routes in contra.
    rewrite map_app in contra.
    fold (transfer_routes v (combine neighbors1 states1)) in contra.
    fold (transfer_routes v (combine neighbors2 states2)) in contra.
    destruct (merge_select (updated_state v (combine neighbors1 states1))
                           (updated_state v (combine neighbors2 states2))) as [Hselect1 | Hselect2].
    - unfold updated_state in Hselect1. rewrite fold_right_merge_init2 in Hselect1.
      rewrite <- Hselect1 in contra.
      apply H5. apply contra.
    - unfold updated_state in Hselect2. rewrite fold_right_merge_init2 in Hselect2.
      rewrite <- Hselect2 in contra.
      apply H6. apply contra.
  Qed.

  Lemma selective_inductive_cond_untimed_join_idemp {V S : Type} `{H: SelectiveNet V S}:
    forall (u1 u2 v : V) (state1 state2 : S) (invv invu : φ S) (neighbors : list V) (states : list S) (invs : list (φ S)),
      length neighbors = length states ->
      length neighbors = length invs ->
      inductive_cond_untimed v invv (combine (u1 :: u2 :: neighbors) (state1 :: state2 :: states)) (invu :: invu :: invs) ->
      inductive_cond_untimed v invv (combine (u1 :: neighbors) (state1 :: states)) (invu :: invs).
  Proof.
    intros.
  Abort.


  Lemma selective_neighbor_pairs_join {V S : Type} `{H: SelectiveNet V S}:
    forall (v : V) (neighbors1 neighbors2 : list V),
      inductive_cond v neighbors1 ->
      inductive_cond v neighbors2 ->
      inductive_cond v (neighbors1 ++ neighbors2).
  Proof.
    intros v neighbors1 neighbors2 Hneighbors1 Hneighbors2 t states Hstateslen.
    unfold inductive_cond in Hneighbors1, Hneighbors2.
    (* prove that states decomposes into [states1 ++ states2] *)
    apply app_inv_Exists in Hstateslen.
    (* now split apart and solve *)
    destruct Hstateslen as [states1 [states2 [Hstates [Hstateslen1 Hstateslen2]]]].
    rewrite Hstates.
    rewrite map_app.
    symmetry in Hstateslen1, Hstateslen2.
    rewrite (combine_app _ _ _ _ Hstateslen1 Hstateslen2).
    apply (selective_inductive_cond_untimed_join v (A v (1 + t)));
      try (assumption || (rewrite map_length; reflexivity)).
    - apply Hneighbors1; symmetry; assumption.
    - apply Hneighbors2; symmetry; assumption.
  Qed.

  Lemma selective_fail_overlap_fail_if_equal  {V S : Type} `{H: SelectiveNet V S}:
    forall (u v : V) (invu invv : φ S) (neighbors1 neighbors2 : list V)
      (stateu state1 state2 : S) (states1 states2 : list S) (invs1 invs2 : list (φ S)),
      length neighbors1 = length states1 ->
      length neighbors1 = length invs1 ->
      length neighbors2 = length states2 ->
      length neighbors2 = length invs2 ->
      state1 <> state2 ->
      stateu = state1 \/ stateu = state2 ->
      ~ inductive_cond_untimed v invv (combine (u :: neighbors1) (state1 :: states1)) (invu :: invs1) ->
      ~ inductive_cond_untimed v invv (combine (u :: neighbors2) (state2 :: states2)) (invu :: invs2) ->
      ~ inductive_cond_untimed v invv (combine (u :: (neighbors1 ++ neighbors2)) (stateu :: (states1 ++ states2))) (invu :: (invs1 ++ invs2)).
  Proof.
    intros u v invu invv neighbors1 neighbors2 stateu state1 state2 states1 states2 invs1 invs2.
    intros Hlenstate1 Hleninvs1 Hlenstates2 Hleninvs2 Hstateneq Hstateu Hneighbors1 Hneighbors2.
    repeat (apply imply_to_and in Hneighbors1; destruct Hneighbors1 as [? Hneighbors1]).
    repeat (apply imply_to_and in Hneighbors2; destruct Hneighbors2 as [? Hneighbors2]).
    destruct Hstateu; subst; intro contra.
    -
      unfold inductive_cond_untimed in *.
  Abort.

  Lemma selective_neighbor_pairs_join_selective_neighbors_fail {V S : Type} `{H: SelectiveNet V S}:
    forall (v : V) (neighbors1 neighbors2 : list V),
      ~ inductive_cond v neighbors1 ->
      ~ inductive_cond v neighbors2 ->
      ~ inductive_cond v (neighbors1 ++ neighbors2).
  Proof.
    intros v neighbors1 neighbors2 Hneighbors1 Hneighbors2.
    unfold inductive_cond in *.
    intro contra.
    repeat (apply not_all_ex_not in Hneighbors1; destruct Hneighbors1 as [? Hneighbors1]).
    repeat (apply not_all_ex_not in Hneighbors2; destruct Hneighbors2 as [? Hneighbors2]).
    rename x into t1, x4 into t2, x0 into states1, x5 into states2.
    destruct (PeanoNat.Nat.eq_decidable t1 t2).
    - (* The case where [t1 = t2] is easy to show.
         Since both inductive conditions fail at a particular time [x],
         there will be no way of satisfying the condition at that particular time,
         by application of the inductive_cond_untimed lemma.
       *)
      specialize (contra t1 (states1 ++ states2)).
      do 2 rewrite app_length in contra.
      rewrite x6 in contra.
      rewrite x1 in contra.
      specialize (contra eq_refl).
      rewrite map_app in contra.
      rewrite combine_app in contra; try (symmetry; assumption).
      apply (selective_inductive_cond_untimed_join_fail v (A v (1 + t1))
              neighbors1 neighbors2 states1 states2
              (map (fun m => A m t1) neighbors1)
              (map (fun m => A m t1) neighbors2)) in contra;
        try (symmetry; assumption) || assumption || (rewrite map_length; reflexivity).
      + intro contra1.
        apply Hneighbors1.
        apply contra1; assumption.
      + intro contra2.
        rewrite <- H1 in *.
        apply Hneighbors2.
        apply contra2; assumption.
    - (* Unfortunately, we have no such luck when [t1 <> t2].
         In this scenario, it could be the case that while one group fails at [t1],
         the other group passes at [t1] and is preferred,
         and likewise at [t2] the other group passes and is preferred.
         This leaves us with no case where the check always fails at all times. *)
      (* Furthermore, we might need some additional condition to show that
         if the neighbors overlap that we can still conclude something
         about all cases? *)
      (* Suppose that [t1] has a case where the chosen route is from [neighbors1]... *)
      destruct (merge_select (updated_state v (combine neighbors1 states1))
                             (updated_state v (combine neighbors2 states2))) as [Hselect1 | Hselect2].
      + specialize (contra t1 (states1 ++ states2)).
        unfold inductive_cond_untimed in contra.
        rewrite combine_length in contra.
        rewrite map_length in contra.
        repeat rewrite app_length in contra. rewrite x1, x6 in contra.
        rewrite PeanoNat.Nat.min_id in contra.
        specialize (contra eq_refl eq_refl).
        unfold updated_state, transfer_routes in contra.
        rewrite map_app in contra.
        unfold updated_state in Hselect1. rewrite fold_right_merge_init2 in Hselect1.
    Abort.

End SelectiveNet.

Section SelectiveNetExamples.
  Example pass_overrules_fail {V S : Type} `{H: SelectiveNet V S}:
    forall (φ1 φ2 φv : φ S),
      better_inv φ1 φ2 ->
      (forall (s1 : S), φ1(s1) -> φv(s1)) ->
      (exists (s2 : S), φ2(s2) /\ not (φv(s2))) ->
      forall (s1 s2 : S), φ1(s1) -> φ2(s2) -> φv(Merge s1 s2).
  Proof.
    intros.
    (* even though there exists an [s2] such that the invariant fails,
       we know that there exists a better [s1] such that [s1 = Merge s1 s2]. *)
    unfold better_inv in H1.
    destruct H3 as [s2' [? ?]].
    destruct (merge_select s1 s2).
    - rewrite <- H7. apply H2. assumption.
    - unfold better_or_eq in H1.
  Abort.

  Example inconsistent_overlap {V S : Type} `{H: SelectiveNet V S}:
    forall (φ1 φ2 φ3 φv : φ S),
      (exists (s1 s2 : S), φ1(s1) /\ φ2(s2) /\ not (φv(Merge s1 s2))) ->
      (exists (s2' s3 : S), φ2(s2') /\ φ3(s3) /\ not (φv(Merge s2' s3))) ->
      not (exists (s1' s2'' s3' : S), φ1(s1') /\ φ2(s2'') /\ φ3(s3') /\ not (φv(Merge s1' (Merge s2'' s3')))).
  Proof.
    intros.
    intro contra.
    destruct H1 as [s1 [s2 [Hs1 [Hs2 Hs12]]]].
    destruct H2 as [s2' [s3 [Hs2' [Hs3 Hs23]]]].
    destruct contra as [s1' [s2'' [s3' [Hs1' [Hs2'' [Hs3' Hs123]]]]]].
    destruct (merge_select )

  Example inconsistend_tetrad1  {V S : Type} `{H: SelectiveNet V S} :
    forall (φ1 φ2 φ3 φ4 φv : φ S),
      (forall (s1 s2 : S), φ1(s1) -> φ2(s2) -> φv(Merge s1 s2)) ->
      (forall (s3 s4 : S), φ3(s3) -> φ4(s4) -> φv(Merge s3 s4)) ->
      (exists (s1 s3 : S), φ1(s1) /\ φ3(s3) /\ not (φv(Merge s1 s3))) ->
      not (exists (s2 s4 : S), φ2(s2) /\ φ4(s4) /\ not (φv(Merge s2 s4))).
  Proof.
    intros.
    intro contra.
    destruct H3 as [s1 [s3 [Hs1 [Hs3 Hs13]]]].
    destruct contra as [s2 [s4 [Hs2 [Hs4 Hs24]]]].
    destruct (merge_select s2 s4); destruct (merge_select s1 s3);
      rewrite <- H4 in Hs13; rewrite <- H3 in Hs24;
      specialize (H1 s1 s2 Hs1 Hs2);
      specialize (H2 s3 s4 Hs3 Hs4).
    - destruct (merge_select s1 s2).
      + apply Hs13.
        rewrite <- H5 in H1.
        apply H1.
      + apply Hs24.
        rewrite H5.
        apply H1.
    - destruct (merge_select s2 s3).
      + assert (Hs12: s2 = Merge s1 s2).
        { rewrite H5.
          rewrite merge_assoc.
          rewrite (merge_comm s1 s2).
          rewrite <- merge_assoc.
          rewrite <- H4.
          reflexivity.
        }
        rewrite <- Hs12 in H1.
        apply Hs24.
        apply H1.
      + assert (Hs34: s3 = Merge s3 s4).
        {
          rewrite H5.
          rewrite <- merge_assoc.
          rewrite (merge_comm s3 s4).
          rewrite merge_assoc.
          rewrite <- H3.
          reflexivity.
        }
        apply Hs13.
        rewrite Hs34.
        apply H2.
    - destruct (merge_select s1 s4).
      + assert (Hs12: s1 = Merge s1 s2).
        {
          rewrite H5.
          rewrite <- merge_assoc.
          rewrite (merge_comm s4 s2).
          rewrite <- H3.
          reflexivity.
        }
        rewrite <- Hs12 in H1.
        apply Hs13.
        apply H1.
      + assert (Hs34: s4 = Merge s3 s4).
        {
          rewrite H5.
          rewrite merge_assoc.
          rewrite (merge_comm s3 s1).
          rewrite <- H4.
          reflexivity.
        }
        rewrite <- Hs34 in H2.
        apply Hs24.
        apply H2.
    - destruct (merge_select s3 s4).
      + rewrite <- H5 in H2.
        apply Hs13.
        apply H2.
      + apply Hs24.
        rewrite H5.
        apply H2.
  Qed.

  Example inconsistend_tetrad2  {V S : Type} `{H: SelectiveNet V S} :
    forall (φ1 φ2 φ3 φ4 φv : φ S),
      (exists (s1 s2 : S), φ1(s1) /\ φ2(s2) /\ not (φv(Merge s1 s2))) ->
      (exists (s3 s4 : S), φ3(s3) /\ φ4(s4) /\ not (φv(Merge s3 s4))) ->
      (forall (s1 s3 : S), φ1(s1) -> φ3(s3) -> φv(Merge s1 s3)) ->
      not (forall (s2 s4 : S), φ2(s2) -> φ4(s4) -> (φv(Merge s2 s4))).
  Proof.
    intros.
    intro contra.
    destruct H1 as [s1 [s2 [Hs1 [Hs2 Hs12]]]].
    destruct H2 as [s3 [s4 [Hs3 [Hs4 Hs34]]]].
    destruct (merge_select s2 s4); destruct (merge_select s1 s3);
      specialize (H3 s1 s3 Hs1 Hs3);
      specialize (contra s2 s4 Hs2 Hs4);
      rewrite <- H2 in H3;
      rewrite <- H1 in contra.
    - apply Hs12.
      destruct (merge_select s1 s2); rewrite <- H4; assumption.
    - destruct (merge_select s2 s3).
      + assert (H12 : s2 = Merge s1 s2).
        {
          rewrite H4.
          rewrite merge_assoc.
          rewrite (merge_comm s1 s2).
          rewrite <- merge_assoc.
          rewrite <- H2.
          reflexivity.
        }
        apply Hs12.
        rewrite <- H12.
        apply contra.
      + assert (H34 : s3 = Merge s3 s4).
        {
          rewrite H4.
          rewrite <- merge_assoc.
          rewrite (merge_comm s3 s4).
          rewrite merge_assoc.
          rewrite <- H1.
          reflexivity.
        }
        rewrite <- H34 in Hs34.
        apply Hs34.
        apply H3.
    - destruct (merge_select s1 s4).
      + assert (H12 : s1 = Merge s1 s2).
        {
          rewrite H4.
          rewrite <- merge_assoc.
          rewrite (merge_comm s4 s2).
          rewrite <- H1.
          reflexivity.
        }
        rewrite <- H12 in Hs12.
        apply Hs12.
        apply H3.
      + assert (H34 : s4 = Merge s3 s4).
        {
          rewrite H4.
          rewrite merge_assoc.
          rewrite (merge_comm s3 s1).
          rewrite <- H2.
          reflexivity.
        }
        rewrite <- H34 in Hs34.
        apply Hs34.
        apply contra.
    - apply Hs34.
      destruct (merge_select s3 s4); rewrite <- H4; assumption.
  Qed.

End SelectiveNetExamples.
