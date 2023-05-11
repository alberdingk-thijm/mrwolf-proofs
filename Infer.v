(* Modular network inference *)
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Lia.
Require Import Coq.Classes.RelationClasses.
Require Import Classical.

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

Lemma combine_nil2 :
  forall {T1 T2 : Type} (l1 : list T1) (l2 : list T2),
    length l1 = length l2 ->
    combine l1 l2 = nil ->
    l1 = nil /\ l2 = nil.
Proof.
  intros.
  split.
  - destruct l1 as [| ? l1].
    + reflexivity.
    + destruct l2 as [| ? l2].
      * inversion H.
      * inversion H0.
  - destruct l2 as [| ? l2].
    + reflexivity.
    + destruct l1 as [| ? l1].
      * inversion H.
      * inversion H0.
Qed.

Lemma Permutation_split :
  forall {T1 T2 : Type} (l1 l2 : list (T1 * T2)) (l11 l12 : list T1) (l21 l22 : list T2),
    Permutation l1 l2 ->
    split l1 = (l11, l21) ->
    split l2 = (l12, l22) ->
    Permutation l11 l12 /\ Permutation l21 l22.
Proof.
  (* intros T1 T2 l1. *)
  (* induction l1; intros. *)
  (* - simpl in H0. inversion H0. subst. *)
  (*   apply Permutation_nil in H. *)
  (*   subst. *)
  (*   inversion H1. *)
  (*   split; constructor. *)
  (* - destruct l2. *)
  (*   + apply Permutation_sym in H. apply Permutation_nil_cons in H. contradiction. *)
  (*   +  *)
  intros.
  generalize dependent l11.
  generalize dependent l12.
  generalize dependent l21.
  generalize dependent l22.
  induction H; intros.
  - inversion H0.
    inversion H1.
    split; constructor.
  - assert (Hlen := H).
    apply Permutation_length in Hlen.
    assert (H0' := H0).
    assert (H1' := H1).
    apply split_combine in H0.
    apply split_combine in H1.
    destruct l11; destruct l21; destruct l12; destruct l22; try inversion H0; inversion H1.
    assert (Hlen12 : length (x :: l') = Datatypes.S (length l12)).
    { rewrite <- split_length_l. rewrite H1'. simpl. reflexivity. }
    assert (Hlen11 : length (x :: l) = Datatypes.S (length l11)).
    { rewrite <- split_length_l. rewrite H0'. simpl. reflexivity. }
    assert (Hlen22 : length (x :: l') = Datatypes.S (length l22)).
    { rewrite <- split_length_r. rewrite H1'. simpl. reflexivity. }
    assert (Hlen21 : length (x :: l) = Datatypes.S (length l21)).
    { rewrite <- split_length_r. rewrite H0'. simpl. reflexivity. }
    simpl in Hlen11, Hlen12, Hlen21, Hlen22.
    injection Hlen12 as Hlen12.
    injection Hlen11 as Hlen11.
    injection Hlen22 as Hlen22.
    injection Hlen21 as Hlen21.
    subst.
    inversion H5.
    subst.
    specialize (IHPermutation l22 l21 l12).
    rewrite combine_split in IHPermutation; try congruence.
    specialize (IHPermutation eq_refl l11).
    rewrite combine_split in IHPermutation; try congruence.
    specialize (IHPermutation eq_refl).
    destruct IHPermutation.
    split; constructor; assumption.
  -
    assert (H0' := H0).
    assert (H1' := H1).
    apply split_combine in H0.
    apply split_combine in H1.
    do 2 (destruct l11; destruct l21; destruct l12; destruct l22; try inversion H0; inversion H1).
    subst.
    inversion H7.
    inversion H9.
    inversion H10.
    subst.
    (* need to show that [l12 = l11] and [l22 = l21] by [H11]. *)
    assert (Hl1: l12 = l11).
    { admit. }
    assert (Hl2: l22 = l21).
    { admit. }
    subst.
    split; constructor.
  - admit.
Admitted.


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

  Definition transfer_routes {V S : Type} `{H: Net V S} (node : V) (neighbors : list (V * S)) :=
    (map (fun (neighbor : (V * S)) => F (fst neighbor) node (snd neighbor)) neighbors).

  Definition updated_state {V S : Type} `{H: Net V S} (node : V) (neighbors : list (V * S)) : S :=
    fold_right Merge (I node) (transfer_routes node neighbors).

  Lemma state_updates_comm {V S : Type} `{H: Net V S} :
    forall (v : V) (neighbors1 : list (V * S)) (neighbors2 : list (V * S)),
      Permutation neighbors1 neighbors2 ->
      updated_state v neighbors1 = updated_state v neighbors2.
  Proof.
    intros.
    induction H0.
    - constructor.
    - unfold updated_state in *. simpl. rewrite IHPermutation. reflexivity.
    - unfold updated_state in *. simpl. rewrite merge_assoc. rewrite merge_assoc.
      replace (Merge (F (fst y) v (snd y)) (F (fst x) v (snd x)))
                with (Merge (F (fst x) v (snd x)) (F (fst y) v (snd y))).
      2: apply merge_comm.
      reflexivity.
    - congruence.
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
    split; intro; intros t states Hstateslen.
    -
      assert (Hstates: exists (states' : list S), Permutation (combine neighbors1 states') (combine neighbors2 states)).
      { eexists. admit. }
      destruct Hstates as [states' Hstates].
      eapply inductive_cond_untimed_comm.
      apply Permutation_sym.
      eassumption.
      3: apply H1.
      apply Permutation_map; apply Permutation_sym; assumption.
      eapply Permutation_split in Hstates.
      2: apply combine_split.
      3: apply combine_split.
      destruct Hstates.
      (* We need to prove that, if the inductive condition holds for neighbors [x :: l],
         then it will hold for neighbors [x :: l'] when l' is a permutation of l.
         The inductive hypothesis isn't useful here, since we can't use l or l' to understand
         the result for [x :: l] and [x :: l'].
         Instead, we need to be able to claim that we have two state permutations such that
         [Permutation (combine l states) (combine l' states')], so that the invariants all align. *)
        (* assert (Hstates: exists (l' : list V) (states' : list S), Permutation (combine l states) (combine l' states')). *)
        (* { exists l. exists states. apply Permutation_refl. } *)
        (* destruct Hstates as [l'' [states' Hnbrs]]. *)
        (* apply (Permutation_combine _ _) in Hnbrs. *)
        (* destruct Hnbrs as [Hl'' Hstates]. *)
        (* specialize (H1 t (s :: states')). *)
        (* assert (H0' := H0). *)
        (* apply Permutation_length in H0'. *)
        (* assert (Hstates' := Hstates). *)
        (* apply Permutation_length in Hstates'. *)
        (* simpl in H1. *)
        (* rewrite combine_length in H1. *)
        (* rewrite map_length in H1. *)
        (* rewrite <- Hstates' in H1. *)
        (* rewrite H0' in H1. *)
        (* rewrite H5 in H1. *)
        (* rewrite PeanoNat.Nat.min_id in H1. *)
        (* specialize (H1 eq_refl eq_refl). *)
        (* rewrite (state_updates_comm _ _ ((x, s) :: (combine l states'))). *)
        (* apply H1. *)
        (* constructor. *)
        (* assumption. *)
        (* admit. *)
        (* constructor. *)
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

  (* Instance NatNet : SelectiveNet nat nat := *)
  (*   { *)
  (*     Merge := PeanoNat.Nat.min; *)
  (*     F := fun u v s => 1 + s; *)
  (*     I := fun v => if (v =? 0) then 0 else 16; *)
  (*     merge_assoc := PeanoNat.Nat.min_assoc; *)
  (*     merge_comm := PeanoNat.Nat.min_comm; *)
  (*     A := fun v => if (v =? 0) then (fun t s => s = 0) else *)
  (*                  (fun t s => if (t <? 1) then True else s = 1); *)
  (*     merge_order := PeanoNat.Nat.min_l; *)
  (*   }. *)

  Lemma merge_idempotent {V S : Type} `{H: SelectiveNet V S} :
    forall s, s = Merge s s.
  Proof.
    intros.
    apply merge_order.
    apply preo.
  Qed.

  Definition better_or_eq {V S : Type} `{H: SelectiveNet V S} (s1 s2 : S) :=
    R s1 s2.

  Definition better {V S : Type} `{H: SelectiveNet V S} (s1 s2 : S) :=
    R s1 s2 /\ s1 <> s2.

  Infix "⪯" := better_or_eq (at level 20).
  Infix "≺" := better (at level 20).

  Definition better_inv {V S : Type} `{H: SelectiveNet V S} (φ1 φ2 : φ S) :=
    forall s1 s2, φ1(s1) -> φ2(s2) -> s1 ⪯ s2.

  Example better_inv1 {V S : Type} `{H: SelectiveNet V S}:
    forall s1 s2, s1 ⪯ s2 -> better_inv (fun s => s = s1) (fun s => s = s2).
  Proof.
    intros s1 s2 Hle.
    unfold better_inv.
    intros s0 s3 Hle1 Hle2.
    congruence.
  Qed.

  Lemma fold_right_merge {V S : Type} `{H: SelectiveNet V S}:
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
    apply fold_right_merge.
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

  Lemma selective_neighbor_pairs_cover_selective_neighbors {V S : Type} `{H: SelectiveNet V S}:
    forall v u neighbors,
      inductive_cond v neighbors ->
      inductive_cond v (u :: nil)  ->
      inductive_cond v (u :: neighbors).
  Proof.
    intros v u neighbors.
    induction neighbors as [| z neighbors]; intros Hneighbors Hu t states Hstateslen.
    - do 2 try (destruct states as [| ? states]); try solve[inversion Hstateslen].
      simpl.
      unfold inductive_cond_untimed.
      simpl.
      intros.
      inversion H2.
      subst.
      simpl in H6.
      specialize (Hu t (s :: nil) eq_refl eq_refl).
      clear H1 H8.
      apply Hu.
      apply H2.
  - do 2 try (destruct states as [| ? states]); try solve[inversion Hstateslen].
    inversion Hstateslen.
    unfold inductive_cond_untimed.
    intros.
    inversion H3.
    inversion H9.
    subst.
    simpl in H7, H13.
    unfold inductive_cond in Hneighbors, Hu.
    specialize (Hneighbors t (s0 :: states)).
    specialize (Hu t (s :: nil)).
    (* assert (Hlenplus2: forall {T1 T2 : Type} (a b : T1) (c d : T2) (l1 : list T1) (l2 : list T2), length l1 = length l2 -> length (a :: b :: l1) = length (c :: d :: l2)). *)
    (* { intros. simpl. rewrite H4. reflexivity. } *)
    simpl in Hstateslen.
    unfold inductive_cond_untimed in Hneighbors, Hu.
    simpl in Hu, Hneighbors.
    specialize (Hu eq_refl eq_refl).
    rewrite map_length in Hneighbors.
    rewrite combine_length in Hneighbors.
    rewrite H2 in Hneighbors.
    rewrite PeanoNat.Nat.min_id in Hneighbors.
    specialize (Hneighbors eq_refl eq_refl H9).
    (* rewrite (state_updates_comm v ((u, s) :: (z, s0) :: combine neighbors states) ((z, s0) :: (u, s) :: combine neighbors states)). *)
    (* 2: constructor. *)
    (* unfold inductive_cond, inductive_cond_untimed in IHneighbors. *)
    unfold updated_state in *.
    simpl.
    simpl in Hneighbors, Hu.
    remember (merge_select (F u v s) (Merge (F z v s0)
                    (fold_right Merge (I v)
                       (transfer_routes v (combine neighbors states))))) as Hz.
    destruct Hsel as [Hselu Hsel].
    + rewrite <- e.
      replace (Merge (F u v s) (fold_right Merge (I v) (transfer_routes v (combine neighbors states))))
                with (updated_state v (combine (u :: neighbors) (s :: states))).
      2: reflexivity.
      remember (merge_select (F u v s) (updated_state v (combine neighbors states))) as Hus.
      destruct Hus.
      * unfold updated_state.
        simpl.
        unfold updated_state in e0.
        rewrite <- e0.
        admit.
      * unfold updated_state. simpl. unfold updated_state in e0.
        rewrite <- e0.
      (* apply IHneighbors; try congruence. *)
      (* applying IHneighbors gets us into trouble, as our hypotheses refer to [t] but we have a goal with [t0] *)
      (* intros. *)
      (* simpl in IHneighbors. *)
      (* unfold updated_state in IHneighbors. *)
      admit.
    + rewrite merge_assoc. rewrite <- e.
      apply Hneighbors.
  Abort.

End SelectiveNet.
