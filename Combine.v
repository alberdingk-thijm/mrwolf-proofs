(** Some useful lemmas of [combine] and [split], which we use extensively. *)
Require Import Coq.Sorting.Permutation.
Require Import Coq.Lists.List.

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

Lemma combine_app :
  forall {T1 T2 : Type} (l1 l2 : list T1) (l3 l4 : list T2),
    length l1 = length l3 ->
    length l2 = length l4 ->
    combine (l1 ++ l2) (l3 ++ l4) = combine l1 l3 ++ combine l2 l4.
Proof.
  induction l1; intros.
  - simpl.
    symmetry in H.
    rewrite length_zero_iff_nil in H.
    subst.
    reflexivity.
  - destruct l3 as [| ? l3]; inversion H.
    specialize (IHl1 l2 l3 l4 H2 H0).
    simpl.
    rewrite IHl1.
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

Lemma combine_ext :
  forall {T1 T2 : Type} (l1 l2 : list T1) (l3 l4 : list T2),
    length l1 = length l3 ->
    length l2 = length l4 ->
    combine l1 l3 = combine l2 l4 ->
    l1 = l2 /\ l3 = l4.
Proof.
  induction l1; intros.
  - simpl.
    symmetry in H.
    rewrite length_zero_iff_nil in H.
    subst.
    simpl in H1.
    symmetry in H1.
    apply (combine_nil2 l2 l4 H0) in H1.
    destruct H1.
    split; congruence.
  - destruct l3 as [| ? l3]; try solve[inversion H].
    destruct l2 as [| ? l2]; try solve[inversion H1].
    destruct l4 as [| ? l4]; try solve[inversion H1].
    injection H as H.
    injection H0 as H0.
    simpl in H1.
    inversion H1.
    subst.
    specialize (IHl1 l2 l3 l4 H H0 H5).
    destruct IHl1.
    subst.
    split; reflexivity.
Qed.

Lemma Permutation_split :
  forall {T1 T2 : Type} (l1 l2 : list (T1 * T2)) (l11 l12 : list T1) (l21 l22 : list T2),
    Permutation l1 l2 ->
    split l1 = (l11, l21) ->
    split l2 = (l12, l22) ->
    Permutation l11 l12 /\ Permutation l21 l22.
Proof.
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
    assert (Hlen11 : length (y :: x :: l) = 2 + (length l11)).
    { rewrite <- split_length_l. rewrite H0'. simpl. reflexivity. }
    assert (Hlen12 : length (x :: y :: l) = 2 + (length l12)).
    { rewrite <- split_length_l. rewrite H1'. simpl. reflexivity. }
    assert (Hlen21 : length (y :: x :: l) = 2 + (length l21)).
    { rewrite <- split_length_r. rewrite H0'. simpl. reflexivity. }
    assert (Hlen22 : length (x :: y :: l) = 2 + (length l22)).
    { rewrite <- split_length_r. rewrite H1'. simpl. reflexivity. }
    simpl in Hlen11, Hlen12, Hlen21, Hlen22.
    injection Hlen12 as Hlen12.
    injection Hlen11 as Hlen11.
    injection Hlen22 as Hlen22.
    injection Hlen21 as Hlen21.
    assert (Hlen1: length l11 = length l21) by congruence.
    assert (Hlen2: length l12 = length l22) by congruence.
    subst.
    inversion H7.
    inversion H9.
    inversion H10.
    subst.
    apply (combine_ext l12 l11 l22 l21 Hlen2 Hlen1) in H11.
    destruct H11.
    subst.
    split; constructor.
  -
    assert (H1' := H1).
    assert (H2' := H2).
    apply split_combine in H1.
    apply split_combine in H2.
    assert (Hlen11 : length l = length l11).
    { rewrite <- split_length_l. rewrite H2'. simpl. reflexivity. }
    assert (Hlen12 : length l'' = length l12).
    { rewrite <- split_length_l. rewrite H1'. simpl. reflexivity. }
    assert (Hlen21 : length l = length l21).
    { rewrite <- split_length_r. rewrite H2'. simpl. reflexivity. }
    assert (Hlen22 : length l'' = length l22).
    { rewrite <- split_length_r. rewrite H1'. simpl. reflexivity. }
    assert (Hlen1: length l11 = length l21) by congruence.
    assert (Hlen2: length l12 = length l22) by congruence.
    apply IHPermutation1; try assumption.
    rewrite <- H1'.
    subst.
    clear Hlen11 Hlen12 Hlen21 Hlen22 H1' H2'.
    admit.
Admitted.

Lemma Permutation_combine_Exists :
  forall {T1 T2 : Type} (l1 l2 : list T1) (l3 : list T2),
    Permutation l1 l2 ->
    exists (l4 : list T2),
      Permutation l3 l4 ->
      Permutation (combine l1 l3) (combine l2 l4).
Proof.
  intros.
  induction H.
  - exists nil.
    intros.
    apply Permutation_sym in H.
    apply Permutation_nil in H.
    subst.
    constructor.
  - destruct IHPermutation as [l4 IHP].
    exists l4.
    intros.
    destruct l3; destruct l4;
      try ((apply Permutation_nil in H0 || (apply Permutation_sym in H0; apply Permutation_nil in H0)); subst; constructor).
    + apply Permutation_nil_cons in H0. inversion H0.
    + apply Permutation_sym in H0. apply Permutation_nil_cons in H0. inversion H0.
    + specialize (IHP H0).
      simpl.
      admit.
  - do 2 (try destruct l3 as [| ? l3]).
    + exists nil. intros. constructor.
    + exists nil. intros. apply Permutation_sym, Permutation_nil_cons in H. inversion H.
    + exists (t0 :: t :: l3).
      intros.
      simpl.
      constructor.
  - destruct IHPermutation1 as [l4' IHP1].
    destruct IHPermutation2 as [l4'' IHP2].
    admit.
Admitted.
