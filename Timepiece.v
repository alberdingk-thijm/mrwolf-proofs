(* Modular network verification *)
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

Lemma self_combine :
  forall { A B C : Type } (l : list A) (f1 : A -> B) (f2 : A -> C),
    map (fun (x : A * A) => (f1 (fst x), f2 (snd x))) (combine l l)
        = map (fun (x : A) => (f1 x, f2 x)) l.
Proof.
  induction l.
  - auto.
  - intros f1 f2.
    simpl.
    rewrite (IHl f1 f2).
    auto.
Qed.

Section NetRec.
  Let φ (S : Type) := S -> Prop.
  Let Q (S : Type) := nat -> (φ S).

  Record Net (VType : Type) (SType : Type) := mkNet {
      V : VType
    ; S : SType
    ; Merge : SType -> SType -> SType
    ; F : VType * VType -> SType -> SType
    ; I : VType -> SType
    ; merge_associates : forall s1 s2 s3, Merge (Merge s1 s2) s3 = Merge s1 (Merge s2 s3)
    ; merge_commutes : forall s1 s2, Merge s1 s2 = Merge s2 s1
    ; A : VType -> Q SType
    ; (* Computing a new route at a node given routes of its neighbors. *)
      update_state (node : VType) (neighbors : list (VType * SType)) : SType :=
      fold_right (fun (neighbor : (VType * SType)) (st : SType) =>
                    let (m, ms) := neighbor in
                    Merge st (F (m, node) ms)) (I node) neighbors
  }.
End NetRec.

Section timepiece.
  Variable S : Type.
  Definition Node := nat.
  Definition Edge : Type := (Node * Node).
  Definition Graph : Type := (list Node * list Edge).

  Variable I : Node -> S.
  Variable Merge : S -> S -> S.
  Variable F : Edge -> S -> S.

  Definition φ := S -> Prop.
  Definition Q := nat -> φ.

  Definition true_inv : Q := fun t s => True.

  Variable A : Node -> Q.

  (** Return all nodes that have an outgoing edge to the given node. *)
  Definition predecessors (g : Graph) (node : Node) : list Node :=
    map (fun e => fst e) (filter (fun e => snd e =? node) (snd g)).

  Lemma in_predecessors :
    forall (g : Graph) (u v : Node),
      In u (fst g) /\ In (u, v) (snd g) -> In u (predecessors g v).
  Proof.
    intros g u v [Hunode Huvedge].
    unfold predecessors.
    replace u with (fst (u, v)) by reflexivity.
    apply (in_map fst (filter (fun e : Node * nat => snd e =? v) (snd g))).
    apply filter_In.
    split.
    + apply Huvedge.
    + apply PeanoNat.Nat.eqb_refl.
  Qed.

  (* all edges in a graph belong to real nodes *)
  Definition well_formed_graph (g : Graph) :=
    forall (n m : Node), In (n, m) (snd g) -> In n (fst g) /\ In m (fst g).

  (* Computing a new route at a node given routes of its neighbors. *)
  Definition updated_state (node : Node)
    (neighbors : list (Node * S)) : S :=
    fold_right (fun (neighbor : (Node * S)) (st : S) =>
                  let (m, ms) := neighbor in
                  Merge st (F (m, node) ms)) (I node) neighbors.

  Fixpoint σ (g : Graph) (node : Node) (t : nat) : S :=
    match t with
      | O => I node
      | Datatypes.S t' => updated_state node (map (fun m => (m, σ g m t')) (predecessors g node))
    end.

  Definition initial_condition (node : Node) := A node 0 (I node).

  (* A helper definition for writing out the inductive condition with times
     erased: all invariants are specified as [S -> Prop] functions. *)
  Definition inductive_condition_untimed
    (node : Node) (node_invariant : φ)
    (neighbors : list (Node * S)) (neighbor_invariants : list φ) :=
    length neighbors = length neighbor_invariants ->
    (* if every neighbor's route satisfies the invariant φ *)
    (Forall2 (fun m p => p (snd m)) neighbors neighbor_invariants) ->
    (* then the node's invariant holds on the updated state *)
    (node_invariant (updated_state node neighbors)).

  (* The original inductive condition for a node [n]. *)
  Definition inductive_condition (n : Node) (g : Graph) :=
    forall (t : nat) (states : list S),
      length states = length (predecessors g n) ->
      inductive_condition_untimed
        n (A n (1 + t))
        (combine (predecessors g n) states) (map (fun m => A m t) (predecessors g n)).

  Definition inductive_invariant
    (n : Node) (g : Graph) :=
    initial_condition n /\ inductive_condition n g.

  Lemma inductive_condition_is_sound :
    forall (g : Graph) (v : Node),
      well_formed_graph g ->
      In v (fst g) ->
      inductive_invariant v g ->
      forall (t : nat), A v t (σ g v t).
  Proof.
    intros g v Hg Hving Hindinv t.
    generalize dependent v.
    induction t; intros v Hving [Hinitial Hinductive].
    - assumption. (* by Hinitial *)
    - simpl in *.
      unfold inductive_condition, inductive_condition_untimed in Hinductive.
      assert (H: length (predecessors g v) = length (predecessors g v)) by reflexivity.
      specialize (Hinductive t (map (fun m => σ g m t) (predecessors g v))).
      rewrite combine_length in Hinductive.
      rewrite map_length in Hinductive.
      rewrite map_length in Hinductive.
      rewrite PeanoNat.Nat.min_id in Hinductive.
      specialize (Hinductive H H).
      replace (combine (predecessors g v)
                       (map (fun m : Node => σ g m t) (predecessors g v)))
                with (map (fun m : Node => (id m, σ g m t)) (predecessors g v)) in Hinductive.
      apply Hinductive; auto.
      2: {
        rewrite <- (map_id (predecessors g v)).
        rewrite map_map.
        rewrite map_map.
        rewrite <- map_combine.
        rewrite <- self_combine.
        reflexivity.
      }
      Abort.
End timepiece.
