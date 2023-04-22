(* Modular network verification *)
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Lia.

Section timepiece.
  Variable S : Type.
  Definition Node := nat.
  Definition Edge : Type := (Node * Node).
  Definition Graph : Type := list (list Node).

  Variable I : Node -> S.
  Variable Merge : S -> S -> S.
  Variable F : Edge -> S -> S.

  Definition φ := S -> Prop.
  Definition Q := nat -> φ.

  Definition true_inv : Q := fun t s => True.

  Variable A : Node -> Q.

  (* Computing a new route at a node given routes of its neighbors. *)
  Definition updated_state (node : Node)
    (neighbors : list (Node * S)) : S :=
    fold_right (fun (neighbor : (Node * S)) (st : S) =>
                  let (m, ms) := neighbor in
                  Merge st (F (m, node) ms)) (I node) neighbors.

  Fixpoint σ (g : Graph) (node : Node) (t : nat) : S :=
    match t with
      | O => I node
      | Datatypes.S t' => updated_state node (map (fun m => (m, σ g m t')) (nth node g nil))
    end.

  Definition initial_condition (node : Node) := A node 0 (I node).

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
  Definition inductive_condition
    (n : Node) (neighbors : list Node) :=
    forall (t : nat) (states : list S),
      length states = length neighbors ->
      inductive_condition_untimed
        n (A n (1 + t))
        (combine neighbors states) (map (fun m => (A m t)) neighbors).

  Definition inductive_invariant
    (n : Node) (neighbors : list Node) :=
    initial_condition n /\ inductive_condition n neighbors.

  Lemma inductive_condition_is_sound :
    forall (g : Graph) (v : Node),
        v < length g ->
        Forall (fun u => u < length g) (nth v g nil) ->
        inductive_invariant v (nth v g nil) ->
        forall (t : nat), A v t (σ g v t).
  Proof.
    intros g v Hving Huing Hindinv t.
    generalize dependent v.
    induction t; intros v Hving Huing [Hinitial Hinductive].
    - assumption. (* by Hinitial *)
    - simpl.
      induction (nth v g nil).
      + simpl. unfold inductive_condition in Hinductive.
        simpl in Hinductive. unfold inductive_condition_untimed in Hinductive.
        apply (Hinductive t nil); auto.
        apply Forall_nil.
      + simpl in *. unfold inductive_condition in Hinductive.
        unfold inductive_condition_untimed in Hinductive.
        simpl in Hinductive.
        admit.
      (* now need to connect the state with the invariant *)
  Admitted.

End timepiece.
