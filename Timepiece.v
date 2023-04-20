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
  Definition A := nat -> φ.

  Definition true_inv : A := fun t s => True.

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

  Definition initial_condition (node : Node) (invariant : A) := invariant 0 (I node).

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
  Definition inductive_condition (n : Node) (node_invariant : A)
                                 (neighbors : list Node) (neighbor_invariants : list A) :=
    forall (t : nat) (states : list S),
      length states = length neighbors ->
      inductive_condition_untimed
        n (node_invariant (1 + t))
        (combine neighbors states) (map (fun a => (a t)) neighbor_invariants).

  Definition inductive_invariant
    (n : Node) (node_invariant : A) (neighbors : list Node) (neighbor_invariants : list A) :=
    initial_condition n node_invariant /\ inductive_condition n node_invariant neighbors neighbor_invariants.

  Lemma inductive_condition_is_sound :
    forall (g : Graph) (invariants : list A),
      length g = length invariants ->
      forall (v : Node),
        v < length g ->
        inductive_invariant
          v (nth v invariants true_inv) (nth v g nil)
          (map (fun nbr => (nth nbr invariants true_inv)) (nth v g nil)) ->
        forall (t : nat), (nth v invariants true_inv) t (σ g v t).
  Proof.
    intros g invariants Hglen v Hving Hindinv t.
    generalize dependent v.
    induction t; intros v Hving [Hinitial Hinductive].
    - assumption. (* by Hinitial *)
    - simpl.
      remember (nth v invariants true_inv) as a.
      (* now need to connect the state with the invariant *)
      admit.
  Admitted.

End timepiece.
