(* Modular network inference *)
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.

Definition iterated_and (args : list Prop) : Prop :=
  fold_right and True args.

Section timepiece.
  Variable S : Type.

  Definition Node := nat.
  Definition Edge : Type := (Node * Node).

  Variable Merge : S -> S -> S.
  Variable F : Edge -> S -> S.

  Definition A := nat -> S -> Prop.

  (* Computing a new route at a node given routes of its neighbors. *)
  Definition updated_state (node : Node) (initial : S) (neighbors : list (Node * S)) : S :=
    fold_right (fun (neighbor : (Node * S)) (st : S) =>
                  let (m, ms) := neighbor in
                  Merge st (F (m, node) ms)) initial neighbors.

  (* The until temporal operator. *)
  Definition until (tau : nat) (before after : S -> Prop) : A :=
    fun t s => if t <? tau then before s else after s.

  Record Until := mkUntil
    {
      tau : nat
    ; before : S -> Prop
    ; after : S -> Prop
    }.

  Definition construct_until (u : Until) : A :=
    until (tau u) (before u) (after u).

  Compute (snd (fst (1, 2, 3))). (* --> 2 *)

  (* A helper definition for writing out the inductive condition given a particular set of states
   and a particular time [t]. *)
  Definition inductive_condition_aux
    (node : Node) (initial : S) (node_invariant : A)
    (neighbor_constraints : list (Node * A * S)) (t : nat) :=
    (* if all the constraints hold on the neighbors at time t... *)
    (Forall (fun (c : Node * A * S) =>
                          ((snd (fst c)) t (snd c))) neighbor_constraints) ->
    (* then the constraint holds on the updated state at the node at time t + 1 *)
      (node_invariant (1 + t)
         (updated_state node initial (map (fun c => (fst (fst c), (snd c))) neighbor_constraints))).

  (* The original inductive condition for a node [n]. *)
  Definition inductive_condition (n : Node) (initial : S) (node_invariant : A)
                                 (neighbor_invariants : list (Node * A)) :=
    forall (t : nat) (states : list S),
      length states = length neighbor_invariants ->
      inductive_condition_aux n initial node_invariant (combine neighbor_invariants states) t.

  Definition boolean_equals_time_bound (b : bool) (t tau : nat) :=
    b = (t <? tau).

  Definition boolean_inductive_condition
    (n : Node) (initial : S) (before after : S -> Prop) (b : bool)
    (neighbors : list (Node * Until)) :=
    forall (B : list bool),
      length B = length neighbors ->
      (exists (t : nat), Forall (fun bt => let (b, tau) := bt in boolean_equals_time_bound b t tau)
                    (combine B (map (fun nbr => tau (snd nbr)) neighbors))) ->
                  forall (states : list S),
                    length states = length neighbors ->
                    (* FIXME: need to add the reference to the nbr *)
                    (Forall (fun bs => let (b, state) := bs in
                                    if b then (before nbr) else (after nbr)) (combine (B states) neighbors)).

  Definition until_combine (T : list nat) (befores afters : list (S -> Prop)) : list A :=
    map (fun args =>
      match args with
      | (tau, before, after) => until tau before after
      end)
        (combine (combine T befores) afters).

  Lemma ind_vc_until_implies_boolean_ind_vc :
    forall n initial tau before after neighbors neighbor_invariants B,
      length neighbors = length B ->
      (* node_invariant = until node_tau nbefore nafter -> *)
      inductive_condition n initial (until tau before after)
        (combine neighbors (map construct_until neighbor_invariants))
      ->

  (* *)
  Definition time_bounds B T :=
    (* Associate each b in B with a t in T. *)
    Admitted.
End timepiece.
