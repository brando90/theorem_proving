(* Chapter 3 Introducing Inductive Types *)

(* 3.1 Proof Terms *)

Check (fun x : nat => x).
(* fun x : nat => x
     : nat -> nat *)

Definition f ( x: nat ) : nat :=
  x.

Check f.
(* f : nat -> nat *)
Compute f(1).
(* = 1: nat *)

(* TODO compare reflexivity vs simpl. *)
Lemma f1_is_1: f(1) = 1.
Proof. 
  simpl. (* why doesn't this change it to f(1)->1, goal doesn't change, how does simpl. work? *)
  reflexivity. 
Qed.

Check (fun x : True => x).
(* fun x : True => x
     : True -> True *)

Check I.


(* 3.2 Enumerations *)

Inductive unit : Set :=
  | tt.

Check unit.
(* unit
     : Set *)

Check tt.
(* tt
     : unit *)
Check unit_ind.
(* unit_ind
     : forall P : unit -> Prop, P tt -> forall u : unit, P u *)