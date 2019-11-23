


(* SIMPL
https://pjreddie.com/coq-tactics/#simpl

simpl
When we have a complex term we can use simpl to crunch it down.

In this example we prove that adding zero to any number returns the same number. We use simpl to "run" the add function in the goal. Since in the example the first argument to add is O, it simplifies the function application to just the result

*)
Inductive nat : Set :=
  | O
  | S : nat -> nat.

Fixpoint add (a: nat) (b: nat) : nat :=
  match a with
    | O => b
    | S x => S (add x b)
  end.

Lemma zero_plus_n_equals_n:
  forall n, (add O n) = n.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.