Example test_oddb1: Nat.odd 1 = true.
Proof.
  simpl. reflexivity.
Qed.

Example test_oddb2: Nat.odd 1 = true.
  simpl. reflexivity.
Qed.

(*
Example test_oddb3: Nat.odd 1 = true.
Qed.
 *)

Theorem plus_O_n :
  forall n : nat,
    0 + n = n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.