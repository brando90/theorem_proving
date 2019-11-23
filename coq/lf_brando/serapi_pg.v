(* File were I test commands I'm throwing to SerAPI *)


(* Theorems from my basics file *)

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity.
Qed.

Lemma addn0 n : n + 0 = n.
Proof.
  simpl. induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. rewrite -> IH. reflexivity.
Qed.

(* SerAPI stuff *)

(* (Add () "Lemma addn0 n : n + 0 = n. Proof. now induction n. Qed.") *)

Lemma addn0 n : n + 0 = n.
Proof.
  now induction n.
Qed.