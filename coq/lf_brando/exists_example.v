Variable T : Type.
Variable R : T -> T -> Prop.

Theorem test1 :
  forall x y,
    R x y -> exists t, R x t.
Proof.
  intros.
    (*
  | Context:
      x, y : T,
      H : R x y
  | Goal: 
      exists t : T, R x t
  *)
  eexists.
  (*
  | Context:
      x, y : T,
      H : R x y
  | Goal: 
      R x ?t 
    (Coq introuced ?T as a placeholder for some t that will be have to be decuded later in the proof)
  *)
  apply H.
Qed.

Theorem test2 :
  forall x y,
    R x y -> exists t, R x t.
Proof.
  intros. exists y. apply H.
Qed.