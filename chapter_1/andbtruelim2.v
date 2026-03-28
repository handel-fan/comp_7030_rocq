(* Tools are: intros, destruct, hypothesis*)
Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct b eqn:Eb.
  - simpl in H.
    rewrite H.
    reflexivity.
  - simpl in H.
    destruct c eqn:Ec.
      + reflexivity.
      + rewrite H.
        reflexivity.
Qed.


