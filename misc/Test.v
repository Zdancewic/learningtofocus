Lemma test: forall P, ~~( P \/ ~P).
Proof.
  intros P.
  unfold not.
  intros.
  apply H. 
  right.
  intros.
  apply H.
  left. apply H0.
Qed.


Print test.