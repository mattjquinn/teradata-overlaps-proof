Require Import Omega.

Local Open Scope nat_scope.

Inductive period : Type :=
| Period (a b : nat).

Definition pstart (p : period) : nat :=
  match p with | Period a b => a end.

Definition pend (p : period) : nat :=
  match p with | Period a b => b end.

Inductive periodR : period -> Prop :=
| PeriodR : forall p,
    (* By definition, a period's end tstamp is strictly greater than its start. *)
    pstart p < pend p ->
    periodR p.

Inductive overlapsTeradataR : period -> period -> Prop :=
| TeradataSGt : forall p1 p2,
    periodR p1 ->
    periodR p2 ->
    (pstart p1) > (pstart p2) ->
    ~ (pstart p1 >= pend p2 /\ pend p1 >= pend p2) ->
    (overlapsTeradataR p1 p2)
| TeradataSLt : forall p1 p2,
    periodR p1 ->
    periodR p2 ->
    (pstart p2) > (pstart p1) ->
    ~ (pstart p2 >= pend p1 /\ pend p2 >= pend p1) ->
    (overlapsTeradataR p1 p2)
| TeradataSEq : forall p1 p2,
    periodR p1 ->
    periodR p2 ->
    pstart p1 = pstart p2 ->
    (pend p1 = pend p2 \/ pend p1 <> pend p2) ->
    (overlapsTeradataR p1 p2).

Inductive overlapsBigQueryR : period -> period -> Prop :=
| BigQuery : forall p1 p2,
    periodR p1 ->
    periodR p2 ->
    max (pstart p1) (pstart p2) < min (pend p1) (pend p2) ->
    (overlapsBigQueryR p1 p2).

Theorem overlaps_Teradata_BigQuery_equiv : forall p1 p2 : period,
    overlapsTeradataR p1 p2 <-> overlapsBigQueryR p1 p2.
Proof.  
  split.
  - intros.
    induction H.
    * inversion H. inversion H0. subst.
      apply BigQuery.
      assumption. assumption.
      rewrite max_l.
      apply Decidable.not_and in H2.
      destruct H2 as [HQ1 | HQ2].
      apply not_le in HQ1.
      (* Want to be able to say min will give us e1 or e2, without
         claiming WHICH one b/c we don't know enough to prove either way. *)
      apply Nat.min_glb_lt. assumption. assumption.
      rewrite min_l.
      apply not_ge in HQ2.
      assumption. rewrite Nat.lt_eq_cases.
      apply not_ge in HQ2.
      left. assumption.
      apply Nat.le_decidable.  
      apply Decidable.not_and in H2.
      destruct H2 as [HQ1 | HQ2].
      apply not_ge in HQ1. 
      rewrite Nat.lt_eq_cases.
      left. assumption.
      apply not_ge in HQ2.
      rewrite Nat.lt_eq_cases.
      left. assumption.
      apply dec_ge.
    * inversion H. inversion H0. subst.
      apply BigQuery.
      assumption. assumption.
      rewrite max_r.
      apply Decidable.not_and in H2.
      destruct H2 as [HQ1 | HQ2].
      apply not_ge in HQ1.
      (* Same as above; we don't know which of the two is actually min.*)
      apply Nat.min_glb_lt. assumption. assumption.
      rewrite min_r.
      assumption.
      rewrite Nat.lt_eq_cases.
      apply not_ge in HQ2.
      left. assumption.
      apply dec_ge.
      rewrite Nat.lt_eq_cases.
      left. assumption.
    * inversion H. inversion H0. subst.
      apply BigQuery. destruct H2 as [HQ1 | HQ2].
      assumption. assumption. assumption.
      rewrite max_r.
      rewrite H1 in H3. apply Nat.min_glb_lt. assumption. assumption.
      rewrite Nat.lt_eq_cases. right. assumption.
  - intros.
    inversion H. subst.
    apply Nat.max_lub_lt_iff in H2.
    destruct H2 as [H3 H4].
    apply Nat.min_glb_lt_iff in H3.
    apply Nat.min_glb_lt_iff in H4.
    destruct H3. destruct H4.
    inversion H. subst. clear H6. clear H7.
    
    assert (HMQ:=Nat.max_spec (pstart p1) (pstart p2)).
    destruct HMQ as [|].
    destruct H6 as [].
    
    apply TeradataSLt.
    apply PeriodR. assumption. assumption. assumption.
    unfold not. intros. destruct H8 as []. intuition. intuition.

    destruct H6 as [].
    rewrite Nat.lt_eq_cases in H6. destruct H6 as [|].
    
    apply TeradataSGt.
    apply PeriodR. assumption. assumption. assumption.
    unfold not. intros. destruct H9 as []. intuition.

    apply TeradataSEq.
    apply PeriodR. assumption. assumption. auto.

    decide equality.
Qed.
