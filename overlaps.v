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
  - intros H. inversion H; subst;
    inversion H0; inversion H1; subst; apply BigQuery; try assumption;
      try (apply Decidable.not_and in H3; try apply dec_ge);
      destruct H3 as [|].
      * rewrite max_l.
        + apply not_le in H3. apply Nat.min_glb_lt; assumption.
        + apply not_ge in H3. rewrite Nat.lt_eq_cases. left. assumption.
      * rewrite min_l; apply not_ge in H3.
        + rewrite max_l. assumption.
          rewrite Nat.lt_eq_cases. left. assumption.
        + rewrite Nat.lt_eq_cases. left. assumption.
      * rewrite max_r.
        + apply not_ge in H3. apply Nat.min_glb_lt; assumption.
        + rewrite Nat.lt_eq_cases. left. assumption.
      * rewrite max_r.
        + rewrite min_r. assumption.
          rewrite Nat.lt_eq_cases. apply not_ge in H3. left. assumption.
        + rewrite Nat.lt_eq_cases. left. assumption.
      * rewrite max_r.
        + rewrite min_r. assumption.
          rewrite Nat.lt_eq_cases. right. symmetry. assumption.
        + rewrite Nat.lt_eq_cases. right. assumption.
      * rewrite max_r.
        + rewrite H2 in H4. apply Nat.min_glb_lt; assumption.
        + rewrite Nat.lt_eq_cases. right. assumption.
  - intros H. inversion H. subst.
    apply Nat.max_lub_lt_iff in H2.
    destruct H2 as [H3 H4].
    apply Nat.min_glb_lt_iff in H3.
    apply Nat.min_glb_lt_iff in H4.
    destruct H3. destruct H4.
    assert (HMQ:=Nat.max_spec (pstart p1) (pstart p2)).
    destruct HMQ as [|]; destruct H6 as [].
    * apply TeradataSLt.
      apply PeriodR. assumption. assumption. assumption.
      unfold not. intros. destruct H8 as []. intuition.
    * rewrite Nat.lt_eq_cases in H6. destruct H6 as [|].
      + apply TeradataSGt.
        apply PeriodR. assumption. assumption. assumption.
        unfold not. intros. destruct H8 as []. intuition.
      + apply TeradataSEq.
        apply PeriodR. assumption. assumption. auto.
        decide equality.
Qed.
