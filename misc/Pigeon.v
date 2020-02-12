Require Import Omega.
Require Import List.
Require Import Arith.Euclid.

Parameter isin : nat -> nat -> Prop.

Inductive phlist (h:nat) : Set :=
| phnil : phlist h
| phcons : forall i hi (rest : phlist h),
             hi < h ->
             isin i hi ->
             phlist h.

Fixpoint phlen (h:nat) (l:phlist h) : nat :=
match l with
| phnil => 0
| phcons _ _ r _ _ => S (phlen h r)
end.

Lemma neq: forall h hi,
  hi < S h ->
  hi <> h ->
  hi < h.
Proof.
  intros. omega.
Qed.

Fixpoint phfilter (h:nat) (l:phlist (S h)) : (phlist (S h) * phlist h) :=
match l with 
| phnil => (phnil (S h), phnil h)
| phcons i hi r p1 p2 =>
     match (eq_nat_dec hi h) with
     | left _ => (phcons (S h) i hi (fst (phfilter h r)) p1 p2, (snd (phfilter h r)))
     | right q =>  ((fst (phfilter h r)), phcons h i hi (snd (phfilter h r)) (neq h hi p1 q) p2)
     end
end.

Lemma phlist_inv : forall h (l : phlist (S h)) l1 l2,
  phfilter h l = (l1, l2) ->
  phlen (S h) l = (phlen (S h) l1) + (phlen h l2).
Proof.
  intros h l. induction l; intros.
  simpl in *. inversion H. subst. simpl in *. auto.

  simpl in H.
  destruct (eq_nat_dec hi h).
  inversion H. subst.
  simpl.
  rewrite <- IHl. auto.
  rewrite <- surjective_pairing. auto.

  inversion H. subst.
  simpl.
  assert (phlen (S h) (fst (phfilter h l)) + S (phlen h (snd (phfilter h l))) = 
         S (phlen (S h) (fst (phfilter h l)) + (phlen h (snd (phfilter h l))))).
  omega.
  rewrite H0.
  rewrite <- IHl. auto.
  rewrite <- surjective_pairing. auto.
Qed.

Fixpoint phhas (h:nat) (i:nat) (l:phlist h) : Prop :=
match l with
| phnil => False
| phcons j _ r _ _ =>
    i = j \/ (phhas h i r)
end.

Inductive phlist_unique (h:nat) : phlist h -> Prop :=
| phu_nil  : phlist_unique h (phnil h)
| phu_cons : forall r i hi (p:hi < h) (q:isin i hi),
              phlist_unique h r ->
              ~phhas h i r ->
              phlist_unique h (phcons h i hi r p q)
.

Lemma has_filter_fst : forall h i r,
  phhas (S h) i (fst (phfilter h r)) ->
  phhas (S h) i r.
Proof.
  intros h i.
  induction r; intros.
  simpl in *. tauto.
  simpl in *.
  destruct (eq_nat_dec hi h).
  subst. simpl in *.  
  destruct H. left. auto.
  right. apply IHr; auto.
  simpl in *.
  right. apply IHr; auto.
Qed.

Lemma has_filter_snd : forall h i r,
  phhas h i (snd (phfilter h r)) ->
  phhas (S h) i r.
Proof.
  intros h i.
  induction r; intros.
  simpl in *. tauto.
  simpl in *.
  destruct (eq_nat_dec hi h).
  subst. simpl in *.  
  right. apply IHr; auto.
  simpl in *.
  destruct H. left. auto.
  right. apply IHr; auto.
Qed.
  
Lemma not_has_filter_fst : forall h i r,
  ~ phhas (S h) i r ->
  ~ phhas (S h) i (fst (phfilter h r)).
Proof.
  intros.
  unfold not.
  intros.
  apply H.
  apply has_filter_fst; auto.
Qed.
  
Lemma not_has_filter_snd : forall h i r,
  ~ phhas (S h) i r ->
  ~ phhas h i (snd (phfilter h r)).
  intros.
  unfold not.
  intros.
  apply H.
  apply has_filter_snd; auto.
Qed.

Lemma filter_unique: forall h (l:phlist (S h)) l1 l2,
  phlist_unique (S h) l ->
  phfilter h l = (l1, l2) ->
  phlist_unique (S h) l1 /\ phlist_unique h l2.
Proof.
  intros h l l1 l2 UN.
  generalize dependent l1. generalize dependent l2.
  induction UN; intros.
  simpl in H. inversion H. simpl. split; apply phu_nil; auto.
  simpl in H0.
  destruct (eq_nat_dec hi h); simpl in *.
  inversion H0. subst. split.
  apply phu_cons. lapply (IHUN (snd (phfilter h r)) (fst (phfilter h r))). 
  intros. destruct H1. auto. rewrite <- surjective_pairing. auto.
  apply not_has_filter_fst. auto.
  lapply (IHUN (snd (phfilter h r)) (fst (phfilter h r))). 
  intros. destruct H1. auto. rewrite <- surjective_pairing. auto.
  simpl in *.
  inversion H0; subst; split.
  lapply (IHUN (snd (phfilter h r)) (fst (phfilter h r))). 
  intros. destruct H1. auto. rewrite <- surjective_pairing. auto.
  apply phu_cons.   lapply (IHUN (snd (phfilter h r)) (fst (phfilter h r))). 
  intros. destruct H1. auto. rewrite <- surjective_pairing. auto.
  apply not_has_filter_snd; auto.
Qed.

Inductive same_holes (h:nat): phlist (S h) -> Prop :=
| sh_nil : same_holes h (phnil (S h))
| sh_cons : forall i r  (p: h < S h) (q:isin i h),
     same_holes h r ->
     same_holes h (phcons (S h) i h r p q)
.

Lemma filter_same_holes: forall h (l:phlist (S h)),
  same_holes h (fst (phfilter h l)).
Proof.
  intros h. 
  induction l; intros; simpl in *.
  apply sh_nil.
  destruct (eq_nat_dec hi h); simpl in *; auto.
  subst. apply sh_cons. auto.
Qed.

Lemma phlist_two : forall h (l:phlist (S h)),
  phlist_unique (S h) l ->
  same_holes h l ->
  phlen (S h) l >= 2 ->
  exists q1, exists q2, q1 <> q2 /\ isin q1 h /\ isin q2 h.
Proof.
  intros h l UN SH LEN.
  destruct l. simpl in LEN. assert False. omega. tauto.
  inversion UN. subst. inversion SH. subst.
  simpl in LEN.
  destruct l. simpl in LEN. assert False. omega. tauto.
  inversion H0. subst. inversion SH. subst.
  assert (i <> i1).
  unfold not. intros. apply H3. subst.
  simpl. left. auto.
  exists i. exists i1. tauto.
Qed.
  
Lemma mk_list: forall h p,
  (forall i, i < p -> exists hi, hi < h /\ isin i hi) ->
  exists l,
    phlist_unique h l /\
    (forall q, p <= q -> ~ phhas h q l) /\
    phlen h l = p.
Proof.
  intros h. induction p; intros.
  exists (phnil h). split. apply phu_nil. split.  simpl.  tauto. simpl. auto.
  lapply (H p); intros.
  destruct H0 as [hi [LT IN]].
  lapply IHp.
  intros.
  destruct H0 as [r [UN [NHAS LEN]]].
  exists (phcons h p hi r LT IN).
  repeat split. apply phu_cons; auto.
  intros. 
  unfold not. intros.  simpl in H1. destruct H1.
  subst. omega. assert (~ phhas h q r). apply NHAS. omega. tauto.
  simpl. subst. auto.
  intros.
  apply H. omega. omega.
Qed.

Lemma ph_strengthened : forall h l,
  phlist_unique h l ->
  h < phlen h l ->
  exists hx, (hx < h /\ exists q1, exists q2, q1 <> q2 /\ isin q1 hx /\ isin q2 hx).
Proof.
  induction h; intros; simpl in *.
  destruct l; simpl in *. inversion H0. inversion l0.
  assert (phfilter h l = (fst (phfilter h l), snd (phfilter h l))).
  rewrite <- surjective_pairing; auto.
  lapply (filter_unique h l (fst (phfilter h l)) (snd (phfilter h l))); intros; auto.
  
  destruct (le_lt_dec 2 (phlen (S h) (fst (phfilter h l)))).
  exists h. split. omega.
  apply (phlist_two h (fst (phfilter h l))); auto.
  tauto.
  apply filter_same_holes; auto. 

  destruct (IHh (snd (phfilter h l))) as [HX [LT [Q1 [Q2 [NEQ [IN1 IN2]]]]]].
  tauto.
  assert (phlen (S h) l = phlen (S h) (fst (phfilter h l)) + phlen h (snd (phfilter h l))).
  apply phlist_inv; auto.
  omega.
  exists HX. split; auto.
  exists Q1. exists Q2. tauto.
Qed.

Lemma pigeon_hole :
  forall (p:nat) (h:nat),
  (forall i, i < p -> exists hi, hi < h /\ isin i hi) ->
  h < p ->
  exists hx, (hx < h /\ exists q1, exists q2, q1 <> q2 /\ isin q1 hx /\ isin q2 hx).
Proof.  
  intros.
  lapply (mk_list h p); auto. intros.
  destruct H1 as [l [UN [ALL LEN]]].
  apply (ph_strengthened h l); auto.
  subst. auto.
Qed.

(* Dijkstra's formulation of the pigeonhole principle:

Fixpoint max (l : list nat) : nat :=
match l with
| nil     => 0
| x :: rest => if (le_lt_dec x (max rest)) then (max rest) else x
end.

Fixpoint sum (l : list nat) : nat :=
match l with
| nil => 0
| x :: rest => x + (sum rest)
end.

Definition avg (l:list nat) (p:length l > 0) : nat :=
  projT1 (quotient (length l) p (sum l)).



Lemma ph_dijkstra : forall (l:list nat)
  (p:length l > 0),
  max l >= (avg l p).
Proof.
  induction l; intros.
  simpl. inversion p.
  simpl in *.
  destruct (le_lt_dec a (max l)).
  destruct (le_lt_dec (length l) 0).
  inversion l1. destruct l. 
  unfold avg. simpl in *.
*)  
  
Definition bijection (f:nat -> nat) :=
  (forall x y, f x = f y -> x = y) /\
  (forall x, exists y, f y = x).

Lemma ph2: forall (p:nat) (h:nat) (hole_of : nat -> nat),
  (forall q, q < p -> hole_of q < h) ->
  h < p ->
  exists q1, exists q2, hole_of q1 = hole_of q2.
Proof.
  induction p; induction h; intros.
  inversion H0.
  inversion H0.
  lapply (H 0); auto. intros. inversion H1.
Admitted.  
    
Lemma ph_classical :  forall (p:nat) (h:nat),
  (forall P:Prop, P \/ ~P) ->
  (forall i, i < p -> exists hi, hi < h /\ isin i hi) ->
  h < p ->
  exists hx, (hx < h /\ exists q1, exists q2, q1 <> q2 /\ isin q1 hx /\ isin q2 hx).
Proof.  
  intros.
  generalize dependent p.
  induction h; intros.
  destruct (H0 0) as [hi [LT IN]].
  auto. inversion LT.
  destruct p. inversion H1.
  assert ((exists q1, isin q1 h)  \/ ~ (exists q1, isin q1 h)).
  apply H. 
  destruct H2.
  destruct H2 as [q1 IN1].
  assert ((exists q2, q1 <> q2 /\ isin q2 h) \/ ~(exists q2, q1 <> q2 /\ isin q2 h)).
  apply H. destruct H2.
  destruct H2 as [q2 [NEQ IN2]].
  exists h. split. omega.
  exists q1. exists q2. tauto.
  


  assert ((forall i : nat, i < S p -> exists hi : nat, hi < h /\ isin i hi) \/
         ~(forall i : nat, i < S p -> exists hi : nat, hi < h /\ isin i hi)).
  apply H. 
  destruct H2.
  destruct IHh as [HX [LT [ Q1 [Q2 [NEQ [IN1 IN2]]]]]]; auto.
  omega.
  exists HX. split. omega.
  exists Q1. exists Q2. tauto.

  destruct p. assert False. omega. tauto.
  destruct (H0 0) as [hi0 [LT0 IN0]]; try omega.
  destruct (H0 1) as [hi1 [LT1 IN1]]; try omega.
  destruct (eq_nat_dec hi0 hi1).
  subst.
  exists hi1. split. auto. exists 0. exists 1. split; auto.
  
  
  

  assert   
   ((exists hx : nat,
     hx < h /\
     (exists q1 : nat, exists q2 : nat, q1 <> q2 /\ isin q1 hx /\ isin q2 hx))
  \/ 
~(exists hx : nat,
     hx < h /\
     (exists q1 : nat, exists q2 : nat, q1 <> q2 /\ isin q1 hx /\ isin q2 hx))).
  apply H.
  destruct H2; auto.
  unfold not in H2.
  


  lapply (mk_list h p); auto. intros.
  destruct H1 as [l [UN [ALL LEN]]].
  apply (ph_strengthened h l); auto.
  subst. auto.


(***********************
  PIGEON HOLE PROBLEM
************************)

Parameter o11:Prop.
Parameter  o12:Prop.
Parameter  o13:Prop.
Parameter  o14:Prop.
Parameter  o15:Prop.
Parameter  o16:Prop.
Parameter  o17:Prop.
Parameter  o18:Prop.
Parameter  o19:Prop.
Parameter o110:Prop.
Parameter o21:Prop.
Parameter  o22:Prop.
Parameter  o23:Prop.
Parameter  o24:Prop.
Parameter  o25:Prop.
Parameter  o26:Prop.
Parameter  o27:Prop.
Parameter  o28:Prop.
Parameter  o29:Prop.
Parameter o210:Prop.
Parameter o31:Prop.
Parameter  o32:Prop.
Parameter  o33:Prop.
Parameter  o34:Prop.
Parameter  o35:Prop.
Parameter  o36:Prop.
Parameter  o37:Prop.
Parameter  o38:Prop.
Parameter  o39:Prop.
Parameter o310:Prop.
Parameter o41:Prop.
Parameter  o42:Prop.
Parameter  o43:Prop.
Parameter  o44:Prop.
Parameter  o45:Prop.
Parameter  o46:Prop.
Parameter  o47:Prop.
Parameter  o48:Prop.
Parameter  o49:Prop.
Parameter o410:Prop.
Parameter o51:Prop.
Parameter  o52:Prop.
Parameter  o53:Prop.
Parameter  o54:Prop.
Parameter  o55:Prop.
Parameter  o56:Prop.
Parameter  o57:Prop.
Parameter  o58:Prop.
Parameter  o59:Prop.
Parameter o510:Prop.
Parameter o61:Prop.
Parameter  o62:Prop.
Parameter  o63:Prop.
Parameter  o64:Prop.
Parameter  o65:Prop.
Parameter  o66:Prop.
Parameter  o67:Prop.
Parameter  o68:Prop.
Parameter  o69:Prop.
Parameter o610:Prop.
Parameter o71:Prop.
Parameter  o72:Prop.
Parameter  o73:Prop.
Parameter  o74:Prop.
Parameter  o75:Prop.
Parameter  o76:Prop.
Parameter  o77:Prop.
Parameter  o78:Prop.
Parameter  o79:Prop.
Parameter o710:Prop.
Parameter o81:Prop.
Parameter  o82:Prop.
Parameter  o83:Prop.
Parameter  o84:Prop.
Parameter  o85:Prop.
Parameter  o86:Prop.
Parameter  o87:Prop.
Parameter  o88:Prop.
Parameter  o89:Prop.
Parameter o810:Prop.
Parameter o91:Prop.
Parameter  o92:Prop.
Parameter  o93:Prop.
Parameter  o94:Prop.
Parameter  o95:Prop.
Parameter  o96:Prop.
Parameter  o97:Prop.
Parameter  o98:Prop.
Parameter  o99:Prop.
Parameter o910:Prop.
Parameter o101:Prop.
Parameter  o102:Prop.
Parameter  o103:Prop.
Parameter  o104:Prop.
Parameter  o105:Prop.
Parameter  o106:Prop.
Parameter  o107:Prop.
Parameter  o108:Prop.
Parameter  o109:Prop.
Parameter o1010:Prop.
Parameter o111:Prop.
Parameter  o112:Prop.
Parameter  o113:Prop.
Parameter  o114:Prop.
Parameter  o115:Prop.
Parameter  o116:Prop.
Parameter  o117:Prop.
Parameter  o118:Prop.
Parameter  o119:Prop.
Parameter o1110:Prop.

Definition Axiom1:Prop :=
( o11 \/ ( o12 \/ ( o13 \/ ( o14 \/ ( o15 \/ ( o16 \/ ( o17 \/ ( o18 \/ ( o19 \/ o110 ) ) ) ) ) ) ) ) ).

Definition Axiom2:Prop :=
( o21 \/ ( o22 \/ ( o23 \/ ( o24 \/ ( o25 \/ ( o26 \/ ( o27 \/ ( o28 \/ ( o29 \/ o210 ) ) ) ) ) ) ) ) ).

Definition Axiom3:Prop :=
( o31 \/ ( o32 \/ ( o33 \/ ( o34 \/ ( o35 \/ ( o36 \/ ( o37 \/ ( o38 \/ ( o39 \/ o310 ) ) ) ) ) ) ) ) ).

Definition Axiom4:Prop :=
( o41 \/ ( o42 \/ ( o43 \/ ( o44 \/ ( o45 \/ ( o46 \/ ( o47 \/ ( o48 \/ ( o49 \/ o410 ) ) ) ) ) ) ) ) ).

Definition Axiom5:Prop :=
( o51 \/ ( o52 \/ ( o53 \/ ( o54 \/ ( o55 \/ ( o56 \/ ( o57 \/ ( o58 \/ ( o59 \/ o510 ) ) ) ) ) ) ) ) ).

Definition Axiom6:Prop :=
( o61 \/ ( o62 \/ ( o63 \/ ( o64 \/ ( o65 \/ ( o66 \/ ( o67 \/ ( o68 \/ ( o69 \/ o610 ) ) ) ) ) ) ) ) ).

Definition Axiom7:Prop :=
( o71 \/ ( o72 \/ ( o73 \/ ( o74 \/ ( o75 \/ ( o76 \/ ( o77 \/ ( o78 \/ ( o79 \/ o710 ) ) ) ) ) ) ) ) ).

Definition Axiom8:Prop :=
( o81 \/ ( o82 \/ ( o83 \/ ( o84 \/ ( o85 \/ ( o86 \/ ( o87 \/ ( o88 \/ ( o89 \/ o810 ) ) ) ) ) ) ) ) ).

Definition Axiom9:Prop :=
( o91 \/ ( o92 \/ ( o93 \/ ( o94 \/ ( o95 \/ ( o96 \/ ( o97 \/ ( o98 \/ ( o99 \/ o910 ) ) ) ) ) ) ) ) ).

Definition Axiom10:Prop :=
( o101 \/ ( o102 \/ ( o103 \/ ( o104 \/ ( o105 \/ ( o106 \/ ( o107 \/ ( o108 \/ ( o109 \/ o1010 ) ) ) ) ) ) ) )).

Definition Axiom11:Prop :=
( o111 \/ ( o112 \/ ( o113 \/ ( o114 \/ ( o115 \/ ( o116 \/ ( o117 \/ ( o118 \/ ( o119 \/ o1110 ) ) ) ) ) ) ) )).

Lemma pigeon_hole : 
Axiom1 /\ Axiom2 /\ Axiom3 /\ Axiom4 /\ Axiom5 /\ Axiom6 /\ Axiom7 /\ Axiom8 /\ Axiom9 /\ Axiom10 /\ Axiom11 ->

( ( o11 /\ o21 ) \/ ( ( o11 /\ o31 ) \/ ( ( o11 /\ o41 ) \/ ( ( o11 /\ o51 ) \/ ( ( o11 /\ o61 ) \/ ( ( o11 /\ o71 ) \/ ( ( o11 /\ o81 ) \/ ( ( o11 /\ o91 ) \/ ( ( o11 /\ o101 ) \/ ( ( o11 /\ o111 ) \/ ( ( o21 /\ o31 ) \/ ( ( o21 /\ o41 ) \/ ( ( o21 /\ o51 ) \/ ( ( o21 /\ o61 ) \/ ( ( o21 /\ o71 ) \/ ( ( o21 /\ o81 ) \/ ( ( o21 /\ o91 ) \/ ( ( o21 /\ o101 ) \/ ( ( o21 /\ o111 ) \/ ( ( o31 /\ o41 ) \/ ( ( o31 /\ o51 ) \/ ( ( o31 /\ o61 ) \/ ( ( o31 /\ o71 ) \/ ( ( o31 /\ o81 ) \/ ( ( o31 /\ o91 ) \/ ( ( o31 /\ o101 ) \/ ( ( o31 /\ o111 ) \/ ( ( o41 /\ o51 ) \/ ( ( o41 /\ o61 ) \/ ( ( o41 /\ o71 ) \/ ( ( o41 /\ o81 ) \/ ( ( o41 /\ o91 ) \/ ( ( o41 /\ o101 ) \/ ( ( o41 /\ o111 ) \/ ( ( o51 /\ o61 ) \/ ( ( o51 /\ o71 ) \/ ( ( o51 /\ o81 ) \/ ( ( o51 /\ o91 ) \/ ( ( o51 /\ o101 ) \/ ( ( o51 /\ o111 ) \/ ( ( o61 /\ o71 ) \/ ( ( o61 /\ o81 ) \/ ( ( o61 /\ o91 ) \/ ( ( o61 /\ o101 ) \/ ( ( o61 /\ o111 ) \/ ( ( o71 /\ o81 ) \/ ( ( o71 /\ o91 ) \/ ( ( o71 /\ o101 ) \/ ( ( o71 /\ o111 ) \/ ( ( o81 /\ o91 ) \/ ( ( o81 /\ o101 ) \/ ( ( o81 /\ o111 ) \/ ( ( o91 /\ o101 ) \/ ( ( o91 /\ o111 ) \/ ( ( o101 /\ o111 ) \/ ( ( o12 /\ o22 ) \/ ( ( o12 /\ o32 ) \/ ( ( o12 /\ o42 ) \/ ( ( o12 /\ o52 ) \/ ( ( o12 /\ o62 ) \/ ( ( o12 /\ o72 ) \/ ( ( o12 /\ o82 ) \/ ( ( o12 /\ o92 ) \/ ( ( o12 /\ o102 ) \/ ( ( o12 /\ o112 ) \/ ( ( o22 /\ o32 ) \/ ( ( o22 /\ o42 ) \/ ( ( o22 /\ o52 ) \/ ( ( o22 /\ o62 ) \/ ( ( o22 /\ o72 ) \/ ( ( o22 /\ o82 ) \/ ( ( o22 /\ o92 ) \/ ( ( o22 /\ o102 ) \/ ( ( o22 /\ o112 ) \/ ( ( o32 /\ o42 ) \/ ( ( o32 /\ o52 ) \/ ( ( o32 /\ o62 ) \/ ( ( o32 /\ o72 ) \/ ( ( o32 /\ o82 ) \/ ( ( o32 /\ o92 ) \/ ( ( o32 /\ o102 ) \/ ( ( o32 /\ o112 ) \/ ( ( o42 /\ o52 ) \/ ( ( o42 /\ o62 ) \/ ( ( o42 /\ o72 ) \/ ( ( o42 /\ o82 ) \/ ( ( o42 /\ o92 ) \/ ( ( o42 /\ o102 ) \/ ( ( o42 /\ o112 ) \/ ( ( o52 /\ o62 ) \/ ( ( o52 /\ o72 ) \/ ( ( o52 /\ o82 ) \/ ( ( o52 /\ o92 ) \/ ( ( o52 /\ o102 ) \/ ( ( o52 /\ o112 ) \/ ( ( o62 /\ o72 ) \/ ( ( o62 /\ o82 ) \/ ( ( o62 /\ o92 ) \/ ( ( o62 /\ o102 ) \/ ( ( o62 /\ o112 ) \/ ( ( o72 /\ o82 ) \/ ( ( o72 /\ o92 ) \/ ( ( o72 /\ o102 ) \/ ( ( o72 /\ o112 ) \/ ( ( o82 /\ o92 ) \/ ( ( o82 /\ o102 ) \/ ( ( o82 /\ o112 ) \/ ( ( o92 /\ o102 ) \/ ( ( o92 /\ o112 ) \/ ( ( o102 /\ o112 ) \/ ( ( o13 /\ o23 ) \/ ( ( o13 /\ o33 ) \/ ( ( o13 /\ o43 ) \/ ( ( o13 /\ o53 ) \/ ( ( o13 /\ o63 ) \/ ( ( o13 /\ o73 ) \/ ( ( o13 /\ o83 ) \/ ( ( o13 /\ o93 ) \/ ( ( o13 /\ o103 ) \/ ( ( o13 /\ o113 ) \/ ( ( o23 /\ o33 ) \/ ( ( o23 /\ o43 ) \/ ( ( o23 /\ o53 ) \/ ( ( o23 /\ o63 ) \/ ( ( o23 /\ o73 ) \/ ( ( o23 /\ o83 ) \/ ( ( o23 /\ o93 ) \/ ( ( o23 /\ o103 ) \/ ( ( o23 /\ o113 ) \/ ( ( o33 /\ o43 ) \/ ( ( o33 /\ o53 ) \/ ( ( o33 /\ o63 ) \/ ( ( o33 /\ o73 ) \/ ( ( o33 /\ o83 ) \/ ( ( o33 /\ o93 ) \/ ( ( o33 /\ o103 ) \/ ( ( o33 /\ o113 ) \/ ( ( o43 /\ o53 ) \/ ( ( o43 /\ o63 ) \/ ( ( o43 /\ o73 ) \/ ( ( o43 /\ o83 ) \/ ( ( o43 /\ o93 ) \/ ( ( o43 /\ o103 ) \/ ( ( o43 /\ o113 ) \/ ( ( o53 /\ o63 ) \/ ( ( o53 /\ o73 ) \/ ( ( o53 /\ o83 ) \/ ( ( o53 /\ o93 ) \/ ( ( o53 /\ o103 ) \/ ( ( o53 /\ o113 ) \/ ( ( o63 /\ o73 ) \/ ( ( o63 /\ o83 ) \/ ( ( o63 /\ o93 ) \/ ( ( o63 /\ o103 ) \/ ( ( o63 /\ o113 ) \/ ( ( o73 /\ o83 ) \/ ( ( o73 /\ o93 ) \/ ( ( o73 /\ o103 ) \/ ( ( o73 /\ o113 ) \/ ( ( o83 /\ o93 ) \/ ( ( o83 /\ o103 ) \/ ( ( o83 /\ o113 ) \/ ( ( o93 /\ o103 ) \/ ( ( o93 /\ o113 ) \/ ( ( o103 /\ o113 ) \/ ( ( o14 /\ o24 ) \/ ( ( o14 /\ o34 ) \/ ( ( o14 /\ o44 ) \/ ( ( o14 /\ o54 ) \/ ( ( o14 /\ o64 ) \/ ( ( o14 /\ o74 ) \/ ( ( o14 /\ o84 ) \/ ( ( o14 /\ o94 ) \/ ( ( o14 /\ o104 ) \/ ( ( o14 /\ o114 ) \/ ( ( o24 /\ o34 ) \/ ( ( o24 /\ o44 ) \/ ( ( o24 /\ o54 ) \/ ( ( o24 /\ o64 ) \/ ( ( o24 /\ o74 ) \/ ( ( o24 /\ o84 ) \/ ( ( o24 /\ o94 ) \/ ( ( o24 /\ o104 ) \/ ( ( o24 /\ o114 ) \/ ( ( o34 /\ o44 ) \/ ( ( o34 /\ o54 ) \/ ( ( o34 /\ o64 ) \/ ( ( o34 /\ o74 ) \/ ( ( o34 /\ o84 ) \/ ( ( o34 /\ o94 ) \/ ( ( o34 /\ o104 ) \/ ( ( o34 /\ o114 ) \/ ( ( o44 /\ o54 ) \/ ( ( o44 /\ o64 ) \/ ( ( o44 /\ o74 ) \/ ( ( o44 /\ o84 ) \/ ( ( o44 /\ o94 ) \/ ( ( o44 /\ o104 ) \/ ( ( o44 /\ o114 ) \/ ( ( o54 /\ o64 ) \/ ( ( o54 /\ o74 ) \/ ( ( o54 /\ o84 ) \/ ( ( o54 /\ o94 ) \/ ( ( o54 /\ o104 ) \/ ( ( o54 /\ o114 ) \/ ( ( o64 /\ o74 ) \/ ( ( o64 /\ o84 ) \/ ( ( o64 /\ o94 ) \/ ( ( o64 /\ o104 ) \/ ( ( o64 /\ o114 ) \/ ( ( o74 /\ o84 ) \/ ( ( o74 /\ o94 ) \/ ( ( o74 /\ o104 ) \/ ( ( o74 /\ o114 ) \/ ( ( o84 /\ o94 ) \/ ( ( o84 /\ o104 ) \/ ( ( o84 /\ o114 ) \/ ( ( o94 /\ o104 ) \/ ( ( o94 /\ o114 ) \/ ( ( o104 /\ o114 ) \/ ( ( o15 /\ o25 ) \/ ( ( o15 /\ o35 ) \/ ( ( o15 /\ o45 ) \/ ( ( o15 /\ o55 ) \/ ( ( o15 /\ o65 ) \/ ( ( o15 /\ o75 ) \/ ( ( o15 /\ o85 ) \/ ( ( o15 /\ o95 ) \/ ( ( o15 /\ o105 ) \/ ( ( o15 /\ o115 ) \/ ( ( o25 /\ o35 ) \/ ( ( o25 /\ o45 ) \/ ( ( o25 /\ o55 ) \/ ( ( o25 /\ o65 ) \/ ( ( o25 /\ o75 ) \/ ( ( o25 /\ o85 ) \/ ( ( o25 /\ o95 ) \/ ( ( o25 /\ o105 ) \/ ( ( o25 /\ o115 ) \/ ( ( o35 /\ o45 ) \/ ( ( o35 /\ o55 ) \/ ( ( o35 /\ o65 ) \/ ( ( o35 /\ o75 ) \/ ( ( o35 /\ o85 ) \/ ( ( o35 /\ o95 ) \/ ( ( o35 /\ o105 ) \/ ( ( o35 /\ o115 ) \/ ( ( o45 /\ o55 ) \/ ( ( o45 /\ o65 ) \/ ( ( o45 /\ o75 ) \/ ( ( o45 /\ o85 ) \/ ( ( o45 /\ o95 ) \/ ( ( o45 /\ o105 ) \/ ( ( o45 /\ o115 ) \/ ( ( o55 /\ o65 ) \/ ( ( o55 /\ o75 ) \/ ( ( o55 /\ o85 ) \/ ( ( o55 /\ o95 ) \/ ( ( o55 /\ o105 ) \/ ( ( o55 /\ o115 ) \/ ( ( o65 /\ o75 ) \/ ( ( o65 /\ o85 ) \/ ( ( o65 /\ o95 ) \/ ( ( o65 /\ o105 ) \/ ( ( o65 /\ o115 ) \/ ( ( o75 /\ o85 ) \/ ( ( o75 /\ o95 ) \/ ( ( o75 /\ o105 ) \/ ( ( o75 /\ o115 ) \/ ( ( o85 /\ o95 ) \/ ( ( o85 /\ o105 ) \/ ( ( o85 /\ o115 ) \/ ( ( o95 /\ o105 ) \/ ( ( o95 /\ o115 ) \/ ( ( o105 /\ o115 ) \/ ( ( o16 /\ o26 ) \/ ( ( o16 /\ o36 ) \/ ( ( o16 /\ o46 ) \/ ( ( o16 /\ o56 ) \/ ( ( o16 /\ o66 ) \/ ( ( o16 /\ o76 ) \/ ( ( o16 /\ o86 ) \/ ( ( o16 /\ o96 ) \/ ( ( o16 /\ o106 ) \/ ( ( o16 /\ o116 ) \/ ( ( o26 /\ o36 ) \/ ( ( o26 /\ o46 ) \/ ( ( o26 /\ o56 ) \/ ( ( o26 /\ o66 ) \/ ( ( o26 /\ o76 ) \/ ( ( o26 /\ o86 ) \/ ( ( o26 /\ o96 ) \/ ( ( o26 /\ o106 ) \/ ( ( o26 /\ o116 ) \/ ( ( o36 /\ o46 ) \/ ( ( o36 /\ o56 ) \/ ( ( o36 /\ o66 ) \/ ( ( o36 /\ o76 ) \/ ( ( o36 /\ o86 ) \/ ( ( o36 /\ o96 ) \/ ( ( o36 /\ o106 ) \/ ( ( o36 /\ o116 ) \/ ( ( o46 /\ o56 ) \/ ( ( o46 /\ o66 ) \/ ( ( o46 /\ o76 ) \/ ( ( o46 /\ o86 ) \/ ( ( o46 /\ o96 ) \/ ( ( o46 /\ o106 ) \/ ( ( o46 /\ o116 ) \/ ( ( o56 /\ o66 ) \/ ( ( o56 /\ o76 ) \/ ( ( o56 /\ o86 ) \/ ( ( o56 /\ o96 ) \/ ( ( o56 /\ o106 ) \/ ( ( o56 /\ o116 ) \/ ( ( o66 /\ o76 ) \/ ( ( o66 /\ o86 ) \/ ( ( o66 /\ o96 ) \/ ( ( o66 /\ o106 ) \/ ( ( o66 /\ o116 ) \/ ( ( o76 /\ o86 ) \/ ( ( o76 /\ o96 ) \/ ( ( o76 /\ o106 ) \/ ( ( o76 /\ o116 ) \/ ( ( o86 /\ o96 ) \/ ( ( o86 /\ o106 ) \/ ( ( o86 /\ o116 ) \/ ( ( o96 /\ o106 ) \/ ( ( o96 /\ o116 ) \/ ( ( o106 /\ o116 ) \/ ( ( o17 /\ o27 ) \/ ( ( o17 /\ o37 ) \/ ( ( o17 /\ o47 ) \/ ( ( o17 /\ o57 ) \/ ( ( o17 /\ o67 ) \/ ( ( o17 /\ o77 ) \/ ( ( o17 /\ o87 ) \/ ( ( o17 /\ o97 ) \/ ( ( o17 /\ o107 ) \/ ( ( o17 /\ o117 ) \/ ( ( o27 /\ o37 ) \/ ( ( o27 /\ o47 ) \/ ( ( o27 /\ o57 ) \/ ( ( o27 /\ o67 ) \/ ( ( o27 /\ o77 ) \/ ( ( o27 /\ o87 ) \/ ( ( o27 /\ o97 ) \/ ( ( o27 /\ o107 ) \/ ( ( o27 /\ o117 ) \/ ( ( o37 /\ o47 ) \/ ( ( o37 /\ o57 ) \/ ( ( o37 /\ o67 ) \/ ( ( o37 /\ o77 ) \/ ( ( o37 /\ o87 ) \/ ( ( o37 /\ o97 ) \/ ( ( o37 /\ o107 ) \/ ( ( o37 /\ o117 ) \/ ( ( o47 /\ o57 ) \/ ( ( o47 /\ o67 ) \/ ( ( o47 /\ o77 ) \/ ( ( o47 /\ o87 ) \/ ( ( o47 /\ o97 ) \/ ( ( o47 /\ o107 ) \/ ( ( o47 /\ o117 ) \/ ( ( o57 /\ o67 ) \/ ( ( o57 /\ o77 ) \/ ( ( o57 /\ o87 ) \/ ( ( o57 /\ o97 ) \/ ( ( o57 /\ o107 ) \/ ( ( o57 /\ o117 ) \/ ( ( o67 /\ o77 ) \/ ( ( o67 /\ o87 ) \/ ( ( o67 /\ o97 ) \/ ( ( o67 /\ o107 ) \/ ( ( o67 /\ o117 ) \/ ( ( o77 /\ o87 ) \/ ( ( o77 /\ o97 ) \/ ( ( o77 /\ o107 ) \/ ( ( o77 /\ o117 ) \/ ( ( o87 /\ o97 ) \/ ( ( o87 /\ o107 ) \/ ( ( o87 /\ o117 ) \/ ( ( o97 /\ o107 ) \/ ( ( o97 /\ o117 ) \/ ( ( o107 /\ o117 ) \/ ( ( o18 /\ o28 ) \/ ( ( o18 /\ o38 ) \/ ( ( o18 /\ o48 ) \/ ( ( o18 /\ o58 ) \/ ( ( o18 /\ o68 ) \/ ( ( o18 /\ o78 ) \/ ( ( o18 /\ o88 ) \/ ( ( o18 /\ o98 ) \/ ( ( o18 /\ o108 ) \/ ( ( o18 /\ o118 ) \/ ( ( o28 /\ o38 ) \/ ( ( o28 /\ o48 ) \/ ( ( o28 /\ o58 ) \/ ( ( o28 /\ o68 ) \/ ( ( o28 /\ o78 ) \/ ( ( o28 /\ o88 ) \/ ( ( o28 /\ o98 ) \/ ( ( o28 /\ o108 ) \/ ( ( o28 /\ o118 ) \/ ( ( o38 /\ o48 ) \/ ( ( o38 /\ o58 ) \/ ( ( o38 /\ o68 ) \/ ( ( o38 /\ o78 ) \/ ( ( o38 /\ o88 ) \/ ( ( o38 /\ o98 ) \/ ( ( o38 /\ o108 ) \/ ( ( o38 /\ o118 ) \/ ( ( o48 /\ o58 ) \/ ( ( o48 /\ o68 ) \/ ( ( o48 /\ o78 ) \/ ( ( o48 /\ o88 ) \/ ( ( o48 /\ o98 ) \/ ( ( o48 /\ o108 ) \/ ( ( o48 /\ o118 ) \/ ( ( o58 /\ o68 ) \/ ( ( o58 /\ o78 ) \/ ( ( o58 /\ o88 ) \/ ( ( o58 /\ o98 ) \/ ( ( o58 /\ o108 ) \/ ( ( o58 /\ o118 ) \/ ( ( o68 /\ o78 ) \/ ( ( o68 /\ o88 ) \/ ( ( o68 /\ o98 ) \/ ( ( o68 /\ o108 ) \/ ( ( o68 /\ o118 ) \/ ( ( o78 /\ o88 ) \/ ( ( o78 /\ o98 ) \/ ( ( o78 /\ o108 ) \/ ( ( o78 /\ o118 ) \/ ( ( o88 /\ o98 ) \/ ( ( o88 /\ o108 ) \/ ( ( o88 /\ o118 ) \/ ( ( o98 /\ o108 ) \/ ( ( o98 /\ o118 ) \/ ( ( o108 /\ o118 ) \/ ( ( o19 /\ o29 ) \/ ( ( o19 /\ o39 ) \/ ( ( o19 /\ o49 ) \/ ( ( o19 /\ o59 ) \/ ( ( o19 /\ o69 ) \/ ( ( o19 /\ o79 ) \/ ( ( o19 /\ o89 ) \/ ( ( o19 /\ o99 ) \/ ( ( o19 /\ o109 ) \/ ( ( o19 /\ o119 ) \/ ( ( o29 /\ o39 ) \/ ( ( o29 /\ o49 ) \/ ( ( o29 /\ o59 ) \/ ( ( o29 /\ o69 ) \/ ( ( o29 /\ o79 ) \/ ( ( o29 /\ o89 ) \/ ( ( o29 /\ o99 ) \/ ( ( o29 /\ o109 ) \/ ( ( o29 /\ o119 ) \/ ( ( o39 /\ o49 ) \/ ( ( o39 /\ o59 ) \/ ( ( o39 /\ o69 ) \/ ( ( o39 /\ o79 ) \/ ( ( o39 /\ o89 ) \/ ( ( o39 /\ o99 ) \/ ( ( o39 /\ o109 ) \/ ( ( o39 /\ o119 ) \/ ( ( o49 /\ o59 ) \/ ( ( o49 /\ o69 ) \/ ( ( o49 /\ o79 ) \/ ( ( o49 /\ o89 ) \/ ( ( o49 /\ o99 ) \/ ( ( o49 /\ o109 ) \/ ( ( o49 /\ o119 ) \/ ( ( o59 /\ o69 ) \/ ( ( o59 /\ o79 ) \/ ( ( o59 /\ o89 ) \/ ( ( o59 /\ o99 ) \/ ( ( o59 /\ o109 ) \/ ( ( o59 /\ o119 ) \/ ( ( o69 /\ o79 ) \/ ( ( o69 /\ o89 ) \/ ( ( o69 /\ o99 ) \/ ( ( o69 /\ o109 ) \/ ( ( o69 /\ o119 ) \/ ( ( o79 /\ o89 ) \/ ( ( o79 /\ o99 ) \/ ( ( o79 /\ o109 ) \/ ( ( o79 /\ o119 ) \/ ( ( o89 /\ o99 ) \/ ( ( o89 /\ o109 ) \/ ( ( o89 /\ o119 ) \/ ( ( o99 /\ o109 ) \/ ( ( o99 /\ o119 ) \/ ( ( o109 /\ o119 ) \/ ( ( o110 /\ o210 ) \/ ( ( o110 /\ o310 ) \/ ( ( o110 /\ o410 ) \/ ( ( o110 /\ o510 ) \/ ( ( o110 /\ o610 ) \/ ( ( o110 /\ o710 ) \/ ( ( o110 /\ o810 ) \/ ( ( o110 /\ o910 ) \/ ( ( o110 /\ o1010 ) \/ ( ( o110 /\ o1110 ) \/ ( ( o210 /\ o310 ) \/ ( ( o210 /\ o410 ) \/ ( ( o210 /\ o510 ) \/ ( ( o210 /\ o610 ) \/ ( ( o210 /\ o710 ) \/ ( ( o210 /\ o810 ) \/ ( ( o210 /\ o910 ) \/ ( ( o210 /\ o1010 ) \/ ( ( o210 /\ o1110 ) \/ ( ( o310 /\ o410 ) \/ ( ( o310 /\ o510 ) \/ ( ( o310 /\ o610 ) \/ ( ( o310 /\ o710 ) \/ ( ( o310 /\ o810 ) \/ ( ( o310 /\ o910 ) \/ ( ( o310 /\ o1010 ) \/ ( ( o310 /\ o1110 ) \/ ( ( o410 /\ o510 ) \/ ( ( o410 /\ o610 ) \/ ( ( o410 /\ o710 ) \/ ( ( o410 /\ o810 ) \/ ( ( o410 /\ o910 ) \/ ( ( o410 /\ o1010 ) \/ ( ( o410 /\ o1110 ) \/ ( ( o510 /\ o610 ) \/ ( ( o510 /\ o710 ) \/ ( ( o510 /\ o810 ) \/ ( ( o510 /\ o910 ) \/ ( ( o510 /\ o1010 ) \/ ( ( o510 /\ o1110 ) \/ ( ( o610 /\ o710 ) \/ ( ( o610 /\ o810 ) \/ ( ( o610 /\ o910 ) \/ ( ( o610 /\ o1010 ) \/ ( ( o610 /\ o1110 ) \/ ( ( o710 /\ o810 ) \/ ( ( o710 /\ o910 ) \/ ( ( o710 /\ o1010 ) \/ ( ( o710 /\ o1110 ) \/ ( ( o810 /\ o910 ) \/ ( ( o810 /\ o1010 ) \/ ( ( o810 /\ o1110 ) \/ ( ( o910 /\ o1010 ) \/ ( ( o910 /\ o1110 ) \/ ( o1010 /\ o1110 ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ).
Proof.
