Require Import Stdlib.Strings.String.
Require Import Stdlib.Strings.Ascii.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import euler.pb54.pb54.

(* iff *)

Lemma IsBetterCombo_rank : forall c1 c2, IsBetterCombo c1 c2 -> combo_rank c1 > combo_rank c2.
Proof.
  intros c1 c2 H.
  induction H.
  - simpl; lia.
  - simpl; lia.
  - simpl; lia.
  - simpl; lia.
  - simpl; lia.
  - simpl; lia.
  - simpl; lia.
  - simpl; lia.
  - simpl; lia.
  - simpl; lia.
Qed.


Definition GetDirectlyBelowOrSame (cb : Combo) :=
  match cb with
  | HighCard => HighCard
  | Pair => HighCard
  | TwoPairs => Pair
  | Triple => TwoPairs
  | Straight => Triple
  | Flush => Straight
  | FullHouse => Flush
  | Four => FullHouse
  | StraighFlush => Four
  | RoyalFlush => StraighFlush
  end.

Lemma IsBetterReduceLeft : forall cb1 cb2,
  IsBetterCombo cb1 cb2 ->
  ~ DirectlyBelowCombo cb2 cb1 ->
  IsBetterCombo (GetDirectlyBelowOrSame cb1) cb2.
Proof.
Admitted.

Lemma IsBetterComboIncreaseLeft : forall cb1 cb2,
  IsBetterCombo (GetDirectlyBelowOrSame cb1) cb2 ->
  IsBetterCombo cb1 cb2.
Proof.
Admitted.

Lemma rank_IsBetterCombo : forall c1 c2,
  combo_rank c1 > combo_rank c2 -> IsBetterCombo c1 c2.
Proof. 
  intros. induction c1.
  - destruct c2; simpl in H; lia.
  - destruct c2; simpl in H; try constructor; try lia.
  - destruct c2; simpl in H; try constructor; try lia;
    apply IsBetterComboIncreaseLeft; simpl; constructor.
  - destruct c2; simpl in H; try constructor; try lia.
    apply IsBetterComboIncreaseLeft. simpl. apply IsBetterComboIncreaseLeft. simpl. constructor.
    apply IsBetterComboIncreaseLeft. simpl. constructor.
Admitted.

Lemma IsBetterCombo_iff : forall c1 c2,
  IsBetterCombo c1 c2 <-> combo_rank c1 > combo_rank c2.
Proof.
 intros. split.
  - apply  IsBetterCombo_rank.
  - apply rank_IsBetterCombo.
Qed.

(* Better combo *) 
 
Theorem TripleBeatsPair :
  IsBetterCombo Triple Pair.
Proof. apply Trans2 with TwoPairs. constructor. constructor. Qed.

Theorem FourBeatsPair :
  IsBetterCombo Four Pair.
Proof. apply Trans2 with FullHouse.
  constructor.
  apply Trans2 with Flush.
  constructor.
  apply Trans2 with Straight.
  constructor.
  apply Trans2 with Triple.
  constructor.
  apply TripleBeatsPair.
  Qed.
  
Theorem TwoPairsIsNotBetterThanTriple :
  ~ IsBetterCombo TwoPairs Triple.
Proof.
  intros H.
  apply IsBetterCombo_rank in H.
  simpl in H.
  lia.
Qed.

Theorem HighCardIsBetterThanNothing :
  forall (cb : Combo), ~ IsBetterCombo HighCard cb.
Proof. 
intros. unfold not. intros. apply IsBetterCombo_iff in H. simpl in H. destruct cb; lia. Qed.

Theorem ComboIsNotBetterThanHimself :
  forall (cb : Combo), ~ IsBetterCombo cb cb.
Proof. Admitted.

Lemma IsDirectlyBelowHighCardPair : 
  DirectlyBelowCombo HighCard Pair.
Proof. 
  constructor. constructor. unfold not.
  intros. destruct H. destruct x.
  - destruct H. apply (ComboIsNotBetterThanHimself HighCard) in H0. assumption.
  - destruct H. apply (ComboIsNotBetterThanHimself Pair) in H. assumption.
  - destruct H. apply IsBetterCombo_rank in H. simpl in H. lia.
  - destruct H. apply IsBetterCombo_rank in H. simpl in H. lia.
  - destruct H. apply IsBetterCombo_rank in H. simpl in H. lia.
  - destruct H. apply IsBetterCombo_rank in H. simpl in H. lia.
  - destruct H. apply IsBetterCombo_rank in H. simpl in H. lia.
  - destruct H. apply IsBetterCombo_rank in H. simpl in H. lia.
  - destruct H. apply IsBetterCombo_rank in H. simpl in H. lia.
  - destruct H. apply IsBetterCombo_rank in H. simpl in H. lia.
Qed.

Theorem RoyalFlushIsBetterThanEverthing :
  forall (cb : Combo),
  IsBetterCombo RoyalFlush cb \/ cb = RoyalFlush.
Proof. 
  intros. destruct cb; try (left; apply IsBetterCombo_iff; simpl; lia); try right; reflexivity.
Qed.



Theorem BetterComboIsOneWayOnly :
  forall (cb1 cb2 : Combo), IsBetterCombo cb1 cb2 ->
  ~ IsBetterCombo cb2 cb1.
Proof.
  intros. unfold not. intros. destruct cb1; destruct cb2; 
  apply IsBetterCombo_iff in H; apply IsBetterCombo_iff in H0; 
  simpl in H; simpl in H0; try lia.
Qed.

Theorem CombosOfSameRankAreSame :
  forall (cb1 cb2 : Combo), 
  (~ IsBetterCombo cb1 cb2 /\ ~ IsBetterCombo cb2 cb1) <->
  EqCombo cb1 cb2.
Proof.
  intros. split.
  - intros. destruct H. rewrite IsBetterCombo_iff in H; rewrite IsBetterCombo_iff in H0;
  destruct cb1; destruct cb2;
  simpl in H; simpl in H0; try lia; try constructor.
  - intros. destruct cb1; destruct cb2;
  rewrite IsBetterCombo_iff; try rewrite IsBetterCombo_iff; simpl; try lia; try inversion H.
Qed.

Theorem ComboIsBetterThanOtherIfNotHighCard :
  forall (cb : Combo), ~ EqCombo cb HighCard ->
  exists (cb' : Combo), IsBetterCombo cb cb'.
Proof.
  intros. destruct cb. 
  - destruct H. constructor.
  - exists HighCard. apply IsBetterCombo_iff. simpl. lia.
  - exists HighCard. apply IsBetterCombo_iff. simpl. lia.
  - exists HighCard. apply IsBetterCombo_iff. simpl. lia.
  - exists HighCard. apply IsBetterCombo_iff. simpl. lia.
  - exists HighCard. apply IsBetterCombo_iff. simpl. lia.
  - exists HighCard. apply IsBetterCombo_iff. simpl. lia.
  - exists HighCard. apply IsBetterCombo_iff. simpl. lia.
  - exists HighCard. apply IsBetterCombo_iff. simpl. lia.
  - exists HighCard. apply IsBetterCombo_iff. simpl. lia.
Qed.


Theorem BetterComboIsTransitive :
  forall (cb1 cb2 cb3 : Combo),
  IsBetterCombo cb1 cb2 ->
  IsBetterCombo cb2 cb3 ->
  IsBetterCombo cb1 cb3.
Proof.
  intros. destruct cb1; destruct cb2; destruct cb3;
  apply IsBetterCombo_iff; apply IsBetterCombo_iff in H; apply IsBetterCombo_iff in H0;
  simpl; simpl in H; simpl in H0; lia.
Qed.

(* combos are one branch only, combos have only one or zeros combos 
directly above and directly below *)
Theorem MaxOneComboDirectlyAbove :
  forall (cb1 cb2 cb3 : Combo), 
  DirectlyAboveCombo cb1 cb3 ->
  DirectlyAboveCombo cb2 cb3 ->
  EqCombo cb1 cb2.
Proof.
  intros. destruct cb1; destruct cb2; destruct cb3; try constructor;
  try (inversion H; inversion H0;
  rewrite -> IsBetterCombo_iff in *; simpl in *; lia);
  try (inversion H; inversion H0; destruct H6; exists Pair;
  split;
  rewrite -> IsBetterCombo_iff in *; simpl in *; lia;
  rewrite -> IsBetterCombo_iff in *; simpl in *; lia).
  try (inversion H; inversion H0; destruct H2; exists Pair;
  split).
  inversion H; inversion H0; rewrite -> IsBetterCombo_iff in *; simpl in *.
  repeat (inversion H; inversion H0; rewrite -> IsBetterCombo_iff in *; simpl in *; lia).
Admitted.

Theorem FourContainsTriple :
  forall (h : Hand), ContainsCombo h Triple ->
  ContainsCombo h Pair.
Proof.
  intros. destruct h.
  - inversion H. inversion H0. inversion H2. destruct (EqCardValb x cd).
    * lia.
    * lia.
  - inversion H. inversion H0. inversion H2. destruct (EqCardValb x cd).
    * constructor. unfold IsPair.
Admitted.

(* si two pairs and nont full and five card then not triple *)
Theorem TwoPairsDontContainAlwaysTriple :
  exists (h : Hand), ContainsCombo h Triple ->
  ~ ContainsCombo h TwoPairs.
Proof.
Admitted.

(*five card *)
Theorem StraightDontContainPair :
  forall (h : Hand), ContainsCombo h Straight ->
  ~ ContainsCombo h Pair.
Proof.
Admitted.

(*five card *)
Theorem FlushContainsOneColor :
  forall (h : Hand), ContainsCombo h Flush ->
  ~ exists (c1 c2 : Color), HandContainsColor c1 h ->
  HandContainsColor c2 h -> DiffColor c1 c2.
Proof.
Admitted.

(* Highest combo*)

Theorem RoyalFlushHighestComboBeatsStraight :
  forall (h1 h2 : Hand),
  HighestCombo h1 RoyalFlush ->
  HighestCombo h2 Straight ->
  IsHigherRanked h1 h2.
Proof.
  intros.
  apply BetterCombo. exists RoyalFlush. exists Straight. intros. assumption. Qed.
  
Theorem AllHandContainsCombo :
  forall (h : Hand), exists (cb : Combo), ContainsCombo h cb.
Proof.
  intros. exists HighCard. constructor. Qed.

  (* iff highest combo *)
Theorem AllHandContainsHighestCombo :
  forall (h : Hand), exists (cb : Combo), HighestCombo h cb.
Proof.
Admitted.

  
Theorem RoyalFlushHighestComboBeatsAll :
  forall (h1 h2 : Hand) (cb : Combo),
  HighestCombo h1 RoyalFlush ->
  ~ HighestCombo h2 RoyalFlush ->
  IsHigherRanked h1 h2.
Proof.
Admitted.

(* IsHigherRanked *)
(*
comparaison deux cartes hautes
carte haute pair
triple pair

forall h1 h2, higher h1 h2 -> ~ higher h2 h1

high h1 h2 -> h2 h3 -> h1 h3

nothing less than worst

nothing better than best

carte haute ace dont beat pair

TieRank avec juste couleur qui diffère

well_defined means
pas 2 triples
pas 2 fulls
pas 2 royalFlushs

*)