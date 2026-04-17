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

Lemma IsDirectlyBelowHighCardPair : 
  DirectlyBelowCombo HighCard Pair.
Proof. Admitted.

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

Theorem RoyalFlushIsBetterThanEverthing :
  forall (cb : Combo),
  IsBetterCombo RoyalFlush cb \/ cb = RoyalFlush.
Proof. 
  intros. destruct cb; try (left; apply IsBetterCombo_iff; simpl; lia); try right; reflexivity.
Qed.

Theorem ComboIsNotBetterThanHimself :
  forall (cb : Combo), ~ IsBetterCombo cb cb.
Proof. Admitted.

Theorem BetterComboIsOneWayOnly :
  forall (cb1 cb2 : Combo), IsBetterCombo cb1 cb2 ->
  ~ IsBetterCombo cb2 cb1.
Proof. Admitted.

Theorem CombosOfSameRankAreSame :
  forall (cb1 cb2 : Combo), 
  (~ IsBetterCombo cb1 cb2 /\ ~ IsBetterCombo cb2 cb1) <->
  EqCombo cb1 cb2.
Proof. Admitted.

Theorem ComboIsBetterThanOtherIfNotHighCard :
  forall (cb : Combo), ~ EqCombo cb HighCard ->
  exists (cb' : Combo), IsBetterCombo cb cb'.
Proof. Admitted.

Theorem BetterComboIsTransitive :
  forall (cb1 cb2 cb3 : Combo),
  IsBetterCombo cb1 cb2 ->
  IsBetterCombo cb2 cb3 ->
  IsBetterCombo cb1 cb3.
Proof. Admitted.

(* combos are one branch only, combos have only one or zeros combos 
directly above and directly below *)
Theorem MaxOneComboDirectlyAbove :
  forall (cb1 cb2 cb3 : Combo), 
  DirectlyAboveCombo cb1 cb3 ->
  DirectlyAboveCombo cb2 cb3 ->
  EqCombo cb1 cb2.
Proof. Admitted.

Theorem MaxOneComboDirectlyBelow :
  forall (cb1 cb2 cb3 : Combo), 
  DirectlyBelowCombo cb1 cb3 ->
  DirectlyBelowCombo cb2 cb3 ->
  EqCombo cb1 cb2.
Proof. Admitted.

Theorem CombosAreSameOrRanked :
  forall (cb1 cb2 : Combo),
  (EqCombo cb1 cb2) 
  \/ (IsBetterCombo cb1 cb2) 
  \/ (IsBetterCombo cb2 cb1).
Proof. Admitted.

(* Contains Combo*)

Theorem TripleContainsPair :
  forall (h : Hand), ContainsCombo h Triple ->
  ContainsCombo h Pair.
Proof.
Admitted.

Theorem FourContainsTriple :
  forall (h : Hand), ContainsCombo h Triple ->
  ContainsCombo h Pair.
Proof.
Admitted.

Theorem TwoPairsDontContainAlwaysTriple :
  exists (h : Hand), ContainsCombo h Triple ->
  ~ ContainsCombo h TwoPairs.
Proof.
Admitted.

Theorem StraightDontContainPair :
  forall (h : Hand), ContainsCombo h Straight ->
  ~ ContainsCombo h Pair.
Proof.
Admitted.

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