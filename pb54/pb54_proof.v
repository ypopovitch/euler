Require Import Stdlib.Strings.String.
Require Import Stdlib.Strings.Ascii.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import euler.pb54.pb54.


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
Proof. Admitted.

Theorem RoyalFlushIsBetterThanEverthing :
  forall (cb : Combo), IsBetterCombo RoyalFlush cb.
Proof. Admitted.

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
  \/ (IsBetterCombo cd1 cb2) 
  \/ (IsBetterCombo cb2 cb1).
Proof. Admitted.

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