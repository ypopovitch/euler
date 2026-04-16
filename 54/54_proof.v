
(* Theorems *) 
 
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

Check IsBetterCombo_rank.
  
Theorem TripleIsNotBetterThanTwoPairs :
  ~ IsBetterCombo TwoPairs Triple.
Proof.
  intros H.
  apply IsBetterCombo_rank in H.
  simpl in H.
  lia.
Qed.

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
  intros. apply BetterCombo. exists RoyalFlush.
  pose proof (AllHandContainsHighestCombo h2).
  destruct H3. exists x. intros. assumption. Qed.